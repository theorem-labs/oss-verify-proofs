(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module names, addresses and numbers changed; 1179 of its 1302 lines of code are new or changed and 3112 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F11.v, with its module names changed; 217 of its 522 lines of code are new or changed and 997 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F11.v b6ff5fc222a0 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f11_fd4_evt_of_F / f11_014_evt_of_F re-derive F11.f11_fd4_evt / F11.f11_014_evt at ExecF.RNG_all;
   f11_fd4_evt_of_F_verbatim / f11_014_evt_of_F_verbatim check by constr_eq that their types are the source types
   (f11_014_evt after F11.v's Section hypothesis HING, the plain ingest contract, as Seg/F21F.v pins).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) forms of F11.v's three run lemmas:
     f11_loop_F   (F11.v:273) the record-sum loop 0x8206c -> 0x820a4, by induction on the turns left;
     f11_fd4_evt_F(F11.v:357) that loop plus the mod-128 test 0x820a4-0x820a8, 0x8206c -> 0x820ac;
     f11_014_evt_F(F11.v:442) 0x820ac -> 0x820f8: the two checked record bytes phi+36 / phi+37, the 16-bit compare
                   against the reply cell, and the reac_identity_ingest call at 0x820f4.
   Each is re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the
   same binders and premises in the same order and the footprint premises appended. The loop's regions are the
   whole record buffer [phi, phi+50) and the byte-exact shadow span of that buffer, both fixed before the
   induction; each turn's byte and shadow byte come out of them by ExecF.rng_sub and f11F_sh_rng.

   The ingest callee is the proved twin reac_identity_ingest_F_holds (lib/A/Prog/reac_identity_ingestF.v), so the
   plain contract hypothesis of F11.v's Section S (Hypothesis HING) is not needed here.

   f11_loop_F has NO _of_F corollary: its continuation premise is a run (an Exec.evt in F11.f11_loop, an ExecF.evtF
   in the twin), so it stands left of the arrow and RNG_all gives nothing; evt does not imply evtF. The corollary
   check for the loop is carried by f11_fd4_evt_of_F, which uses it. Reported to the lead.

   F11.v itself is unchanged apart from comment text (comment line 400 differs from the blob above); its seg_F11_* proofs still use the source lemmas. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcParseLib RcFrag RcIdentModel
  RcAsanLib RcLib RcReply RcReplyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_identity_ingest_c.
(* The ingest callee's own proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_identity_ingestF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F11.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
Import ListNotations.
(* Restore YK11's register reads (the names F11's statements are written over). *)
Import YK11.
Open Scope Z_scope.

Module F11LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module ING := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_ingestF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* RNG_all over a closed address range: both bounds are decided by computation. *)
Local Ltac rng_lit := apply rng_all; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.

(* The instrumented check of the byte y loads the shadow byte at (y >> 3) + ASAN_K; it lies in the byte-exact
   shadow span of a block [x, z] that contains y (Seg/F21F.v f21_sh_rng, the same text). *)
Lemma f11F_sh_rng : forall (RNG : footprint) x y z, 0 <= x <= y -> y <= z ->
  rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  rng RNG (Z.shiftr y 3 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* The same, in the x / 8 + ASAN_K shape the loads form after unsigned_lit. *)
Lemma f11F_sh_rng' : forall (RNG : footprint) x y z, 0 <= x <= y -> y <= z ->
  rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  rng RNG (y / 8 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* A byte-exact shadow span of a block that lies below APPMEM_END is inside the address space. *)
Lemma f11F_sh_all : forall x z, 0 <= x <= z -> z + 1 <= 2 ^ 64 ->
  rng RNG_all (shadow_addr x) (shadow_addr z - shadow_addr x + 1).
Proof.
  intros x z Hxz Hz. apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- the record-sum loop 0x8206c -> 0x820a4 under a footprint ---- *)
Lemma f11_loop_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a5' a6' a7' : word,
     evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3
         (Z_to_bv 64 (psum (skipn 34 bs) (Z.to_nat n0))) a5' a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820a4) fc None m (seg_rom rsegs))) ->
  rng RNG phi 50 ->
  rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
  forall (k i : nat) (a6' a7' : word), (i + k = Z.to_nat n0)%nat -> (0 < k)%nat ->
  evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34 + Z.of_nat i))
         (Z_to_bv 64 (n0 - Z.of_nat i)) a2 a3 (Z_to_bv 64 (psum (skipn 34 bs) i))
         (Z_to_bv 64 (phi + 34 + Z.of_nat i)) a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m phi n0 bs Q
    Hphi0 Hphi50 Hlen Hn0 HB HA Hjoin RBUF RSHA.
  induction k as [|k IH]; intros i a6' a7' Hik Hk; [lia|].
  (* the instrumented check of the byte at phi+34+i *)
  assert (Haddr1 : addressable m (phi + 34 + Z.of_nat i) 1).
  { replace (phi + 34 + Z.of_nat i) with (phi + (34 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (34 + Z.of_nat i) 1 HA); lia. }
  (* the two accesses of this turn, out of the two fixed regions *)
  assert (Rb : rng RNG (phi + 34 + Z.of_nat i) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rsh : rng RNG (Z.shiftr (phi + 34 + Z.of_nat i) 3 + ASAN_K) 1)
    by (apply (f11F_sh_rng RNG phi (phi + 34 + Z.of_nat i) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rsh' : rng RNG ((phi + 34 + Z.of_nat i) / 8 + ASAN_K) 1)
    by (apply (f11F_sh_rng' RNG phi (phi + 34 + Z.of_nat i) (phi + 49)); [lia | lia | exact RSHA]).
  destruct (sl_shadow1 m (phi + 34 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (34 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (34 + i)) with (34 + Z.of_nat i) in RDb by lia.
  replace (phi + (34 + Z.of_nat i)) with (phi + 34 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 34 bs) i) as PR.
  (* the join at 0x8207c (the check passed), with the slow path's scratch register a7 generalized *)
  assert (G4 : forall y7 : word,
    evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34 + Z.of_nat i))
       (Z_to_bv 64 (n0 - Z.of_nat i)) a2 a3 (Z_to_bv 64 (psum (skipn 34 bs) i))
       (Z_to_bv 64 (phi + 34 + Z.of_nat i)) (sxb sb) y7
       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x8207c) fc None m (seg_rom rsegs))).
  { intro y7.
    step. (* lbu a6,0(a5) *)
    step. (* addi a1,a1,-1 *)
    step. (* addi a0,a0,1 *)
    step. (* add a4,a4,a6 *)
    rewrite <- (f11_nth_skipn byte (Z_to_bv 8 0) 34 bs i).
    rewrite psum_S_zxb.
    step. (* addi a5,a5,1 *)
    step. (* bnez a1,8206c *)
    destruct k as [|k'].
    - (* last turn: a1 = 0, not taken; 0x82094 j 820a4 *)
      replace (n0 - Z.of_nat i + -1) with 0 by lia.
      rewrite bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* j 820a4 *)
      assert (E : (S i = Z.to_nat n0)%nat) by lia. rewrite <- E in Hjoin.
      apply Hjoin.
    - (* more turns: a1 = n0-(i+1) <> 0, taken back to 0x8206c *)
      replace (n0 - Z.of_nat i + -1) with (n0 - Z.of_nat (S i)) by lia.
      rewrite (rc_neq0_64 (n0 - Z.of_nat (S i))) by lia. cbn [negb]. cbv iota.
      replace (phi + 34 + Z.of_nat i + 1) with (phi + 34 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia. }
  (* 0x8206c-0x82078: the shadow byte of phi+34+i and the branch on it *)
  step. (* srli a6,a0,3 *)
  step. (* add a6,a6,s10 *)
  rewrite (unsigned_lit (phi + 34 + Z.of_nat i)) by lia.
  step. (* lb a6,0(a6) *)
  step. (* bnez a6,82098 *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* the shadow byte is 0: not taken, the byte is in an addressable range *)
    cbn [negb]. cbv iota. apply (G4 a7').
  - (* the shadow byte is not 0: the slow path 0x82098, whose compare sends the error call 0x82c94 away *)
    cbn [negb]. cbv iota.
    step. (* andi a7,a0,7 *)
    rewrite (unsigned_lit (phi + 34 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* bge a7,a6,82c94 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 34 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 34 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 34 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 8207c *)
    apply (G4 (Z_to_bv 64 ((phi + 34 + Z.of_nat i) mod 8))).
Qed.

(* F11.f11_loop's statement as a corollary: the twin at RNG_all, its CPS (continuation) premise mapped back by
   lib/Lib/ExecF_all.evt_evtF_all (evt -> evtF at RNG_all), and the two rng premises by rng_all (bounds from the
   lemma's own 0 <= phi and phi + 50 <= 2^64). *)
Lemma f11_loop_of_F : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a5' a6' a7' : word,
     F11LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3
         (Z_to_bv 64 (psum (skipn 34 bs) (Z.to_nat n0))) a5' a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820a4) fc None m (seg_rom rsegs))) ->
  forall (k i : nat) (a6' a7' : word), (i + k = Z.to_nat n0)%nat -> (0 < k)%nat ->
  F11LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34 + Z.of_nat i))
         (Z_to_bv 64 (n0 - Z.of_nat i)) a2 a3 (Z_to_bv 64 (psum (skipn 34 bs) i))
         (Z_to_bv 64 (phi + 34 + Z.of_nat i)) a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m phi n0 bs Q
    Hphi0 Hphi50 Hlen Hn0 HB HA HK k i a6' a7' Hik Hk.
  apply (evtF_evt rsegs RNG_all).
  apply (f11_loop_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
           Fr fc m phi n0 bs Q Hphi0 Hphi50 Hlen Hn0 HB HA
           (fun a0' a5'' a6'' a7'' => EFA.evt_evtF_all rsegs _ _ (HK a0' a5'' a6'' a7''))
           ltac:(apply rng_all; lia) ltac:(apply f11F_sh_all; lia) k i a6' a7' Hik Hk).
Qed.

(* The pin: f11_loop_of_F states F11.f11_loop's v1.9 text, term for term. *)
Example f11_loop_of_F_verbatim : True.
Proof.
  let a := type of F11.f11_loop in let b := type of f11_loop_of_F in constr_eq a b.
  exact I.
Qed.

(* ---- the loop plus the mod-128 test, 0x8206c -> 0x820ac, under a footprint ---- *)
Lemma f11_fd4_evt_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a6i a7i : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  psum (skipn 34 bs) (Z.to_nat n0) mod 128 = 0 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  rng RNG phi 50 ->
  rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
  evtF rsegs RNG
    (fun ms' => exists (a0' a4' a5' a6' a7' : word),
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3 a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 n0) a2 a3 (Z_to_bv 64 0)
             (Z_to_bv 64 (phi + 34)) a6i a7i
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a6i a7i Fr fc m phi n0 bs
    Hphi0 Hphi50 Hlen Hn0 Hsum HB HA RBUF RSHA.
  pose proof (psum_range (skipn 34 bs) (Z.to_nat n0)) as PR.
  (* 0x820a4 andi a0,a4,127 ; 0x820a8 bnez a0,82bf4 not taken: the record sum is 0 mod 128 *)
  match goal with
  | |- evtF _ _ ?P _ =>
    assert (Hjoin : forall a0' a5' a6' a7' : word,
      evtF rsegs RNG P
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3
             (Z_to_bv 64 (psum (skipn 34 bs) (Z.to_nat n0))) a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x820a4) fc None m (seg_rom rsegs)))
  end.
  { intros a0' a5' a6' a7'.
    step. (* andi a0,a4,127 *)
    step. (* bnez a0,82bf4 *)
    rewrite (rc_z127 (psum (skipn 34 bs) (Z.to_nat n0))) by lia.
    rewrite Hsum. cbn [Z.eqb negb]. cbv iota.
    apply evtF_done. do 5 eexists. reflexivity. }
  replace (Z_to_bv 64 (phi + 34)) with (Z_to_bv 64 (phi + 34 + Z.of_nat 0)) by (f_equal; cbn; lia).
  replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - Z.of_nat 0)) by (f_equal; cbn; lia).
  exact (f11_loop_F RNG ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
           Fr fc m phi n0 bs _ Hphi0 Hphi50 Hlen Hn0 HB HA Hjoin RBUF RSHA (Z.to_nat n0) 0%nat a6i a7i
           ltac:(lia) ltac:(lia)).
Qed.

(* F11.f11_fd4_evt's statement back from f11_fd4_evt_F at RNG_all: the record buffer's bounds are the lemma's own
   (0 <= phi, phi + 50 <= 2^64), and its shadow span lies below 2^64 (f11F_sh_all). *)
Lemma f11_fd4_evt_of_F : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
                                 a6i a7i : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  psum (skipn 34 bs) (Z.to_nat n0) mod 128 = 0 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  F11LE.evt rsegs
    (fun ms' => exists (a0' a4' a5' a6' a7' : word),
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3 a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 n0) a2 a3 (Z_to_bv 64 0)
             (Z_to_bv 64 (phi + 34)) a6i a7i
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a6i a7i Fr fc m phi n0 bs
    Hphi0 Hphi50 Hlen Hn0 Hsum HB HA.
  eapply evtF_evt, (f11_fd4_evt_F RNG_all); try eassumption.
  - apply rng_all; lia.
  - apply f11F_sh_all; lia.
Qed.

(* The pin: f11_fd4_evt_of_F states F11.f11_fd4_evt's v1.9 text, term for term. *)
Example f11_fd4_evt_of_F_verbatim : True.
Proof.
  let a := type of F11.f11_fd4_evt in let b := type of f11_fd4_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---- 0x820ac -> 0x820f8 under a footprint: the two checked record bytes, the 16-bit compare and the ingest
   call, through the callee's footprint contract (its owner's proof reac_identity_ingest_F_holds). ---- *)
Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

Lemma f11_014_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi fr A lo len : Z) (G idb pb : list byte),
    length G = 50%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 -> len = ir_s G - 13 -> 14 <= ir_s G <= 23 ->
    bytes_at rsegs m phi G -> addressable m phi 50 ->
    0 <= A < 2 ^ 64 -> q64 m (A + 256) (fr + 256) -> q64 m (A + 144) (fr + 2688) ->
    bytes_at rsegs m (fr + 256) (reply_addr G) ->
    0 < fr -> fr + FRAME_BYTES <= 2 ^ 64 -> (fr + 2688) mod 2 = 0 ->
    rw_cells rsegs m (fr + 2688) [CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m (phi + 38) pb ->
    (phi + 38 + len <= fr + 2688 \/ fr + 2688 + 38 <= phi + 38) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (fr + 2688 + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= fr + 2688) ->
    (phi + 38 + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= phi + 38) ->
    asan_cells m -> shadow_rw m ->
    addressable m (fr + 2688) 38 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       Frame.outside (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) x) ->
    rng RNG phi 50 ->
    rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
    rng RNG (A + 256) 8 ->
    rng RNG (A + 144) 8 ->
    rng RNG (fr + 256) 2 ->
    rng RNG (bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME) REAC_IDENTITY_INGEST_FRAME ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG (fr + 2688) 38 ->
    rng RNG ((fr + 2688) / 8 + ASAN_K) ((fr + 2688 + 37) / 8 - (fr + 2688) / 8 + 1) ->
    rng RNG (phi + 38) len ->
    rng RNG ((phi + 38) / 8 + ASAN_K) ((phi + 38 + len - 1) / 8 - (phi + 38) / 8 + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               a4i a5i a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i Fr fc m
    phi fr A lo len G idb pb HG Hphi0 Hphi50 Hlen Hs HB HA HAr Hq256 Hq144 Hra Hfr0 Hfrub Hid2 Hidrw Hpbl Hpb
    Hdj Hstk Hlo Hidw Hpw HAC HSW HidA HOUT
    RBUF RSHA R256 R144 RRA RFR RGOT RCK RID RIS RP RPS.
  pose proof (cp_v_range' G 36) as R36. pose proof (cp_v_range' G 37) as R37.
  assert (Hlen0 : 1 <= len <= 10) by lia.
  (* the two checked bytes and their shadow bytes, out of the record buffer's two regions *)
  assert (Rb36 : rng RNG (phi + 36) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rb37 : rng RNG (phi + 37) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rs36 : rng RNG ((phi + 36) / 8 + ASAN_K) 1)
    by (apply (f11F_sh_rng' RNG phi (phi + 36) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs37 : rng RNG ((phi + 37) / 8 + ASAN_K) 1)
    by (apply (f11F_sh_rng' RNG phi (phi + 37) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs36' : rng RNG (Z.shiftr (phi + 36) 3 + ASAN_K) 1)
    by (apply (f11F_sh_rng RNG phi (phi + 36) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rs37' : rng RNG (Z.shiftr (phi + 37) 3 + ASAN_K) 1)
    by (apply (f11F_sh_rng RNG phi (phi + 37) (phi + 49)); [lia | lia | exact RSHA]).
  (* the two instrumented checks: the bytes phi+36 and phi+37 lie in the addressable range [phi, phi+50) *)
  assert (Ha36 : addressable m (phi + 36) 1)
    by (apply (addressable_sub m phi 50 36 1 HA); lia).
  assert (Ha37 : addressable m (phi + 37) 1)
    by (apply (addressable_sub m phi 50 37 1 HA); lia).
  destruct (sl_shadow1 m (phi + 36) Ha36) as (sb1 & RD1 & OK1 & IS1).
  destruct (sl_shadow1 m (phi + 37) Ha37) as (sb2 & RD2 & OK2 & IS2).
  pose proof (rd_byte rsegs m phi G 36 HB ltac:(lia)) as RD36.
  pose proof (rd_byte rsegs m phi G 37 HB ltac:(lia)) as RD37.
  change (Z.of_nat 36) with 36 in RD36. change (Z.of_nat 37) with 37 in RD37.
  pose proof (f11_rd8 m (A + 256) _ Hq256 ltac:(apply length_le8)) as RD256.
  pose proof (f11_rd8 m (A + 144) _ Hq144 ltac:(apply length_le8)) as RD144.
  (* The reply cell in `le2` form, so the `lhu` at 0x820e8 does not make load_post's fold_lit_load vm_compute
     a symbolic byte list (the hang of the cons form [cp_b G 37; cp_b G 36]). *)
  assert (Hra2 : bytes_at rsegs m (fr + 256) (le2 (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)))).
  { unfold reply_addr in Hra. rewrite <- (rc_le2_pair (cp_b G 37) (cp_b G 36)) in Hra.
    change (bv_unsigned (cp_b G 36)) with (cp_v G 36) in Hra.
    change (bv_unsigned (cp_b G 37)) with (cp_v G 37) in Hra. exact Hra. }
  pose proof (f11_rd2 m (fr + 256) _ Hra2 ltac:(apply length_le2)) as RDa.
  (* the ingest call at 0x820f4, from the join at 0x820e0 *)
  assert (J48 : forall y6 : word,
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 37))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (zxb (nth 36 G (Z_to_bv 8 0))) (sxb sb2) y6 a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820e0) fc None m (seg_rom rsegs))).
  { intro y6.
    step. (* lbu a0,0(a0) : the byte phi+37 *)
    step. (* slli a4,a4,8 *)
    step. (* or a0,a4,a0 *)
    rewrite (rc_pack2 (nth 37 G (Z_to_bv 8 0)) (nth 36 G (Z_to_bv 8 0))).
    step. (* bne a0,a1,82bf4 : not taken *)
    change (bv_unsigned (nth 36 G (Z_to_bv 8 0))) with (cp_v G 36).
    change (bv_unsigned (nth 37 G (Z_to_bv 8 0))) with (cp_v G 37).
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    step. (* ld a0,144(s1) : the identity record fr+2688 *)
    step. (* jal reac_identity_ingest *)
    pose proof ING.reac_identity_ingest_F_holds as HI.
    unfold reac_identity_ingest_contract_F, REAC_IDENTITY_INGEST in HI.
    eapply evtF_cut.
    { eapply (HI RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lo (fr + 2688)
                 (cp_v G 36 * 256 + cp_v G 37) (phi + 38) len idb pb).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - intros _. split; [exact Hid2 | exact Hidrw].
      - exact Hpbl.
      - intros _ _. exact Hpb.
      - intros _ _ _. lia.
      - exact Hstk.
      - unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _ _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - exact HAC.
      - exact HSW.
      - intros _. exact HidA.
      - intros _ _. apply (addressable_sub m phi 50 38 len HA); lia.
      - exact HOUT.
      - exact RFR.
      - exact RGOT.
      - exact RCK.
      - intros _. split; [exact RID | exact RIS].
      - intros _ _. split; [exact RP | exact RPS]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI & ST & _ & HRW).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 532728)) with (Z_to_bv 64 532728)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (Href : ingest_refused (fr + 2688) (phi + 38) len = false).
    { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq (fr + 2688) 0) ltac:(lia)).
      rewrite (proj2 (Z.eqb_neq (phi + 38) 0) ltac:(lia)). rewrite andb_false_r. reflexivity. }
    unfold ingest_ret. rewrite Href.
    apply evtF_done.
    exists (Z_to_bv 64 532728), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    exact (HRW Href). }
  (* the join at 0x820c8: the check of phi+36 passed (its slow path 0x829b4 writes a5) *)
  assert (J30 : forall y5 : word,
    evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 36))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (sxb sb1) y5 a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820c8) fc None m (seg_rom rsegs))).
  { intro y5.
    step. (* addi a0,s6,19 : phi+37 *)
    step. (* srli a4,a0,3 *)
    rewrite (unsigned_lit (phi + 37)) by lia.
    step. (* add a4,a4,s10 *)
    step. (* lb a5,0(a4) : the shadow byte of phi+37 *)
    step. (* lbu a4,18(s6) : the byte phi+36 *)
    step. (* bnez a5,829c0 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb2)) by (pose proof (rc_byte_signed sb2); lia).
    destruct (Z.eqb_spec (bv_signed sb2) 0) as [Z2|Z2].
    - cbn [negb]. cbv iota. apply (J48 a6i).
    - cbn [negb]. cbv iota.
      step. (* andi a6,a0,7 *)
      rewrite (unsigned_lit (phi + 37)) by lia. rewrite rc_land7.
      step. (* bge a6,a5,82ccc *)
      unfold sxb. rewrite (rc_lts_signed ((phi + 37) mod 8) (bv_signed sb2))
        by (pose proof (rc_byte_signed sb2); pose proof (Z.mod_pos_bound (phi + 37) 8 ltac:(lia)); lia).
      replace ((phi + 37) mod 8 <? bv_signed sb2) with true
        by (symmetry; apply Z.ltb_lt; destruct OK2 as [H|H]; lia).
      cbn [negb]. cbv iota.
      step. (* j 820e0 *)
      apply (J48 (Z_to_bv 64 ((phi + 37) mod 8))). }
  (* 0x820ac-0x820c4: phi+36, its shadow byte, the u16 at pa = fr+256 and the branch *)
  step. (* addi a0,s6,18 : phi+36 *)
  step. (* srli a1,a0,3 *)
  rewrite (unsigned_lit (phi + 36)) by lia.
  step. (* add a1,a1,s10 *)
  step. (* lb a4,0(a1) : the shadow byte of phi+36 *)
  step. (* ld a1,256(s1) : pa = fr+256 *)
  step. (* lhu a1,0(a1) : the reply address (le2 form; load_post's zext_extract_le2 leaves zx16) *)
  rewrite (f11_zx16 (cp_v G 36 * 256 + cp_v G 37)) by (change (2 ^ 16) with 65536; lia).
  step. (* bnez a4,829b4 *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb1)) by (pose proof (rc_byte_signed sb1); lia).
  destruct (Z.eqb_spec (bv_signed sb1) 0) as [Z1|Z1].
  - cbn [negb]. cbv iota. apply (J30 a5i).
  - cbn [negb]. cbv iota.
    step. (* andi a5,a0,7 *)
    rewrite (unsigned_lit (phi + 36)) by lia. rewrite rc_land7.
    step. (* bge a5,a4,82cc8 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 36) mod 8) (bv_signed sb1))
      by (pose proof (rc_byte_signed sb1); pose proof (Z.mod_pos_bound (phi + 36) 8 ltac:(lia)); lia).
    replace ((phi + 36) mod 8 <? bv_signed sb1) with true
      by (symmetry; apply Z.ltb_lt; destruct OK1 as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 820c8 *)
    apply (J30 (Z_to_bv 64 ((phi + 36) mod 8))).
Qed.

(* F11.f11_014_evt's statement (after its Section hypothesis, the plain ingest contract) back from f11_014_evt_F
   at RNG_all: every region's bounds come from the lemma's own premises (the record buffer and its shadow span;
   the two spills and the reply cell by their q64 / bytes_at bounds; the callee frame by stk and sp's range; the
   identity record by fr + FRAME_BYTES <= 2^64; the ingest source by the bytes_at of pb), and the two runtime
   cells are literals. *)
Lemma f11_014_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi fr A lo len : Z) (G idb pb : list byte),
    length G = 50%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 -> len = ir_s G - 13 -> 14 <= ir_s G <= 23 ->
    bytes_at rsegs m phi G -> addressable m phi 50 ->
    0 <= A < 2 ^ 64 -> q64 m (A + 256) (fr + 256) -> q64 m (A + 144) (fr + 2688) ->
    bytes_at rsegs m (fr + 256) (reply_addr G) ->
    0 < fr -> fr + FRAME_BYTES <= 2 ^ 64 -> (fr + 2688) mod 2 = 0 ->
    rw_cells rsegs m (fr + 2688) [CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m (phi + 38) pb ->
    (phi + 38 + len <= fr + 2688 \/ fr + 2688 + 38 <= phi + 38) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (fr + 2688 + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= fr + 2688) ->
    (phi + 38 + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= phi + 38) ->
    asan_cells m -> shadow_rw m ->
    addressable m (fr + 2688) 38 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       Frame.outside (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) x) ->
    F11LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               a4i a5i a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv.
  intros ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i Fr fc m
    phi fr A lo len G idb pb HG Hphi0 Hphi50 Hlen Hs HB HA HAr Hq256 Hq144 Hra Hfr0 Hfrub Hid2 Hidrw Hpbl Hpb
    Hdj Hstk Hlo Hidw Hpw HAC HSW HidA HOUT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof Hstk as (HL0 & _ & _).
  pose proof Hq256 as (B256 & L256 & _). rewrite length_le8 in L256.
  pose proof Hq144 as (B144 & L144 & _). rewrite length_le8 in L144.
  pose proof Hra as (BRA & LRA & _).
  pose proof Hpb as (BP & LP & _). rewrite Hpbl in LP.
  assert (HK : REAC_IDENTITY_INGEST_FRAME = 32) by reflexivity.
  eapply evtF_evt, (f11_014_evt_F RNG_all); try eassumption.
  - apply rng_all; lia.
  - apply f11F_sh_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - rng_lit.
  - rng_lit.
  - apply rng_all; lia.
  - apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - apply rng_all; lia.
  - apply rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.

End RunF.

(* The pin: f11_014_evt_of_F states F11.f11_014_evt's v1.9 text after F11.v's first premise, the plain ingest
   contract (F11.v Section S, Hypothesis HING), term for term. The corollary needs no premise in its place: the
   callee is proved (reac_identity_ingest_F_holds). *)
Example f11_014_evt_of_F_verbatim : True.
Proof.
  lazymatch type of F11.f11_014_evt with ?P -> ?A =>
    constr_eq P reac_identity_ingest_contract;
    let B := type of f11_014_evt_of_F in constr_eq A B
  end.
  exact I.
Qed.
