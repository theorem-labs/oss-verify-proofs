(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F5.v, with its module paths, module names and addresses changed; 444 of its 541 lines of code are new or changed and 1679 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F6.v 5a9c598d249e (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f6_e28_evt_of_F / f6_ebc_evt_of_F re-derive F6.f6_e28_evt / F6.f6_ebc_evt at ExecF.RNG_all;
   f6_e28_evt_of_F_verbatim / f6_ebc_evt_of_F_verbatim check by constr_eq that their types are the source types
   (f6_ebc_evt after F6.v's Section hypothesis HPARSE, the plain parse contract, as Seg/F21F.v pins).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) forms of F6.v's three run lemmas:
     f6_loop_F    (F6.v:398)  the 32-byte sum loop 0x81ec0 -> 0x81ef8, by induction on the turns left;
     f6_e28_evt_F (F6.v:483)  that loop, the two instrumented byte checks of phi+16 / phi+17, the abort compare at
                  0x81f40 (not taken) and the store [s1+280], 0x81ec0 -> 0x81f54;
     f6_ebc_evt_F (F6.v:1418) 0x81f54 -> 0x81f64: the three argument moves and the reac_ctrl_parse call at
                  0x81f60, run on MemNorm.normalize m as in F6.v and lifted by MemNormF.evtF_normalize_ro (the
                  evtF form of MemNorm.evt_normalize, which keeps the footprint RNG).
   Each is re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the
   same binders and premises in the same order and the footprint premises appended. The loop's regions are the
   whole record buffer [phi, phi+50) and the byte-exact shadow span of that buffer, both fixed before the
   induction; each turn's byte and shadow byte come out of them by ExecF.rng_sub and f6F_sh_rng.

   The parse callee is reac_ctrl_parse_contract_F (lib/A/Prog/reac_ctrl_parse_c.v), taken as the first premise of
   f6_ebc_evt_F in the place of F6.v's Section hypothesis HPARSE; its footprint premises are the contract_F ones at
   this call's instance (o = 0, so the two o-premises are vacuous and are not asked for).

   f6_loop_F has NO _of_F corollary: its continuation premise is a run (an Exec.evt in F6.f6_loop, an ExecF.evtF in
   the twin), so it stands left of the arrow and RNG_all gives nothing; evt does not imply evtF. The corollary
   check for the loop is carried by f6_e28_evt_of_F, which uses it. Reported to the lead.

   F6.v itself is unchanged apart from comment text; its seg_F6_* proofs still use the source lemmas. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcModel RcLib RcParse RcAsanLib RcLay
  RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c memcmp_c bcmp_wrap_c
  asan_stack_malloc_c RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
(* The evtF form of MemNorm.evt_normalize (a Theorem Labs lane's rule for a run already lifted through evt_normalize). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F6.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow lib.Lib Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
Import ListNotations.
(* Restore YK11's register reads (the names F6's statements are written over). *)
Import YK11.
Open Scope Z_scope.

Module F6LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* RNG_all over a closed address range: both bounds are decided by computation. *)
Local Ltac rng_lit := apply rng_all; apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.

(* The instrumented check of the byte y loads the shadow byte at (y >> 3) + ASAN_K; it lies in the byte-exact
   shadow span of a block [x, z] that contains y (Seg/F21F.v f21_sh_rng, the same text). *)
Lemma f6F_sh_rng : forall (RNG : footprint) x y z, 0 <= x <= y -> y <= z ->
  rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  rng RNG (Z.shiftr y 3 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* The same, in the y / 8 + ASAN_K shape the loads form after unsigned_lit. *)
Lemma f6F_sh_rng' : forall (RNG : footprint) x y z, 0 <= x <= y -> y <= z ->
  rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  rng RNG (y / 8 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* The 8-aligned shadow word cover of a block below 2^64 lies in the address space (sh_lo / sh_len of
   lib/A/Prog/reac_ctrl_parse_c.v: (p / 8 + ASAN_K) / 8 * 8 and the word that covers its last byte). *)
Lemma f6F_sh_cov_all : forall p n, 0 <= p -> p + n <= 2 ^ 64 -> rng RNG_all (sh_lo p) (sh_len p n).
Proof.
  intros p n Hp Hpn.
  apply rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* A byte-exact shadow span of a block below 2^64 lies in the address space. *)
Lemma f6F_sh_all : forall x z, 0 <= x <= z -> z + 1 <= 2 ^ 64 ->
  rng RNG_all (shadow_addr x) (shadow_addr z - shadow_addr x + 1).
Proof.
  intros x z Hxz Hz. apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---------------- the block-sum loop 0x81ec0 -> 0x81f54 under a footprint ---------------- *)

Lemma f6_loop_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a2' a3' a4' a5' : word,
     evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0'
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2' a3' a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ef8) fc None m (seg_rom rsegs))) ->
  rng RNG phi 50 ->
  rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
  forall n i (a4' a5' : word), (i + n = 32)%nat -> (0 < n)%nat ->
  evtF rsegs RNG Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (psum (skipn 18 bs) i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (32 - Z.of_nat i)) a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA Hjoin RBUF RSHA.
  induction n as [|n IH]; intros i a4' a5' Hin Hn; [lia|].
  (* shadow check of the byte at phi+18+i *)
  assert (Haddr1 : addressable m (phi + 18 + Z.of_nat i) 1).
  { replace (phi + 18 + Z.of_nat i) with (phi + (18 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (18 + Z.of_nat i) 1 HA); lia. }
  (* the two accesses of this turn, out of the two fixed regions *)
  assert (Rb : rng RNG (phi + 18 + Z.of_nat i) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
  assert (Rsh : rng RNG (Z.shiftr (phi + 18 + Z.of_nat i) 3 + ASAN_K) 1)
    by (apply (f6F_sh_rng RNG phi (phi + 18 + Z.of_nat i) (phi + 49)); [lia | lia | exact RSHA]).
  assert (Rsh' : rng RNG ((phi + 18 + Z.of_nat i) / 8 + ASAN_K) 1)
    by (apply (f6F_sh_rng' RNG phi (phi + 18 + Z.of_nat i) (phi + 49)); [lia | lia | exact RSHA]).
  destruct (sl_shadow1 m (phi + 18 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (18 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (18 + i)) with (18 + Z.of_nat i) in RDb by lia.
  replace (phi + (18 + Z.of_nat i)) with (phi + 18 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 18 bs) i) as PR. change (Z.of_nat 32) with 32 in PR.
  (* the join at 0x81ed0 (shadow passed), with the slow-path register a5 generalized *)
  assert (G38 : forall y5 : word,
    evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 18 + Z.of_nat i))
       (Z_to_bv 64 (psum (skipn 18 bs) i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
       (Z_to_bv 64 (32 - Z.of_nat i)) (sxb sb) y5 a6 a7
       s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x81ed0) fc None m (seg_rom rsegs))).
  { intro y5.
    step. (* lbu a4,0(a2) *)
    step. (* addi a3,a3,-1 *)
    step. (* addi a0,a0,1 *)
    step. (* add a1,a1,a4 *)
    rewrite <- (f6_nth_skipn byte (Z_to_bv 8 0) 18 bs i).
    rewrite psum_S_zxb.
    step. (* addi a2,a2,1 *)
    step. (* bnez a3,81ec0 *)
    destruct n as [|n'].
    - (* last turn: a3 = 0, not taken; fall to 0x81ee8 -> 0x81ef8 *)
      replace i with 31%nat in * by lia.
      replace (32 - Z.of_nat 31) with 1 by lia. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* j 81ef8 *)
      apply Hjoin.
    - (* more turns: a3 = 32-(i+1) <> 0, taken back to 0x81ec0 at i+1 *)
      replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
      rewrite (rc_neq0_64 (32 - Z.of_nat (S i))) by lia. cbn [negb]. cbv iota.
      replace (phi + 18 + Z.of_nat i + 1) with (phi + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia. }
  (* run the shadow check 0x81ec0-0x81ecc *)
  step. (* srli a4,a0,3 *)
  step. (* add a4,a4,s10 *)
  rewrite (unsigned_lit (phi + 18 + Z.of_nat i)) by lia.
  step. (* lb a4,0(a4) : a4 = sxb sb (RDsb) *)
  step. (* bnez a4,81eec *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* shadow 0: not taken, fall to 0x81ed0 *)
    cbn [negb]. cbv iota. apply (G38 a5').
  - (* shadow <> 0: slow path 0x81eec *)
    cbn [negb]. cbv iota.
    step. (* andi a5,a0,7 *)
    rewrite (unsigned_lit (phi + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* bge a5,a4,82c90 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 18 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 18 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 81ed0 *)
    apply (G38 (Z_to_bv 64 ((phi + 18 + Z.of_nat i) mod 8))).
Qed.

(* F6.f6_loop's statement as a corollary: the twin at RNG_all, its CPS (continuation) premise mapped back by
   lib/Lib/ExecF_all.evt_evtF_all (evt -> evtF at RNG_all), and the two rng premises by rng_all (bounds from the
   lemma's own 0 <= phi and phi + 50 <= 2^64). *)
Lemma f6_loop_of_F : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a2' a3' a4' a5' : word,
     F6LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0'
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2' a3' a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ef8) fc None m (seg_rom rsegs))) ->
  forall n i (a4' a5' : word), (i + n = 32)%nat -> (0 < n)%nat ->
  F6LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (psum (skipn 18 bs) i)) (Z_to_bv 64 (phi + 18 + Z.of_nat i))
         (Z_to_bv 64 (32 - Z.of_nat i)) a4' a5' a6 a7
         s2 s3 s4 s5 s6 s7 s8v s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6 Fr fc m phi bs Q
    Hphi0 Hphi50 Hlen HB HA HK n i a4' a5' Hin Hn.
  apply (evtF_evt rsegs RNG_all).
  apply (f6_loop_F RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s11 t3 t4 t5 t6
           Fr fc m phi bs Q Hphi0 Hphi50 Hlen HB HA
           (fun a0' a2' a3' a4'' a5'' => EFA.evt_evtF_all rsegs _ _ (HK a0' a2' a3' a4'' a5''))
           ltac:(apply rng_all; lia) ltac:(apply f6F_sh_all; lia) n i a4' a5' Hin Hn).
Qed.

(* The pin: f6_loop_of_F states F6.f6_loop's v1.9 text, term for term. *)
Example f6_loop_of_F_verbatim : True.
Proof.
  let a := type of F6.f6_loop in let b := type of f6_loop_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------- 0x81ec0 -> 0x81f54 under a footprint ---------------- *)

Lemma f6_e28_evt_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A tlen v8 e240 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 288 <= 2 ^ 64 -> stk rsegs m (A + 240) (A + 288) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 240) e240 -> e240 = (if v8 =? 0 then 0 else 1) ->
    rng RNG phi 50 ->
    rng RNG (shadow_addr phi) (shadow_addr (phi + 49) - shadow_addr phi + 1) ->
    rng RNG (A + 240) 8 ->
    rng RNG (A + 280) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6 a7
                       (Z_to_bv 64 tlen) s3 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1)) s5 s6
                       (Z_to_bv 64 phi) (Z_to_bv 64 v8) (Z_to_bv 64 (f6_s9 bs)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f54) fc None
                  (write_to_mem m (wa (A + 280)) (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 32) a4i a5i a6 a7
               (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 Fr fc m phi A tlen v8 e240 bs
    Hphi0 Hphi50 Hlen HB HA HA0 HA288 Hstk Hv8 Hq240 He240 RBUF RSHA R240 R280.
  match goal with |- evtF _ _ ?Q _ => set (QE := Q) end.
  (* the two byte-check / abort / store tail 0x81ef8 -> 0x81f54, as the loop join *)
  assert (Htail : forall a0' a2' a3' a4' a5' : word,
    evtF rsegs RNG QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0'
       (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2' a3' a4' a5' a6 a7
       (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x81ef8) fc None m (seg_rom rsegs))).
  { intros a0' a2' a3' a4' a5'.
    assert (Ha16 : addressable m (phi + 16) 1)
      by (apply (addressable_sub m phi 50 16 1 HA); lia).
    assert (Rb16 : rng RNG (phi + 16) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
    assert (Rs16 : rng RNG ((phi + 16) / 8 + ASAN_K) 1)
      by (apply (f6F_sh_rng' RNG phi (phi + 16) (phi + 49)); [lia | lia | exact RSHA]).
    assert (Rs16' : rng RNG (Z.shiftr (phi + 16) 3 + ASAN_K) 1)
      by (apply (f6F_sh_rng RNG phi (phi + 16) (phi + 49)); [lia | lia | exact RSHA]).
    destruct (sl_shadow1 m (phi + 16) Ha16) as (sb16 & RD16 & OK16 & IS16).
    pose proof (rd_byte rsegs m phi bs 16 HB ltac:(lia)) as RDb16. change (Z.of_nat 16) with 16 in RDb16.
    assert (Ha17 : addressable m (phi + 17) 1)
      by (apply (addressable_sub m phi 50 17 1 HA); lia).
    assert (Rb17 : rng RNG (phi + 17) 1) by (eapply rng_sub; [exact RBUF | lia | lia]).
    assert (Rs17 : rng RNG ((phi + 17) / 8 + ASAN_K) 1)
      by (apply (f6F_sh_rng' RNG phi (phi + 17) (phi + 49)); [lia | lia | exact RSHA]).
    assert (Rs17' : rng RNG (Z.shiftr (phi + 17) 3 + ASAN_K) 1)
      by (apply (f6F_sh_rng RNG phi (phi + 17) (phi + 49)); [lia | lia | exact RSHA]).
    destruct (sl_shadow1 m (phi + 17) Ha17) as (sb17 & RD17 & OK17 & IS17).
    pose proof (rd_byte rsegs m phi bs 17 HB ltac:(lia)) as RDb17. change (Z.of_nat 17) with 17 in RDb17.
    pose proof (bytes_at_ov_read rsegs m (A + 240) (le8 (Z_to_bv 64 e240)) 0 8 Hq240 ltac:(rewrite length_le8; lia)) as RD240.
    cbn [Z.of_nat] in RD240. rewrite Z.add_0_r, skipn_O, firstn_all2 in RD240 by (rewrite length_le8; lia).
    assert (HS280 : store_ok rsegs m (wa (A + 280)) 8 = true).
    { apply (f6_store_ok m m (A + 280) 8); [|apply wmono_refl|lia|lia].
      intros kk Hk. destruct Hstk as (_ & _ & Hs). destruct (Hs (A + 280 + kk) ltac:(lia)) as [Hw _]. exact Hw. }
    pose proof (psum_range (skipn 18 bs) 32) as PRsum. change (Z.of_nat 32) with 32 in PRsum.
    (* the join at 0x81f38 (after both byte checks), dead a0/a2/a3/a4/a5 generalized, s9 the model flag *)
    assert (GA0 : forall a0v a2v a3v a4v a5v s9v : word, s9v = Z_to_bv 64 (f6_s9 bs) ->
      evtF rsegs RNG QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0v
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) a2v a3v a4v a5v a6 a7
         (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9v (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81f38) fc None m (seg_rom rsegs))).
    { intros a0v a2v a3v a4v a5v s9v Hs9v. subst s9v.
      step. (* snez a0,s8 *)
      rewrite f6_snez, (unsigned_lit v8) by lia.
      step. (* ld a2,240(s1) *)
      step. (* bne a0,a2 : not taken (e240 = (v8<>0)) *)
      rewrite He240, bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* zext.b a0,a1 *)
      rewrite (unsigned_lit (psum (skipn 18 bs) 32)) by lia. rewrite f6_land255.
      step. (* seqz a1,a0 *)
      rewrite f6_seqz, (unsigned_lit (psum (skipn 18 bs) 32 mod 256))
        by (pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)); lia).
      step. (* sd a1,280(s1) *)
      step. (* snez s4,a0 *)
      rewrite f6_snez, (unsigned_lit (psum (skipn 18 bs) 32 mod 256))
        by (pose proof (Z.mod_pos_bound (psum (skipn 18 bs) 32) 256 ltac:(lia)); lia).
      unfold QE. apply evtF_done. do 6 eexists. reflexivity. }
    (* the join at 0x81f0c (byte16 shadow passed), dead a3 generalized *)
    assert (G74 : forall a3v : word,
      evtF rsegs RNG QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 16))
         (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb16) a3v a4' a5' a6 a7
         (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x81f0c) fc None m (seg_rom rsegs))).
    { intro a3v.
      step. (* lbu a0,0(a0) : byte16 *)
      step. (* beqz a0,81f1c *)
      unfold zxb. rewrite (rc_eqb0_signed (bv_unsigned (nth 16 bs (Z_to_bv 8 0))))
        by (pose proof (byte_range (nth 16 bs (Z_to_bv 8 0))); lia).
      destruct (Z.eqb_spec (bv_unsigned (nth 16 bs (Z_to_bv 8 0))) 0) as [B16|B16].
      - (* byte16 = 0: beqz taken to 0x81f1c, check byte17, s9 = seqz byte17 *)
        cbv iota.
        step. step. step. rewrite (unsigned_lit (phi + 17)) by lia. step. (* addi;srli;add;lb a2 (phi+17) *)
        step. (* bnez a2,82ab0 *)
        unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb17)) by (pose proof (rc_byte_signed sb17); lia).
        assert (G98 : forall a3w : word,
          evtF rsegs RNG QE (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 17))
             (Z_to_bv 64 (psum (skipn 18 bs) 32)) (sxb sb17) a3w a4' a5' a6 a7
             (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x81f30) fc None m (seg_rom rsegs))).
        { intro a3w.
          step. (* lbu a0,0(a0) : byte17 *)
          step. (* seqz s9,a0 *)
          rewrite f6_seqz. apply GA0.
          unfold f6_s9. rewrite B16, Z.eqb_refl. rewrite ?f6_zxb_u.
          rewrite ?(unsigned_lit (bv_unsigned (nth 17 bs (Z_to_bv 8 0))))
            by (pose proof (byte_range (nth 17 bs (Z_to_bv 8 0))); lia).
          reflexivity. }
        destruct (Z.eqb_spec (bv_signed sb17) 0) as [Z17|Z17].
        + cbn [negb]. cbv iota. apply (G98 a3v).
        + cbn [negb]. cbv iota.
          step. (* andi a3,a0,7 *)
          rewrite (unsigned_lit (phi + 17)) by lia. rewrite rc_land7.
          step. (* bge a3,a2,82d2c *)
          unfold sxb. rewrite (rc_lts_signed ((phi + 17) mod 8) (bv_signed sb17))
            by (pose proof (rc_byte_signed sb17); pose proof (Z.mod_pos_bound (phi + 17) 8 ltac:(lia)); lia).
          replace ((phi + 17) mod 8 <? bv_signed sb17) with true
            by (symmetry; apply Z.ltb_lt; destruct OK17 as [H|H]; lia).
          cbn [negb]. cbv iota. step. (* j 81f30 *)
          apply (G98 (Z_to_bv 64 ((phi + 17) mod 8))).
      - (* byte16 <> 0: beqz not taken, 0x81f14 li s9,0 ; j 81f38 *)
        cbv iota.
        step. (* li s9,0 *)
        step. (* j 81f38 *)
        apply GA0. unfold f6_s9. rewrite (proj2 (Z.eqb_neq _ 0) B16). reflexivity. }
    (* run 0x81ef8-0x81f08: compute phi+16 and its shadow check *)
    step. step. step. rewrite (unsigned_lit (phi + 16)) by lia. step. (* addi;srli;add;lb a2 (phi+16) *)
    step. (* bnez a2,82a38 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb16)) by (pose proof (rc_byte_signed sb16); lia).
    destruct (Z.eqb_spec (bv_signed sb16) 0) as [Z16|Z16].
    - cbn [negb]. cbv iota. apply (G74 a3').
    - cbn [negb]. cbv iota.
      step. (* andi a3,a0,7 *)
      rewrite (unsigned_lit (phi + 16)) by lia. rewrite rc_land7.
      step. (* bge a3,a2,82cfc *)
      unfold sxb. rewrite (rc_lts_signed ((phi + 16) mod 8) (bv_signed sb16))
        by (pose proof (rc_byte_signed sb16); pose proof (Z.mod_pos_bound (phi + 16) 8 ltac:(lia)); lia).
      replace ((phi + 16) mod 8 <? bv_signed sb16) with true
        by (symmetry; apply Z.ltb_lt; destruct OK16 as [H|H]; lia).
      cbn [negb]. cbv iota. step. (* j 81f0c *)
      apply (G74 (Z_to_bv 64 ((phi + 16) mod 8))). }
  (* step into the loop at i = 0 and discharge the join with Htail *)
  replace (Z_to_bv 64 (phi + 18)) with (Z_to_bv 64 (phi + 18 + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (psum (skipn 18 bs) 0)) by reflexivity.
  replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 - Z.of_nat 0)) by (f_equal; lia).
  apply (f6_loop_F RNG ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a6 a7 (Z_to_bv 64 tlen) s3 s4i s5 s6
           (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i s11 t3 t4 t5 t6 Fr fc m phi bs QE
           Hphi0 Hphi50 Hlen HB HA Htail RBUF RSHA 32 0 a4i a5i eq_refl ltac:(lia)).
Qed.

(* F6.f6_e28_evt's statement back from f6_e28_evt_F at RNG_all: the record buffer's bounds are the lemma's own, its
   shadow span lies below 2^64 (f6F_sh_all), and the two spill cells lie in [A+240, A+288) <= 2^64. *)
Lemma f6_e28_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi A tlen v8 e240 : Z) (bs : list byte),
    0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat ->
    bytes_at rsegs m phi bs -> addressable m phi 50 ->
    0 <= A -> A + 288 <= 2 ^ 64 -> stk rsegs m (A + 240) (A + 288) ->
    0 <= v8 < 2 ^ 64 -> q64 m (A + 240) e240 -> e240 = (if v8 =? 0 then 0 else 1) ->
    F6LE.evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6 a7
                       (Z_to_bv 64 tlen) s3 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 0 else 1)) s5 s6
                       (Z_to_bv 64 phi) (Z_to_bv 64 v8) (Z_to_bv 64 (f6_s9 bs)) (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f54) fc None
                  (write_to_mem m (wa (A + 280)) (le8 (Z_to_bv 64 (if psum (skipn 18 bs) 32 mod 256 =? 0 then 1 else 0))))
                  (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 0)
               (Z_to_bv 64 (phi + 18)) (Z_to_bv 64 32) a4i a5i a6 a7
               (Z_to_bv 64 tlen) s3 s4i s5 s6 (Z_to_bv 64 phi) (Z_to_bv 64 v8) s9i (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ec0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a4i a5i a6 a7 s3 s4i s5 s6 s9i s11 t3 t4 t5 t6 Fr fc m phi A tlen v8 e240 bs
    Hphi0 Hphi50 Hlen HB HA HA0 HA288 Hstk Hv8 Hq240 He240.
  eapply evtF_evt, (f6_e28_evt_F RNG_all); try eassumption.
  - apply rng_all; lia.
  - apply f6F_sh_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
Qed.

(* The pin: f6_e28_evt_of_F states F6.f6_e28_evt's v1.9 text, term for term. *)
Example f6_e28_evt_of_F_verbatim : True.
Proof.
  let a := type of F6.f6_e28_evt in let b := type of f6_e28_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------- 0x81f54 -> 0x81f64 under a footprint: the parse call ---------------- *)
Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

Lemma f6_ebc_evt_F :
  forall (RNG : footprint),
    reac_ctrl_parse_contract_F ->
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    rng_bytes RNG ->
    rng RNG IMG_LO IMG_LEN ->
    rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> rng RNG f 50) ->
    (50 <= n -> rng RNG (sh_lo f) (sh_len f 50)) ->
    rng RNG REAC_CTRL_PARSE_BC 6 ->
    rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81f64) fc None m' (seg_rom rsegs) /\
         munch (f6_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (seg_rom rsegs)).
Proof.
  intros RNG HPF ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs
    Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS
    RBY RIMG RWIN RWSH RF RFSH RBC RBCSH RHDR RW1 RTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HSKl : 0x5fe000 <= S - REAC_CTRL_PARSE_K) by (unfold HIGHMEM_BEG in HHI; lia).
  (* the premises on the normalized memory *)
  pose proof (proj1 (f6_stk_iff m (normalize rsegs m) (S - REAC_CTRL_PARSE_K) S REL HSKl ltac:(lia)) HST)
    as HSTn.
  pose proof (mem_inv_normalize rsegs m) as HMIn.
  assert (HRDn : forall i, In i (cp_rd n bs) ->
            mrd rsegs (normalize rsegs m) (wa (f + Z.of_nat i)) = nth_error bs i).
  { intros i Hi. rewrite <- (mrd_rel rsegs m _ _ REL). exact (HRD i Hi). }
  pose proof (f6_cells_rel m _ REL HAC) as HACn.
  pose proof (proj1 (f6_sw_iff m _ REL) HSW) as HSWn.
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HWA) as HWAn.
  assert (HFAn : 50 <= n -> addressable (normalize rsegs m) f 50)
    by (intros Hb; exact (proj1 (f6_addr_iff m _ _ _ REL) (HFA Hb))).
  pose proof (proj1 (f6_addr_iff m _ _ _ REL) HBC) as HBCn.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H1) as H1n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H2) as H2n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H3) as H3n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H4) as H4n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H5) as H5n.
  pose proof (proj1 (f6_fp_iff _ m _ _ _ _ _ _ _ REL) HFP) as HFPn.
  assert (HTLSn : reac_ctrl_parse_tls (normalize rsegs m) (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S).
  { intros DT TS C T DB k HT. apply HTLS. exact (proj2 (f6_tls_iff m _ _ _ _ _ _ _ _ REL) HT). }
  (* the tls footprint premise, moved to the normalized memory by the same iff *)
  assert (RTLSn : forall DT TS C T DB k,
            asan_tls_cells (normalize rsegs m) (bv_unsigned tp) DT TS C T DB k ->
            Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)).
  { intros DT TS C T DB k HT. apply RTLS. exact (proj2 (f6_tls_iff m _ _ _ _ _ _ _ _ REL) HT). }
  clear HST HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS RTLS.
  (* 0x81f54 mv a0,s7 ; 0x81f58 mv a1,s2 ; 0x81f5c li a2,0 ; 0x81f60 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPF as HP. unfold reac_ctrl_parse_contract_F, REAC_CTRL_PARSE in HP.
  eapply evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG); [exact HRO |].
    eapply HP with (f := f) (n := n) (o := 0) (S := S) (FS := FS) (fr := bs) (junk := []).
    all: try reflexivity.
    all: try assumption.
    all: try lia.
    all: try (intros Ho; exfalso; apply Ho; reflexivity). }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & _ & ACm & SR & AD & FP & _) & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  set (mm' := ms_mem ms') in Hrel, HROs.
  rewrite (f6_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  apply evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mm'.
  split.
  { replace (ret_pc (Z_to_bv 64 0x81f64)) with (Z_to_bv 64 0x81f64)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  split; [exact (munch_rel rsegs (f6_PW S FS) m (normalize rsegs m) mm' m0' REL Hrel HROs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mm' m0' REL Hrel HROs WM)|].
  split; [exact (ro_agree_same rsegs m mm' HRO HROs)|].
  split; [exact (proj2 (f6_stk_iff mm' m0' (S - REAC_CTRL_PARSE_K) S Hrel HSKl ltac:(lia)) ST)|].
  split; [exact (proj2 (f6_sw_iff mm' m0' Hrel) SR)|].
  split; [exact (proj2 (f6_addr_iff mm' m0' _ _ Hrel) AD)|].
  exact (proj2 (f6_fp_iff _ mm' m0' _ _ _ _ _ _ Hrel) FP).
Qed.

(* F6.f6_ebc_evt's statement (after its Section hypothesis, the plain parse contract) back from f6_ebc_evt_F at
   RNG_all: rng_bytes holds of RNG_all by definition, the image / BC ranges are literals, the window and its
   shadow come from S mod 16 = 0 and HIGHMEM_BEG <= S - K <= S <= APPMEM_END, f and its shadow from the 50 <= n
   premise, the side-stack header and the class-1 ranges from fp's fs_place, and the thread cells from the
   bytes_at bounds of asan_tls_cells. The callee premise of the corollary is the plain contract, lifted by
   reac_ctrl_parse_contract_of_F's twin direction: the corollary takes reac_ctrl_parse_contract_F, as the
   consumer's callee twin, and the pin strips F6.v's plain hypothesis. *)
Lemma f6_ebc_evt_of_F :
    reac_ctrl_parse_contract_F ->
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    F6LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f64) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81f64) fc None m' (seg_rom rsegs) /\
         munch (f6_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3 s4 s5 s6 (Z_to_bv 64 f) s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f54) fc None m (seg_rom rsegs)).
Proof.
  intros HPF ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs
    Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (HK : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  eapply evtF_evt, (f6_ebc_evt_F RNG_all HPF); try eassumption.
  - intros b j _ _ _. exact I.
  - rng_lit.
  - apply rng_all; unfold HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply rng_all; unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *; Z.div_mod_to_equations; lia.
  - intros Hb. destruct (Hbig Hb) as (Hf0 & Hf50 & _). apply rng_all; lia.
  - intros Hb. destruct (Hbig Hb) as (Hf0 & Hf50 & _). apply f6F_sh_cov_all; lia.
  - rng_lit.
  - apply f6F_sh_cov_all; unfold REAC_CTRL_PARSE_BC; lia.
  - (* side-stack header *) apply rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply rng_all; lia|]).
    destruct Hiv.
Qed.

End RunF.

(* The pin: f6_ebc_evt_of_F states F6.f6_ebc_evt's v1.9 text after F6.v's first premise, the plain parse contract
   (F6.v Section S, Hypothesis HPARSE), with the footprint form of that contract in its place. *)
Example f6_ebc_evt_of_F_verbatim : True.
Proof.
  lazymatch type of F6.f6_ebc_evt with ?P -> ?A =>
    constr_eq P reac_ctrl_parse_contract;
    lazymatch type of f6_ebc_evt_of_F with ?P' -> ?B =>
      constr_eq P' reac_ctrl_parse_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.
