(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 495 of its 533 lines of code are new or changed and 358 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F22.v, with its module paths and module names changed; 120 of its 220 lines of code are new or changed and 433 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F22.v 933f14d98428 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F22.<r> at ExecF.RNG_all (the CPS premise of f22_loop by
   lib/Lib/ExecF_all.evt_evtF_all); <r>_of_F_verbatim checks by constr_eq that its type is the type of F22.<r>
   (f22_tail: after F22's own first premise, the plain record-verifier contract). Mechanical re-run, route (a)
   (lead 22:15Z); input to the ported walk only.
   Callee _F cited: reac_ctrl_headamp_record_verify_contract_F, proved by
   lib/A/Prog/reac_ctrl_headamp_record_verify_F.v (blob 87d3a9c0822b, copied byte-for-byte from 911c6aa5d24 with its
   statement's home lib/A/Prog/reac_ctrl_headamp_record_verify_c.v blob a751f3b5d3ae; neither is on fdd2ed9f9d7). *)
(* Footprint twins of Seg/F22.v f22_loop / f22_tail: the same runs as ExecF.evtF under a footprint RNG.
   f22_loop (0x82554 -> 0x8258c, six turns) reads, per turn i, the shadow byte of X + i and the record byte at
   X + i, so its footprint premises are the regions its own premises name: the six bytes [X, X + 6) of its
   bytes_at, and the shadow bytes of those six bytes.  f22_tail (0x8258c -> 0x825a0) is register arithmetic and the
   call of reac_ctrl_headamp_record_verify, so its footprint premises are exactly the callee's: the record bytes
   [phi+18, phi+20) and [phi+34, phi+40), the shadow bytes of those, the callee frame [sp-16, sp), the GOT cell of
   the shadow-offset cell and that cell.  F22.v is unchanged apart from comment text.
   The only script changes against F22.v are engine heads: F22's Ltac f22_br matches `evt _ _ (MS ...)`, so the
   twin uses the same tactic over `ExecF.evtF _ _ _ (MS ...)` (f22F_br below); the rest is F22's text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_headamp_record_verify_c.
(* The record verifier's owner proof; not imported, so its helper names shadow nothing here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_headamp_record_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F22.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all.
(* StepF after the old engine: its step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* YK11 last, as in F22.v (its seg_rom). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11.
Import ListNotations.
Open Scope Z_scope.

Module HRVF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_headamp_record_verify_F.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.

(* F22's f22_br over the footprint engine's goal head. *)
Ltac f22F_br v pf :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; pf); cbv iota
  end.

(* The instrumented check of byte y loads the shadow byte at (y >> 3) + ASAN_K; it lies in the shadow range of a
   block [x, z] that contains y (the same helper as Seg/F21F.v's f21_sh_rng). *)
Lemma f22_sh_rng : forall (RNG : ExecF.footprint) x y z, 0 <= x <= y -> y <= z ->
  ExecF.rng RNG (shadow_addr x) (shadow_addr z - shadow_addr x + 1) ->
  ExecF.rng RNG (Z.shiftr y 3 + ASAN_K) 1.
Proof.
  intros RNG x y z Hxy Hyz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono y z 8 ltac:(lia) ltac:(lia)).
  eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr; lia.
Qed.

(* ---- The record-sum loop as an evtF, 0x82554 -> 0x8258c, by F22.f22_loop's induction on the down-counter. ---- *)
Lemma f22_loop_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z) (rec : list byte),
  s10 = Z_to_bv 64 ASAN_K -> 0 <= X -> X + 6 <= 2 ^ 64 ->
  length rec = 6%nat -> bytes_at rsegs m X rec ->
  (forall i, (i < 6)%nat -> b8 m (Z.shiftr (X + Z.of_nat i) 3 + ASAN_K) 0) ->
  (forall a0' a2' a3' a4' : word,
     ExecF.evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (psum rec 6)) a2' a3' a4' a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (a0 a1 a2 a3 a4 : word),
    (i + n = 6)%nat -> (0 < n)%nat ->
    a0 = Z_to_bv 64 (X + Z.of_nat i) -> a2 = Z_to_bv 64 (X + Z.of_nat i) ->
    a3 = Z_to_bv 64 (Z.of_nat n) -> a1 = Z_to_bv 64 (psum rec i) ->
    ExecF.rng RNG X 6 ->
    ExecF.rng RNG (shadow_addr X) (shadow_addr (X + 5) - shadow_addr X + 1) ->
    ExecF.evtF rsegs RNG Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    Fr (Z_to_bv 64 0x82554) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m X rec
    E26 HX0 HX6 Lrec Hrec Hsh HK n.
  subst s10.
  induction n as [|n IH]; intros i a0 a1 a2 a3 a4 Hin Hpos E0 E2 E3 E1 RDAT RSH; [lia|]. subst a0 a1 a2 a3.
  (* the two accesses of this turn, from the lemma's own regions *)
  pose proof (ExecF.rng_sub RNG X 6 (X + Z.of_nat i) 1 RDAT ltac:(lia) ltac:(lia)) as RCb.
  pose proof (f22_sh_rng RNG X (X + Z.of_nat i) (X + 5) ltac:(lia) ltac:(lia) RSH) as RCs.
  pose proof (f22_rd1 m _ _ (Hsh i ltac:(lia))) as RDs.
  pose proof (f22_rdb m X rec i Hrec ltac:(lia)) as RDb.
  pose proof (f22_psum_range rec i) as PR.
  pose proof (f22_ubyte (nth i rec (Z_to_bv 8 0))) as RB.
  (* 0x82554 srli a4,a0,3 ; 0x82558 add a4,a4,s10 ; 0x8255c lb a4,0(a4) = 0 ; 0x82560 bnez a4 (not taken) *)
  step. step. ush. step. step. if_false.
  (* 0x82564 lbu a4,0(a2) ; 0x82568 addi a3,a3,-1 ; 0x8256c addi a0,a0,1 ; 0x82570 add a1,a1,a4 *)
  step. step. step. step. rewrite f22_psum_S_zxb.
  (* 0x82574 addi a2,a2,1 ; 0x82578 bnez a3,0x82554 *)
  step. step.
  destruct n as [|n'].
  - (* last turn: fall through, 0x8257c j 0x8258c *)
    f22F_br false ltac:(rewrite f22_eqb_small by lia; f22_zdec).
    step.
    assert (Ei : i = 5%nat) by lia. subst i.
    apply HK.
  - f22F_br true ltac:(rewrite f22_eqb_small by lia; f22_zdec).
    eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | reflexivity
                       | exact RDAT | exact RSH].
Qed.

(* F22.f22_loop's statement as a corollary: the twin at RNG_all, its CPS premise mapped by evt_evtF_all and each
   rng premise by rng_all (bounds from the lemma's own 0 <= X and X + 6 <= 2^64). *)
Lemma f22_loop_of_F : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z) (rec : list byte),
  s10 = Z_to_bv 64 ASAN_K -> 0 <= X -> X + 6 <= 2 ^ 64 ->
  length rec = 6%nat -> bytes_at rsegs m X rec ->
  (forall i, (i < 6)%nat -> b8 m (Z.shiftr (X + Z.of_nat i) 3 + ASAN_K) 0) ->
  (forall a0' a2' a3' a4' : word,
     evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (psum rec 6)) a2' a3' a4' a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (a0 a1 a2 a3 a4 : word),
    (i + n = 6)%nat -> (0 < n)%nat ->
    a0 = Z_to_bv 64 (X + Z.of_nat i) -> a2 = Z_to_bv 64 (X + Z.of_nat i) ->
    a3 = Z_to_bv 64 (Z.of_nat n) -> a1 = Z_to_bv 64 (psum rec i) ->
    evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    Fr (Z_to_bv 64 0x82554) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m X rec
    E26 HX0 HX6 Lrec Hrec Hsh HK n i a0 a1 a2 a3 a4 Hin Hpos E0 E2 E3 E1.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f22_loop_F ExecF.RNG_all Q ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m X rec E26 HX0 HX6 Lrec Hrec Hsh
           (fun a0' a2' a3' a4' => EFA.evt_evtF_all rsegs _ _ (HK a0' a2' a3' a4'))
           n i a0 a1 a2 a3 a4 Hin Hpos E0 E2 E3 E1).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

Example f22_loop_of_F_verbatim : True.
Proof.
  let A := type of F22.f22_loop in let B := type of f22_loop_of_F in constr_eq A B.
  exact I.
Qed.

Section SF.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.

(* ---- 0x8258c -> 0x825a0 as an evtF: s4 from the record sum, a0 = s7 = phi, and the call of
   reac_ctrl_headamp_record_verify under the callee's footprint contract (its owner's proof
   reac_ctrl_headamp_record_verify_holds_F, so the twin takes no contract premise). ---- *)
Lemma f22_tail_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rec : list byte),
    0 <= sp < 2 ^ 64 -> 0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> length rec = 6%nat -> bytes_at rsegs m (phi + 34) rec ->
    stk rsegs m lo sp -> asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    ExecF.rng RNG (phi + 18) 2 -> ExecF.rng RNG (phi + 34) 6 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (shadow_addr (phi + 34)) (shadow_addr (phi + 39) - shadow_addr (phi + 34) + 1) ->
    ExecF.rng RNG (sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (if psum rec 6 mod 128 =? 0 then 0 else -1)) s5 s6 (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum rec 6)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rec Rsp Hp0 HpE Hpsp Hlo Hlo16 H18 Lrec Hrec Hstk HAC HSW Had2 Had6
    R18 R34 RS18 RS34 RFr RGOT RCK.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof (f22_psum_range rec 6) as PR. change (Z.of_nat 6) with 6 in PR.
  (* 0x8258c andi a0,a1,127 ; 0x82590 seqz s4,a0 ; 0x82594 addi s4,s4,-1 *)
  step. step. step.
  rewrite (f22_s0 (psum rec 6)) by lia.
  (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
  step. step.
  eapply ExecF.evtF_cut.
  { eapply HRVF.reac_ctrl_headamp_record_verify_holds_F with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := rec);
      unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Esp.
    - first [reflexivity | f_equal; lia].
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - exact H18.
    - exact Lrec.
    - exact Hrec.
    - exact Hstk.
    - lia.
    - left. lia.
    - left. lia.
    - exact HAC.
    - exact HSW.
    - exact Had2.
    - exact Had6.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
      lia.
    - exact RFr.
    - exact RGOT.
    - exact RCK.
    - exact R18.
    - exact R34.
    - exact RS18.
    - exact RS34. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply ExecF.evtF_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

(* F22.f22_tail restated: evtF_evt of the twin at RNG_all, each rng premise by rng_all. *)
Ltac f22_rng_all :=
  apply ExecF.rng_all;
  unfold shadow_addr, GOT_CELL_K, CELL_K, ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.

Lemma f22_tail_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rec : list byte),
    0 <= sp < 2 ^ 64 -> 0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> length rec = 6%nat -> bytes_at rsegs m (phi + 34) rec ->
    stk rsegs m lo sp -> asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (if psum rec 6 mod 128 =? 0 then 0 else -1)) s5 s6 (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum rec 6)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rec Rsp Hp0 HpE Hpsp Hlo Hlo16 H18 Lrec Hrec Hstk HAC HSW Had2 Had6.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f22_tail_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m phi lo sp b0 b1 rec); try assumption; f22_rng_all.
Qed.

End SF.

(* The pin: f22_tail_of_F states F22's text after F22's own first premise, the plain record-verifier contract
   (F22.v Section S, Hypothesis HARV), term for term (constr_eq: syntactic, not up to conversion). *)
Example f22_tail_of_F_verbatim : True.
Proof.
  lazymatch type of F22.f22_tail with ?P -> ?A =>
    constr_eq P reac_ctrl_headamp_record_verify_contract;
    let B := type of f22_tail_of_F in constr_eq A B
  end.
  exact I.
Qed.
