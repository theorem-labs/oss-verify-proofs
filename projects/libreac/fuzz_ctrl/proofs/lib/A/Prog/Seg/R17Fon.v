(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 629 of its 730 lines of code are new or changed and 1401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R17.v; 39 of its 110 lines of code are new or changed and 659 lines of the source are left out. *)
(* lib/A/Prog/Seg/R17Fon.v -- route (C) twin of a Theorem Labs lane's footprint run A.Prog.Seg.R17F.r17_evt_F (source not in this delivery), for fuzz_ctrl
   image A's walk stage seg_R17 (glue lib/A/ACtlG/R17.v).  Written by a Theorem Labs lane;
   single writer.  rule 24: no function proved (stage glue of a walk; kind: segment lemma).  ADDITIVE beside-file:
   a Theorem Labs lane's lib/A/Prog/Seg/R17F.v (not in this delivery) is not edited.

   PROVENANCE.  Base text: a Theorem Labs lane's fold a working branch 4bae33fdf54, lib/A/Prog/Seg/R17F.v (not in this delivery) blob
   bbdfb80ade0 (lemma r17_evt_F).  That blob differs from a working branch's R17F.v (an earlier version, blob e5d2fd55e19, not in this delivery) (
   a working branch 1899bed1aee) only by qualification: it names lib/Lib's Frame through a Module alias
   LFr and writes the full path of MState.unsigned_lit.  Here lib/Lib's Frame is written by its full path
   (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame), with no Module alias.  The image, the run
   [0x8183c, 0x81858) and its regions are R17F.v's (its header: image A = fuzz_ctrl.asan, libreac v1.9.0, sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d; source Seg/R17.v r17_evt).

   THE FORM RULE (a Theorem Labs lane's L3-brief.md (a working note, not in this delivery); a Theorem Labs lane 12:52Z, agreed; a Theorem Labs lane approved R17Fon):
   a twin of a Seg run whose premise is the universal `shadow_rw m` REMOVES that premise if the run neither reads nor
   stores shadow through it, else NARROWS it to the region it reads and stores (via the callees' own R); the callees
   are taken in their _on form.

   WHAT CHANGED against r17_evt_F (binders, premise order and post otherwise identical):
   - the first premise is the callee's region-form footprint contract
     A.Prog.reac_ports_parse_c.reac_ports_parse_contract_F_on (reac_ports_parse_c.v 3cb58b9552c (the blob this tree had at release c5e779efe8c), :141) in place
     of reac_ports_parse_contract_F: the same contract with `shadow_rw m` dropped from its asan premise
     (`asan_cells m /\ addressable m p 20 /\ addressable m q 12`), same post reac_ports_parse_post;
   - the premise `shadow_rw m` (R17F.v bbdfb80ade0:59, between `asan_cells m` and `addressable m (phi + 18) 20`) is
     REMOVED, not narrowed.  Why: the run's own five instructions before the call (two spill loads `ld a1,112(s1)` /
     `ld a1,216(s1)` from the ro_cells premises, `beq`, `addi s11,s8,18`, `mv a0,s11`) and the `jal` touch no shadow
     byte; in r17_evt_F's proof the only use of that premise (HSW, introduced at :92) is :113, `split; [exact HSW|]`,
     which feeds the callee's asan bundle; the _on contract no longer has that conjunct.  So the run reads and stores
     no shadow through the premise.  The callee's own shadow reads (of p and q) are justified inside the callee from
     addressable m p 20 / addressable m q 12 (reac_ports_parse_c.v's route (C) comment), which stay premises here.
   The proof is r17_evt_F's, with the HSW binder and its one use deleted.

   No global setting (Local only), no Module alias, no Section hypothesis, no unproved step. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcDecl RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm B3FrCl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R17.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11's getr (the register read the statement below is built over), as R17.v does. *)
Import YK11.
Local Open Scope Z_scope.

(* ---- The Lib-level run of [0x8183c, 0x81858) with the region-form reac_ports_parse footprint contract. ---- *)
Lemma r17_evt_F_on : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ports_parse_c.reac_ports_parse_contract_F_on ->
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A phi q mr lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 mr -> s8 = Z_to_bv 64 phi ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= q -> q + 12 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    ro_cells rsegs m (A + 112) [C8 (Z_to_bv 64 mr)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 q)] ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    q mod 4 = 0 -> wr_at rsegs m q 12 ->
    (q + 12 <= phi + 18 \/ phi + 18 + 20 <= q) ->
    (phi + 18 + 20 <= spv - 16 \/ spv <= phi + 18) -> (q + 12 <= spv - 16 \/ spv <= q) ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    asan_cells m ->
    addressable m (phi + 18) 20 -> addressable m q 12 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside [(spv - 16, spv); (q, q + 12)] x) ->
    RcLeaf.ports_ok (phi + 18) q bs = true ->
    (* 0x8183c ld a1,112(s1) and 0x81850 ld a1,216(s1): the two ro_cells of the premises *)
    rng RNG (A + 112) 8 ->
    rng RNG (A + 216) 8 ->
    (* the callee's regions (reac_ports_parse_contract_F_on's rng premises, p := phi + 18) *)
    rng RNG (spv - REAC_PORTS_PARSE_FRAME) REAC_PORTS_PARSE_FRAME ->
    rng RNG GOT_CELL_K 8 ->
    rng RNG CELL_K 8 ->
    rng RNG (phi + 18) 20 ->
    rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 18 + 19) - shadow_addr (phi + 18) + 1) ->
    rng RNG q 12 ->
    rng RNG (shadow_addr q) (shadow_addr (q + 11) - shadow_addr q + 1) ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81858) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\
         getr R 24 = Z_to_bv 64 phi /\ getr R 10 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (phi + 18) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.munch [(spv - 16, spv); (q, q + 12)] m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono rsegs m m' /\
         stk rsegs m' lo spv /\
         bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * RcLeaf.n_in bs))) /\
         bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out bs))) /\
         bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt bs 7))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8183c) fc None m (seg_rom rsegs)).
Proof.
  intros PPF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi q mr lo bs -> -> -> -> Hphi0 Hphi50 Hq0 Hqb Hspv0 Hspv
    RO1 RO2 Hlen HB Hqmod HWR Hdisj Hsep1 Hsep2 ST Hlo16 HAC HAp HAq HOutside Hok
    R112 R216 RFR RGOT RCELL RP RPS RQ RQS.
  step.                                 (* 8183c ld a1,112(s1) : a1 := mr *)
  step. if_true_by (r17_eqb_refl (Z_to_bv 64 mr)).    (* 81840 beq a0,a1,81848 taken *)
  step.                                 (* 81848 addi s11,s8,18 *)
  step.                                 (* 8184c mv a0,s11 *)
  clear RO1.
  step.                                 (* 81850 ld a1,216(s1) : a1 := q *)
  step.                                 (* 81854 jal reac_ports_parse *)
  eapply evtF_cut.
  { eapply PPF with (p := phi + 18) (q := q) (lo := lo) (bs := bs).
    - first [ reflexivity | f_equal; lia ].
    - reflexivity.
    - lia.
    - lia.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Hlo16.
    - intros _ _. split; [exact Hlen | exact HB].
    - intros _ _. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      split; [exact Hqmod|]. split; [exact HWR|]. split; [exact Hdisj|].
      split; [exact Hsep1 | exact Hsep2].
    - intros _ _. split; [exact HAC|]. split; [exact HAp | exact HAq].
    - intros _ _. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      exact HOutside.
    - rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RFR.
    - intros _ _.
      split; [exact RGOT|]. split; [exact RCELL|]. split; [exact RP|]. split; [exact RPS|].
      split; [exact RQ | exact RQS]. }
  intros ms' PO. unfold reac_ports_parse_post in PO. rewrite Hok in PO.
  destruct PO as (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & MI & STc & HI & HO & H8 & MUc).
  subst ms'.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 14 (split; [reflexivity|]).
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in MUc, STc by lia.
  split; [exact MUc|]. split; [exact WM|]. split; [exact STc|].
  split; [exact HI|]. split; [exact HO | exact H8].
Qed.

Print Assumptions r17_evt_F_on.
