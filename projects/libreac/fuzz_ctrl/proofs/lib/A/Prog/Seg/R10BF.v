(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names and addresses changed; 1437 of its 1585 lines of code are new or changed and 1354 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10B.v; 170 of its 350 lines of code are new or changed and 1405 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R10B.v blob 260216a100ea (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r10b_evt_of_F re-derives R10B.r10b_evt at ExecF.RNG_all; r10b_evt_of_F_verbatim checks by constr_eq that
   its type is the type of R10B.r10b_evt, the first premise aside (the plain contract there, the _F contract here).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) twin of R10B.v's one run lemma (r10b_evt, R10B.v:734), both fragment arms (b = 6 and b = 5)
   of segment R10 from 0x81680 to the arm's exit pc, re-stepped with lib.Lib StepF as an ExecF.evtF under a
   universally quantified footprint RNG, with the same post-state predicate (R10B.r10b_K).
   The run's own accesses (instruction fetch is not an access):
     the three metadata stores 0x81684 / 0x81688 / 0x8168c, inside the window the premise
       `stk rsegs m (SHv + 306) (SHv + 313)` names: rng RNG (SHv + 306) 7;
     the four argument loads `ld a0,48(s1)`, `ld a3,88(s1)`, `ld a4,80(s1)`, `ld a5,72(s1)` (0x816ec .. 0x81700 on
       the b = 6 arm, 0x817ac .. 0x817c0 on the b = 5 arm), which R10B.r10b_pre names:
       rng RNG (A + 48) 8, rng RNG (A + 88) 8, rng RNG (A + 80) 8, rng RNG (A + 72) 8.
   The two `li` / `mv` arguments and every branch of both arms are register-only.
   The callee enters through its footprint contract reac_ctrl_identity_fragment_contract_F
   (lib/A/Prog/reac_ctrl_identity_fragment_c.v:91) as the Section hypothesis FRAGF, in the place of R10B.r10b_evt's
   plain FGC.reac_ctrl_identity_fragment_contract premise; its rng premises are passed through at this call's
   values (f = fr + 2256, fr = phi, pa = fr + 2448, pp = fr + 2464, pn = fr + 2496), with the guards discharged
   from the owner's 0 < phi, 6283264 <= fr and 50 <= nb. As in R10B.r10b_evt the call is made on the normalized
   memory; the evtF form of that transfer is MemNormF.evtF_normalize_ro (the evtF twin of MemNorm.evt_normalize).
   r10b_evt_of_F re-derives R10B.r10b_evt's conclusion at ExecF.RNG_all. R10B.v itself is unchanged. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcLay RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 B3Rtm R10B.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step / mem_after_store (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* R10B.r10b_sb / r10b_newb / r10b_keepb restated for evtF goals (the owner's matches are on `evt _ _ (MS ...)`,
   which an evtF goal does not meet); the bodies are the owner's. *)
Ltac r10bF_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (R10B.r10b_stk_store_ok mm (SHv + 306) (SHv + 313) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 306, SHv + 313)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite ?length_le1; cbn [length Z.of_nat]; lia
           | rewrite ?length_le1; cbn [length inside Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 306) (SHv + 313) (SHv + off) bs) in STh;
         [ | lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

Ltac r10bF_newb SHv off v Bn :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      assert (Bn : bytes_at rsegs (write_to_mem mm (wa (SHv + off)) bs) (SHv + off) [Z_to_bv 8 v]) by
        (replace [Z_to_bv 8 v] with bs by (apply a_bytes_eq; vm_compute; reflexivity);
         apply (bytes_at_write_same rsegs mm (SHv + off) bs);
         [ lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ])
  end.

Ltac r10bF_keepb SHv off Bn :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      apply (bytes_at_write_other rsegs mm (SHv + off) bs) in Bn;
        [ | lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia ]
  end.

(* The rng premises of the callee contract at ExecF.RNG_all (for r10b_evt_of_F). *)
Lemma r10b_bytes_all : rng_bytes ExecF.RNG_all.
Proof. intros b j _ _ _. exact I. Qed.

(* The aligned 8-byte cover of the shadow bytes of [lo, z], at RNG_all. *)
Lemma r10b_sh_all : forall lo z, 0 <= lo -> lo <= z -> z < 2 ^ 64 ->
  ExecF.rng ExecF.RNG_all (shadow_addr lo / 8 * 8) (shadow_addr z / 8 * 8 + 8 - shadow_addr lo / 8 * 8).
Proof.
  intros lo z H0 H1 H2. apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* Proof speed (common.md Proof-speed (2)): hide disjunctions and mod facts from lia; unfold at each use site. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.

Section R10BF.
(* The callee's footprint contract, in the place of R10B.r10b_evt's plain contract premise. *)
Hypothesis FRAGF : FGC.reac_ctrl_identity_fragment_contract_F.

Lemma r10b_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bb pce spv A SHv fr phi nb : Z) (g st : list byte),
    (bb = 6 /\ pce = 0x81708) \/ (bb = 5 /\ pce = 0x817c8) ->
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 SHv -> s7 = Z_to_bv 64 bb ->
    s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 11 -> s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K -> spv <= APPMEM_END -> spv mod 16 = 0 ->
    0 <= A -> A + 96 <= 2 ^ 64 -> 6283264 <= SHv -> SHv + 313 <= 2 ^ 64 ->
    6283264 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> fr mod 8 = 0 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= nb < 2 ^ 64 ->
    (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) ->
    (phi + 50 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) ->
    (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
    app_mem (fr + 2256 + 78) -> length g = 50%nat -> length st = 72%nat ->
    stk rsegs m (SHv + 306) (SHv + 313) -> ro_agree rsegs m ->
    (forall m1, munch [(SHv + 306, SHv + 313)] m m1 -> wmono rsegs m m1 ->
       stk rsegs m1 (SHv + 306) (SHv + 313) -> ro_agree rsegs m1 ->
       bytes_at rsegs m1 (SHv + 306) [Z_to_bv 8 2] -> bytes_at rsegs m1 (SHv + 308) [Z_to_bv 8 0] ->
       bytes_at rsegs m1 (SHv + 312) [Z_to_bv 8 0] -> R10B.r10b_pre m1 A spv fr phi g st) ->
    (* the run's own regions: the three metadata stores and the four argument loads *)
    ExecF.rng RNG (SHv + 306) 7 ->
    ExecF.rng RNG (A + 48) 8 -> ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 ->
    ExecF.rng RNG (A + 72) 8 ->
    (* the callee's regions (reac_ctrl_identity_fragment_contract_F's rng premises, at this call's values) *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    ExecF.rng RNG phi 50 ->
    ExecF.rng RNG (shadow_addr phi / 8 * 8) (shadow_addr (phi + 49) / 8 * 8 + 8 - shadow_addr phi / 8 * 8) ->
    ExecF.rng RNG (fr + 2256) 72 ->
    ExecF.rng RNG (shadow_addr (fr + 2256) / 8 * 8)
      (shadow_addr (fr + 2256 + 71) / 8 * 8 + 8 - shadow_addr (fr + 2256) / 8 * 8) ->
    ExecF.rng RNG (fr + 2448) 2 ->
    ExecF.rng RNG (shadow_addr (fr + 2448) / 8 * 8)
      (shadow_addr (fr + 2448 + 1) / 8 * 8 + 8 - shadow_addr (fr + 2448) / 8 * 8) ->
    ExecF.rng RNG (fr + 2464) 8 ->
    ExecF.rng RNG (shadow_addr (fr + 2464) / 8 * 8)
      (shadow_addr (fr + 2464 + 7) / 8 * 8 + 8 - shadow_addr (fr + 2464) / 8 * 8) ->
    ExecF.rng RNG (fr + 2496) 8 ->
    ExecF.rng RNG (shadow_addr (fr + 2496) / 8 * 8)
      (shadow_addr (fr + 2496 + 7) / 8 * 8 + 8 - shadow_addr (fr + 2496) / 8 * 8) ->
    ExecF.evtF rsegs RNG
      (fun ms => exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs) /\
         R10B.r10b_K sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SHv spv fr nb pce g st R pc' m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bb pce spv A SHv fr phi nb g st Harm -> -> -> -> -> -> -> -> HspK HspE Hsp16 HA0 HA96 HSH0 HSHb
    Hfr0 Hfrb Hfr8 Hphi0 Hphib Hnb Hphifr Hphiw Hfrw Happf Hgl Hstl ST HRO HPRE
    RSH R48 R88 R80 R72 RBYT RIMG RWIN RWINS RPHI RPHIS RFRG RFRGS RPAa RPAS RPPa RPPS RPNa RPNS.
  unfold FGC.reac_ctrl_identity_fragment_contract_F in FRAGF.
  assert (EK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof (munch_refl [(SHv + 306, SHv + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ecls : fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) nb st g = fcls nb st g)
    by (apply R10B.r10b_cls; lia).
  assert (DJ : R10B.r10b_box ((phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
                       (phi + 50 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) /\
                       (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr)))
    by exact (conj Hphifr (conj Hphiw Hfrw)).
  clear Hphifr Hphiw Hfrw.
  apply rs_hide in Harm. apply rs_hide in Hsp16. apply rs_hide in Hfr8.
  (* 0x81680 li a3,2 ; 0x81684 .. 0x8168c the three metadata stores *)
  step.
  r10bF_sb SHv 306 ST MU WM. r10bF_newb SHv 306 2 B0.
  r10bF_sb SHv 308 ST MU WM. r10bF_keepb SHv 308 B0. r10bF_newb SHv 308 0 B1.
  r10bF_sb SHv 312 ST MU WM. r10bF_keepb SHv 312 B0. r10bF_keepb SHv 312 B1. r10bF_newb SHv 312 0 B2.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MI : ro_agree rsegs mm)
        by (apply (R10B.r10b_ro_keep m mm [(SHv + 306, SHv + 313)] HRO MU); intros x Hx;
            cbn [outside]; split; [lia | exact I])
  end.
  destruct (HPRE _ MU WM ST MI B0 B1 B2)
    as (R48c & R88c & R80c & R72c & STw & Hgb & ADphi & RWf & ADf & STf & ADpa & ADpp & ADpn & HAC & HSW &
        HB1 & HB2 & HB3 & HB4 & HB5).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      change (ov_read_bytes rsegs mm (wa (A + 48)) 8 = Some (le8 (Z_to_bv 64 (fr + 2256)))) in R48c;
      change (ov_read_bytes rsegs mm (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 (fr + 2448)))) in R88c;
      change (ov_read_bytes rsegs mm (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 (fr + 2464)))) in R80c;
      change (ov_read_bytes rsegs mm (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 (fr + 2496)))) in R72c
  end.
  (* 0x81690 li a2,4 ; 0x81694 blt s11,s7 (taken: 4 < bb); then the arm's own kind checks *)
  unfold rs_hold in Harm.
  destruct Harm as [[-> ->]|[-> ->]];
    [ step; step; first [ if_true_by R10B.r10b_c46 | if_true ];
      step; step; first [ if_false_by R10B.r10b_c65 | if_false ];
      step; step; first [ if_false_by R10B.r10b_c66 | if_false ];
      step; step; first [ if_true_by R10B.r10b_c1111 | if_true ];
      step; step; step; step; step; step; step
    | step; step; first [ if_true_by R10B.r10b_c45 | if_true ];
      step; step; first [ if_true_by R10B.r10b_c55 | if_true ];
      step; step; first [ if_true_by R10B.r10b_c1111 | if_true ];
      step; step; step; step; step; step; step ].
  (* the call's premises on the normalized memory *)
  all: lazymatch goal with
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in *
       end.
  all: unfold R10B.r10b_box in DJ.
  all: destruct DJ as (Hphifr & Hphiw & Hfrw).
  all: apply rs_hide in Hphifr; apply rs_hide in Hphiw; apply rs_hide in Hfrw.
  all: assert (MI1 : ro_agree rsegs m1) by exact MI.
  all: pose proof (mem_rel_normalize rsegs m1 MI1) as REL.
  all: assert (STw0 : stk rsegs (normalize rsegs m1) (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv)
    by exact (proj1 (R10B.r10b_rel_stk m1 _ (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv REL ltac:(lia) ltac:(lia)) STw).
  all: assert (STf0 : stk rsegs (normalize rsegs m1) (fr + 2256) (fr + 2504))
    by exact (proj1 (R10B.r10b_rel_stk m1 _ (fr + 2256) (fr + 2504) REL ltac:(lia) ltac:(lia)) STf).
  all: assert (Hgb0 : bytes_at rsegs (normalize rsegs m1) phi g)
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) Hgb).
  all: assert (RWf0 : rw_cells rsegs (normalize rsegs m1) (fr + 2256) [CB 72 st])
    by exact (proj1 (R10B.r10b_rel_rw m1 _ (fr + 2256) _ REL ltac:(lia)) RWf).
  all: assert (ADphi0 : addressable (normalize rsegs m1) phi 50)
    by exact (proj1 (R10B.r10b_rel_ad m1 _ _ _ REL) ADphi).
  all: assert (ADf0 : addressable (normalize rsegs m1) (fr + 2256) 72)
    by exact (proj1 (R10B.r10b_rel_ad m1 _ _ _ REL) ADf).
  all: assert (ADpa0 : addressable (normalize rsegs m1) (fr + 2448) 2)
    by exact (proj1 (R10B.r10b_rel_ad m1 _ _ _ REL) ADpa).
  all: assert (ADpp0 : addressable (normalize rsegs m1) (fr + 2464) 8)
    by exact (proj1 (R10B.r10b_rel_ad m1 _ _ _ REL) ADpp).
  all: assert (ADpn0 : addressable (normalize rsegs m1) (fr + 2496) 8)
    by exact (proj1 (R10B.r10b_rel_ad m1 _ _ _ REL) ADpn).
  all: assert (HAC0 : asan_cells (normalize rsegs m1)) by exact (proj1 (R10B.r10b_rel_cells m1 _ REL) HAC).
  all: assert (HSW0 : shadow_rw (normalize rsegs m1)) by exact (proj1 (R10B.r10b_rel_sw m1 _ REL) HSW).
  all: assert (HB10 : bytes_at rsegs (normalize rsegs m1) REAL_BCMP (le8 (wa BCMP)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB1).
  all: assert (HB20 : bytes_at rsegs (normalize rsegs m1) REAL_MEMCMP (le8 (wa MEMCMP)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB2).
  all: assert (HB30 : bytes_at rsegs (normalize rsegs m1) GOT_CF (le8 (wa CF)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB3).
  all: assert (HB40 : bytes_at rsegs (normalize rsegs m1) (CF + 254) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB4).
  all: assert (HB50 : bytes_at rsegs (normalize rsegs m1) (CF + 255) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB5).
  all: assert (P17 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 -> 50 <= nb ->
                bytes_at rsegs (normalize rsegs m1) phi g) by (intros; exact Hgb0).
  all: assert (P18 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 ->
                rw_cells rsegs (normalize rsegs m1) (fr + 2256) [CB 72 st] /\ (fr + 2448) mod 2 = 0 /\
                (fr + 2464) mod 8 = 0 /\ (fr + 2496) mod 8 = 0 /\
                wr_at rsegs (normalize rsegs m1) (fr + 2448) 2 /\ wr_at rsegs (normalize rsegs m1) (fr + 2464) 8 /\
                wr_at rsegs (normalize rsegs m1) (fr + 2496) 8 /\
                all_dj [(fr + 2256, fr + 2256 + 72); (fr + 2448, fr + 2448 + 2); (fr + 2464, fr + 2464 + 8);
                        (fr + 2496, fr + 2496 + 8); (phi, phi + 50);
                        (spv - REAC_CTRL_IDENTITY_FRAGMENT_K, spv)])
    by (unfold rs_hold in Hphifr, Hphiw, Hfrw, Hfr8; intros _ _ _ _ _; split; [exact RWf0|];
        split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|];
        split; [Z.div_mod_to_equations; lia|];
        split; [apply (R10B.r10b_wr_sub _ _ _ _ _ STf0); lia|];
        split; [apply (R10B.r10b_wr_sub _ _ _ _ _ STf0); lia|];
        split; [apply (R10B.r10b_wr_sub _ _ _ _ _ STf0); lia|];
        destruct Hphifr as [Hd1|Hd1]; destruct Hphiw as [Hd2|Hd2]; destruct Hfrw as [Hd3|Hd3];
        cbn [all_dj dj_from]; repeat split; lia).
  all: assert (P24 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 -> 50 <= nb ->
                addressable (normalize rsegs m1) phi 50) by (intros; exact ADphi0).
  all: assert (P25 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 ->
                addressable (normalize rsegs m1) (fr + 2256) 72 /\ addressable (normalize rsegs m1) (fr + 2448) 2 /\
                addressable (normalize rsegs m1) (fr + 2464) 8 /\ addressable (normalize rsegs m1) (fr + 2496) 8 /\
                app_mem (fr + 2256 + 78) /\
                dj_from RT_LO RT_HI [(fr + 2256, fr + 2256 + 72); (fr + 2448, fr + 2448 + 2);
                                     (fr + 2464, fr + 2464 + 8); (fr + 2496, fr + 2496 + 8)])
    by (intros _ _ _ _ _; split; [exact ADf0|]; split; [exact ADpa0|]; split; [exact ADpp0|];
        split; [exact ADpn0|]; split; [exact Happf|]; cbn [dj_from]; unfold RT_LO, RT_HI; repeat split; lia).
  (* the call, on the normalized memory; the footprint premises are RNG's, memory-independent *)
  all: (eapply ExecF.evtF_mono;
        [ eapply (MNF.evtF_normalize_ro RNG _ _ _ _ _ _ _ _ MI1);
          eapply FRAGF with (m := normalize rsegs m1) (f := fr + 2256) (fr := phi) (len := nb) (pa := fr + 2448)
            (pp := fr + 2464) (pn := fr + 2496) (st := st) (g := g);
          rewrite ?(MState.unsigned_lit spv) by lia;
          first
            [ reflexivity
            | exact Hgl | exact Hstl | exact STw0 | exact Hsp16 | exact (mem_inv_normalize rsegs m1)
            | exact HAC0 | exact HSW0 | exact P17 | exact P18 | exact P24 | exact P25
            | exact HB10 | exact HB20 | exact HB30 | exact HB40 | exact HB50
            | lia
            | (intros; assumption) | (unfold rs_hold in *; lia) ]
        | idtac ]).
  all: intros ms' (s0' & PO & HREL & HROS).
  all: destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                       E & MU0 & WM0 & MI0 & ST0 & FM0 & AC0 & SW0).
  all: subst s0'.
  all: destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
  all: cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in
         ERg, EF, EP, ES, EV, EC, ERo, HMR.
  all: pose proof (R10B.r10b_ms_eta ms' ES) as Ems.
  all: rewrite ERg, EF, EP, EC, EV, ERo in Ems.
  all: lazymatch type of Ems with
       | context [ret_pc (Z_to_bv 64 ?k)] =>
           replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) in Ems
             by (symmetry; apply ret_pc_even; [lia | reflexivity])
       end.
  all: remember (ms_mem ms') as m' eqn:Em'.
  all: clear Em'.
  all: rewrite ?(MState.unsigned_lit spv) in MU0, ST0 by lia.
  all: rewrite Ecls in Ems, MU0, FM0.
  all: do 3 eexists; split; [exact Ems|].
  all: split; [reflexivity|].
  all: exists m1.
  all: do 16 (split; [reflexivity|]).
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact ST|].
  all: split; [exact (munch_rel rsegs _ m1 _ m' m0' REL HMR HROS MU0)|].
  all: split; [exact (wmono_rel rsegs m1 _ m' m0' REL HMR HROS WM0)|].
  all: split; [exact (ro_agree_same rsegs m1 m' MI1 HROS)|].
  all: split; [exact (proj2 (R10B.r10b_rel_stk m' m0' (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv HMR ltac:(lia)
                                ltac:(lia)) ST0)|].
  all: split; [exact STf|].
  all: exact (R10B.r10b_fgmem_rel m' m0' _ _ _ _ _ _ _ HMR FM0).
Qed.

(* R10B.r10b_evt's conclusion as a corollary (evtF_evt of r10b_evt_F at RNG_all; every rng premise by rng_all,
   its bounds from the owner's own premises: 0 <= A and A + 96 <= 2 ^ 64 for the four spill reads, 6283264 <= SHv
   and SHv + 313 <= 2 ^ 64 for the metadata window, HIGHMEM_BEG <= spv - K and spv <= APPMEM_END for the callee
   window, 0 < phi and phi + 50 <= 2 ^ 64 for the record, 6283264 <= fr and fr + FRAME_BYTES <= 2 ^ 64 for the
   fragment cells; the shadow covers by r10b_sh_all). *)
Lemma r10b_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bb pce spv A SHv fr phi nb : Z) (g st : list byte),
    (bb = 6 /\ pce = 0x81708) \/ (bb = 5 /\ pce = 0x817c8) ->
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 SHv -> s7 = Z_to_bv 64 bb ->
    s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 11 -> s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K -> spv <= APPMEM_END -> spv mod 16 = 0 ->
    0 <= A -> A + 96 <= 2 ^ 64 -> 6283264 <= SHv -> SHv + 313 <= 2 ^ 64 ->
    6283264 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> fr mod 8 = 0 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= nb < 2 ^ 64 ->
    (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) ->
    (phi + 50 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) ->
    (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
    app_mem (fr + 2256 + 78) -> length g = 50%nat -> length st = 72%nat ->
    stk rsegs m (SHv + 306) (SHv + 313) -> ro_agree rsegs m ->
    (forall m1, munch [(SHv + 306, SHv + 313)] m m1 -> wmono rsegs m m1 ->
       stk rsegs m1 (SHv + 306) (SHv + 313) -> ro_agree rsegs m1 ->
       bytes_at rsegs m1 (SHv + 306) [Z_to_bv 8 2] -> bytes_at rsegs m1 (SHv + 308) [Z_to_bv 8 0] ->
       bytes_at rsegs m1 (SHv + 312) [Z_to_bv 8 0] -> R10B.r10b_pre m1 A spv fr phi g st) ->
    LE.evt rsegs
      (fun ms => exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs) /\
         R10B.r10b_K sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SHv spv fr nb pce g st R pc' m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bb pce spv A SHv fr phi nb g st Harm Esp Es1 Es3 Es7 Es11 Ea0 Es8 Es2
    HspK HspE Hsp16 HA0 HA96 HSH0 HSHb Hfr0 Hfrb Hfr8 Hphi0 Hphib Hnb Hphifr Hphiw Hfrw Happf Hgl Hstl ST HRO HPRE.
  assert (EK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  apply rs_hide in Harm. apply rs_hide in Hsp16. apply rs_hide in Hfr8.
  apply rs_hide in Hphifr. apply rs_hide in Hphiw. apply rs_hide in Hfrw.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r10b_evt_F ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
           s11 t3 t4 t5 t6 F fc m bb pce spv A SHv fr phi nb g st Harm Esp Es1 Es3 Es7 Es11 Ea0 Es8 Es2
           HspK HspE Hsp16 HA0 HA96 HSH0 HSHb Hfr0 Hfrb Hfr8 Hphi0 Hphib Hnb Hphifr Hphiw Hfrw Happf Hgl Hstl
           ST HRO HPRE).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - exact r10b_bytes_all.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply r10b_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply r10b_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply r10b_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply r10b_sh_all; lia.
  - apply ExecF.rng_all; lia.
  - apply r10b_sh_all; lia.
Qed.

End R10BF.

(* The pin: r10b_evt_of_F's statement is R10B.r10b_evt's, term for term, except the first premise, which names the
   _F contract in place of the plain one; both are checked by name (Seg/F30F.v's form). *)
Example r10b_evt_of_F_verbatim : True.
Proof.
  lazymatch type of R10B.r10b_evt with ?P -> ?A =>
  lazymatch type of r10b_evt_of_F with ?Q -> ?B =>
    constr_eq P OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract;
    constr_eq Q OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.
