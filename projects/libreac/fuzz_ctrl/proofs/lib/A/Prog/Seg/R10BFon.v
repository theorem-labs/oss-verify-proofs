(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names and addresses changed; 1437 of its 1585 lines of code are new or changed and 1354 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R10B.v, with its module names changed; 93 of its 249 lines of code are new or changed and 1429 lines of the source are left out. *)
(* lib/A/Prog/Seg/R10BFon.v -- route (C): the NARROWED twin of a Theorem Labs lane's R10BF.r10b_evt_F (Seg/R10BF.v:115), the
   footprint run of both fragment arms (b = 6 and b = 5) of segment R10 of fuzz_ctrl image A (libreac v1.9.0), from
   0x81680 to the arm's exit pc.  Written by a Theorem Labs lane (a Theorem Labs lane's stage lane for seg_R10) under the Seg *F.v twin
   rule (a Theorem Labs lane 12:52Z, agreed): an ADDITIVE beside-file; this file edits no line of R10BF.v, which since the BASE below changed only by a proof-speed edit (the Local rs_hold / rs_hide pair, used in r10b_evt_F and r10b_evt_of_F) and in comment text.
   proves no function (kind: segment lemma).

   BASE: a Theorem Labs lane's fold blob of R10BF.v at a working branch 4bae33fdf54, bef08c47c5a, which is also the
   route (C) walk's blob (a working branch 1899bed1aee): no diff.

   WHY A TWIN: R10BF.r10b_evt_F's argument-load premise HPRE ends in R10B.r10b_pre (Seg/R10B.v:661), whose conjunct
   `shadow_rw m1` is the universal form; the route (C) walk's cut gives only ctl_rt_C (the cut's own shadow and the image's), so
   a stage cannot feed it.  The run itself neither reads nor stores a shadow byte through that premise: its three
   metadata stores (0x81684 .. 0x8168c) go through the premise `stk m (SHv + 306) (SHv + 313)`, and the premise is
   spent only on the callee, reac_ctrl_identity_fragment, whose contract takes it (via the normalized memory).  So
   the twin narrows it to the callee's own region, at this call's values (f = fr + 2256, fr = phi, len = nb,
   pa / pp / pn = fr + 2448 / 2464 / 2496):
     shadow_rw m1  ->  A.ShadowRwOn.shadow_rw_on
                         (FGC.reac_ctrl_identity_fragment_shadow_R (fr + 2256) phi nb (fr + 2448) (fr + 2464)
                            (fr + 2496) st g) m1
   (r10b_pre_on below: R10B.r10b_pre with that one conjunct changed), and takes the callee in its _on form,
   FGC.reac_ctrl_identity_fragment_contract_F_on (lib/A/Prog/reac_ctrl_identity_fragment_c.v 0359af7161a (the blob this tree had at release c5e779efe8c),
   a Theorem Labs lane, LANDED row 56 (a working note, not in this delivery)), in the place of R10BF's FRAGF.  Every other premise, the post (R10B.r10b_K, which
   names no shadow fact) and the proof script are R10BF.r10b_evt_F's; the script's two changed lines are the
   normalized shadow premise (A.ShadowRwOnT.shadow_rw_on_rel in the place of R10B.r10b_rel_sw) and the callee
   hypothesis's name.  The three store tactics are R10BF's own (r10bF_sb / r10bF_newb / r10bF_keepb, Required). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 B3Rtm R10B.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
(* R10BF's store tactics (r10bF_sb, r10bF_newb, r10bF_keepb) and its premise list. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R10BF.
(* Last: StepF's step / mem_after_store (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* R10B.r10b_pre (Seg/R10B.v:661) with its universal `shadow_rw m1` narrowed to the fragment's region at this call. *)
Definition r10b_pre_on (m1 : word -> option byte) (A spv fr phi nb : Z) (g st : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 48)) 8 = Some (le8 (Z_to_bv 64 (fr + 2256))) /\
  ov_read_bytes rsegs m1 (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 (fr + 2448))) /\
  ov_read_bytes rsegs m1 (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 (fr + 2464))) /\
  ov_read_bytes rsegs m1 (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 (fr + 2496))) /\
  stk rsegs m1 (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
  bytes_at rsegs m1 phi g /\ addressable m1 phi 50 /\
  rw_cells rsegs m1 (fr + 2256) [CB 72 st] /\ addressable m1 (fr + 2256) 72 /\
  stk rsegs m1 (fr + 2256) (fr + 2504) /\
  addressable m1 (fr + 2448) 2 /\ addressable m1 (fr + 2464) 8 /\ addressable m1 (fr + 2496) 8 /\
  asan_cells m1 /\
  A.ShadowRwOn.shadow_rw_on
    (FGC.reac_ctrl_identity_fragment_shadow_R (fr + 2256) phi nb (fr + 2448) (fr + 2464) (fr + 2496) st g) m1 /\
  bytes_at rsegs m1 REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m1 REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m1 GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m1 (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m1 (CF + 255) [Z_to_bv 8 1].

Section R10BFon.
(* The callee's narrowed footprint contract, in the place of R10BF's FRAGF. *)
Hypothesis FRAGF_on : FGC.reac_ctrl_identity_fragment_contract_F_on.

Lemma r10b_evt_F_on :
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
       bytes_at rsegs m1 (SHv + 312) [Z_to_bv 8 0] -> r10b_pre_on m1 A spv fr phi nb g st) ->
    (* the run's own regions: the three metadata stores and the four argument loads *)
    ExecF.rng RNG (SHv + 306) 7 ->
    ExecF.rng RNG (A + 48) 8 -> ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 80) 8 ->
    ExecF.rng RNG (A + 72) 8 ->
    (* the callee's regions (reac_ctrl_identity_fragment_contract_F_on's rng premises, at this call's values) *)
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
  unfold FGC.reac_ctrl_identity_fragment_contract_F_on in FRAGF_on.
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
  all: assert (HSW0 : A.ShadowRwOn.shadow_rw_on
                        (FGC.reac_ctrl_identity_fragment_shadow_R (fr + 2256) phi nb (fr + 2448) (fr + 2464)
                           (fr + 2496) st g) (normalize rsegs m1))
    by exact (A.ShadowRwOnT.shadow_rw_on_rel _ m1 _ REL HSW).
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
    by (intros _ _ _ _ _; split; [exact RWf0|];
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
          eapply FRAGF_on with (m := normalize rsegs m1) (f := fr + 2256) (fr := phi) (len := nb) (pa := fr + 2448)
            (pp := fr + 2464) (pn := fr + 2496) (st := st) (g := g);
          rewrite ?(lib.Lib.MState.unsigned_lit spv) by lia;
          first
            [ reflexivity
            | exact Hgl | exact Hstl | exact STw0 | exact Hsp16 | exact (mem_inv_normalize rsegs m1)
            | exact HAC0 | exact HSW0 | exact P17 | exact P18 | exact P24 | exact P25
            | exact HB10 | exact HB20 | exact HB30 | exact HB40 | exact HB50
            | lia
            | (intros; assumption) ]
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
  all: rewrite ?(lib.Lib.MState.unsigned_lit spv) in MU0, ST0 by lia.
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

End R10BFon.
