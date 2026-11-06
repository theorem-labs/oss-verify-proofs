(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names, addresses and numbers changed; 104 of its 131 lines of code are new or changed and 369 lines of the source are left out. *)
(* Segment P9 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): 0x81c34-0x81c48, 6 instructions
   (v1.8 0x81bb4-0x81bc8, IDENTICAL: every pc +0x80).
     81c34 li s2,-1; 81c38 beq a0,s2,81c40 (taken: a0 = -1 the first ports_parse result; the fall-through 81c3c
     j 82bf4 to the failure exit is not reached); 81c40 li a0,0; 81c44 li a1,0; 81c48 jal reac_ports_parse@0x8765c.
   With p = q = 0 the callee fails (ports_ok 0 0 bs = false): it returns -1 and writes only its 16-byte stack frame
   [sp - 16, sp). Both cuts are SlotInv's: the entry Inv_A81c34 and the exit Inv_A81c4c (the entry of P10; v1.9
   re-anchors it on 0x81c4c `beq a0,s2,81c54`, the first instruction of the pair that replaces v1.8's 0x81bcc
   `bne`; the return address of the call is 0x81c4c in both readings).
   Gap 4 (aslot push 11) and pushes 12 / 13: CUR, PRO, the spill [s1 + 144] = fr + 2688, the 17 addressable bytes
   at fr + 2691, IDBe and FGBe move across the call with P7's stk_call (the run keeps s1, s6, s9). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot P7 P8.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract, a Section Hypothesis (it is proved in reac_ports_parse.v; that proof is not imported). *)
Hypothesis HPP : reac_ports_parse_contract.

Lemma p9_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 (-1) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_PARSE_FRAME <= bv_unsigned sp ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' t3' a1' a2' a3' a4' a5' a6' a7' s2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c4c) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       a1' a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c4c) fc None m' (seg_rom rsegs) /\
         s2' = Z_to_bv 64 (-1) /\
         munch [(bv_unsigned sp - REAC_PORTS_PARSE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c34) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m lo -> HST Hlo.
  step. (* 81c34 li s2,-1 *)
  step. (* 81c38 beq a0,s2,81c40 *)
  if_true.
  step. step. (* 81c40 li a0,0; 81c44 li a1,0 *)
  step. (* 81c48 jal reac_ports_parse *)
  pose proof HPP as HP. unfold reac_ports_parse_contract, REAC_PORTS_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (p := 0) (q := 0) (lo := lo) (bs := repeat (Z_to_bv 8 0) 20).
    all: try reflexivity.
    all: try assumption.
    all: try (intros _ HH; exfalso; apply HH; reflexivity).
    all: lia. }
  intros ms' (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & WM & MIi & ST' & Hif).
  subst ms'.
  rewrite ports_ok_q0 in Hif |- *. cbv iota in Hif |- *.
  replace (ret_pc (Z_to_bv 64 531532)) with (Z_to_bv 64 531532)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  do 12 eexists. exists m'.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hif|]. split; [exact WM | exact ST'].
Qed.

Lemma seg_P9 : Hcut B APIf ra (Inv_A81c4c B APIf ra) -> Hcut B APIf ra (Inv_A81c34 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HOUR & HCUR & HPRO & HSP & HADR & HSP208 & HADF &
    HADI & HIDB & HFGB &
    Ha0 & HXC & HAF).
  subst c. rewrite SEGS.
  destruct (fra_sp B APIf ra g fr [] regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  unfold AC.aspZ in Hspb, Hspm, HaspB, Hhi, Hwinsp.
  apply (p7_run regs (Z_to_bv 64 0x81c34) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81c4c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 18 = Z_to_bv 64 (-1) /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       munch [(AC.aspZ regs - REAC_PORTS_PARSE_FRAME, AC.aspZ regs)] mem mem' /\
       wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_PORTS_PARSE_FRAME) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply p9_evt with (sp := getr regs 2) (lo := bv_unsigned (getr regs 2) - FN_STACK).
      - unfold a0v, rg in Ha0. exact Ha0.
      - exact Hwinsp.
      - unfold REAC_PORTS_PARSE_FRAME, FN_STACK, AF.SLOT_STACK. lia. }
    { intros ms' (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & m' &
        E & Hs2 & MU & WM & ST').
      eexists _, (Z_to_bv 64 0x81c4c), m'. split; [exact E|].
      split; [reflexivity|].
      do 8 (split; [reflexivity|]).
      split; [exact Hs2|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|].
      apply (p7_stk_sub m' (bv_unsigned (getr regs 2) - FN_STACK)); [exact ST'|].
      unfold AC.aspZ, REAC_PORTS_PARSE_FRAME, FN_STACK, AF.SLOT_STACK. lia. }
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K10 & K18 & K22 & K25 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    destruct (stk_call B APIf ra empty FF g fr [] regs regs' mem mem' md md' REAC_PORTS_PARSE_FRAME _ HFRA HENT
      HXC HOUR HCUR HPRO HSP HADR HSP208 HADF HADI HIDB HFGB
      ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_PORTS_PARSE_FRAME; lia) MU WM
      ST'
      ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
      ltac:(rewrite Hreg; exact K8) ltac:(rewrite Hreg; exact K9) ltac:(rewrite Hreg; exact K19)
      ltac:(rewrite Hreg; exact K26) ltac:(rewrite Hreg; exact K22) ltac:(rewrite Hreg; exact K25) Hmat)
      as (HFRA' & HENT' & HXC' & HOUR' & HCUR' & HPRO' & HSP' & HADR' & HSP208' & HADF' & HADI' & HIDB' & HFGB').
    assert (HIexit : Inv_A81c4c B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x81c4c) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|]. split; [exact HOUR'|].
      split; [exact HCUR'|]. split; [exact HPRO'|]. split; [exact HSP'|]. split; [exact HADR'|].
      split; [exact HSP208'|]. split; [exact HADF'|]. split; [exact HADI'|].
      split; [exact HIDB'|].
      split; [exact HFGB'|].
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split; [unfold rg; rewrite Hreg; exact K18|]. split; [exact HXC'|].
      (* round 4: first.sroa.7's 35 bytes stay addressable (the callee writes only its window) *)
      exact (stk_addr_keep B APIf ra g fr [] regs mem mem' md REAC_PORTS_PARSE_FRAME (fr + 2880) 35 HFRA
               ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_PORTS_PARSE_FRAME; lia) MU HAF). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
