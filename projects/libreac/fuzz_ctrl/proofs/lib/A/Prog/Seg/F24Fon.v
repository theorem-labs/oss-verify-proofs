(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths and module names changed; 914 of its 1020 lines of code are new or changed and 1096 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F24.v; 35 of its 125 lines of code are new or changed and 930 lines of the source are left out. *)
(* lib/A/Prog/Seg/F24Fon.v -- route (C) twin of Seg/F24F.v's (not in this delivery) f24_evt_F (a Theorem Labs lane 12:52Z twin rule: an ADDITIVE
   beside-file; Seg/F24F.v (not in this delivery) stays byte-identical).  Writer: a Theorem Labs lane, for glue stage seg_F24.
   proves no function (kind: segment lemma).

   BASE: Seg/F24F.v (not in this delivery) at a Theorem Labs lane's fold a working branch 4bae33fdf54 (blob e6648db89d5), not the
   blob 2ea56089851 of a working branch: the two differ only in the fold's full qualification of the twin-library lemmas
   (A.Tk.UL.MState / Mem / Frame), which this file keeps.

   THE CHANGE, and only it: f24_evt_F's premise `shadow_rw m` is REMOVED, and its callee premise
   reac_ports_parse_contract_F becomes reac_ports_parse_contract_F_on (LANDED.md (a working note, not in this delivery): a Theorem Labs lane d4f70537e6f, proof
   a Theorem Labs lane 4038362e590 reac_ports_parse_F_holds_on).  Why removed, not narrowed: the run 0x825c8 -> 0x825d4 is two register
   moves and the call; it reads and stores no shadow byte itself, and its only use of `shadow_rw m` in f24_evt_F was
   to feed the callee's premise, which the _on contract drops (the callee reads its shadow bytes from `addressable`
   and the runtime cells).  The post is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts F24.
(* Last: StepF's step / if_false / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Restore YK11.getr, as F24.v does. *)
Import YK11.
Local Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.

(* ---- f24_evt_F with no shadow premise, on the callee's route (C) contract. ---- *)
Lemma f24_evt_F_on :
  forall (RNG : ExecF.footprint),
    reac_ports_parse_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi fr lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> s4 = Z_to_bv 64 (fr + 128) ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> fr mod 32 = 0 ->
    0 <= spv < 2 ^ 64 ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    wr_at rsegs m (fr + 128) 12 ->
    (fr + 140 <= phi + 18 \/ phi + 38 <= fr + 128) ->
    (phi + 38 <= spv - 16 \/ spv <= phi + 18) ->
    (fr + 140 <= spv - 16 \/ spv <= fr + 128) ->
    asan_cells m -> addressable m (phi + 18) 20 -> addressable m (fr + 128) 12 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv); (fr + 128, fr + 140)] x) ->
    ExecF.rng RNG (spv - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (phi + 18) 20 ->
    ExecF.rng RNG (shadow_addr (phi + 18)) (shadow_addr (phi + 18 + 19) - shadow_addr (phi + 18) + 1) ->
    ExecF.rng RNG (fr + 128) 12 ->
    ExecF.rng RNG (shadow_addr (fr + 128)) (shadow_addr (fr + 128 + 11) - shadow_addr (fr + 128) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' t0' t1' t2' t3' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if RL.decl bs then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  Fr (Z_to_bv 64 0x825d4) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv); (fr + 128, fr + 140)] m m' /\ wmono rsegs m m' /\
         (RL.decl bs = true ->
            u32 m' (fr + 128) (4 * RL.n_in bs) /\ u32 m' (fr + 132) (4 * RL.n_out bs) /\
            u32 m' (fr + 136) (16 * RL.bt bs 7)) /\
         (RL.decl bs = false -> munch [(spv - 16, spv)] m m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825c8) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros RNG PP ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi fr lo bs -> -> -> Hphi1 Hphi2 Hfr1 Hfr2 Hfr32 Hspv Hstk Hlo Hlen Hbs Hwr Hdj Hdjp Hdjq
    HAC HADp HADq HOUT RFR RGOT RCK RP20 RSHp RQ12 RSHq.
  pose proof (munch_refl [(spv - 16, spv); (fr + 128, fr + 140)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  step. step. step.
  eapply ExecF.evtF_cut.
  { eapply PP with (p := phi + 18) (q := fr + 128) (bs := bs) (lo := lo) (RNG := RNG).
    - first [reflexivity | f_equal; lia].
    - first [reflexivity | f_equal; lia].
    - lia.
    - lia.
    - rewrite Hspu. exact Hstk.
    - rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME. lia.
    - intros _ _. split; [exact Hlen | exact Hbs].
    - intros _ _. split; [Z.div_mod_to_equations; lia|].
      split; [exact Hwr|]. split; [lia|].
      rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME. split; lia.
    - intros _ _. split; [exact HAC|]. split; [exact HADp | exact HADq].
    - intros _ _ x Hx. rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME.
      replace (fr + 128 + 12) with (fr + 140) by lia. exact (HOUT x Hx).
    - rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME. exact RFR.
    - intros _ _. split; [exact RGOT|]. split; [exact RCK|]. split; [exact RP20|].
      split; [exact RSHp|]. split; [exact RQ12 | exact RSHq]. }
  intros ms' (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & Hpost).
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x825d4)
        by (symmetry; first [ rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_fold;
          apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RL.ports_ok (phi + 18) (fr + 128) bs = RL.decl bs)
    by (apply b7_ports_ok; lia).
  rewrite Eok in Hpost |- *.
  apply ExecF.evtF_done.
  destruct Hpost as (WMc & _ & STc & Hbr).
  rewrite Hspu in Hbr.
  revert Hbr. destruct (RL.decl bs) eqn:Ed; intros Hbr.
  - destruct Hbr as (Q0 & Q4 & Q8 & MUc).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split.
    { eapply munch_weaken; [|exact MUc]. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.sub_fp.
      cbn [outside].
      intros x (Hx1 & Hx2 & _). unfold REAC_PORTS_PARSE_FRAME.
      split; [lia|]. split; [lia | exact I]. }
    split; [exact WMc|].
    split.
    { intros _. unfold u32. split; [exact Q0|]. split.
      - replace (fr + 132) with (fr + 128 + 4) by lia. exact Q4.
      - replace (fr + 136) with (fr + 128 + 8) by lia. exact Q8. }
    intros E; discriminate E.
  - eexists _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split.
    { eapply munch_weaken; [|exact Hbr]. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.sub_fp.
      cbn [outside].
      intros x (Hx1 & _). unfold REAC_PORTS_PARSE_FRAME. split; [lia | exact I]. }
    split; [exact WMc|].
    split; [intros E; discriminate E|].
    intros _. eapply munch_weaken; [|exact Hbr].
      unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.sub_fp. cbn [outside].
    intros x (Hx1 & _). unfold REAC_PORTS_PARSE_FRAME. split; [lia | exact I].
Qed.
