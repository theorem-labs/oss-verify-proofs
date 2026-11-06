(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R7tail.v; 127 of its 214 lines of code are new or changed and 1145 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R7tail.v 0481d807aab5 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Callee: asan_set_shadow_f8_contract_F (lib/A/Prog/asan_set_shadow_cF.v, a Theorem Labs lane's
   working branch 1afda39f97b; proved there by asan_set_shadowF.v asan_set_shadow_f8_holds_F).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: r7_tail_evt_of_F_bounded re-derives R7tail.r7_tail_evt at ExecF.RNG_all after the callee premise, with
   ONE bound premise added (below); r7_tail_evt_of_F_bounded_shape checks that it is the source statement plus
   premises only. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) twin of the one run lemma of Seg/R7tail.v (r7_tail_evt :533): the same run (the b = 6,
   n_6 = 0 tail 0x815ec -> 0x8194c -> 0x81990 .. 0x81abc -> 0x81ac8, the 14 frame-shadow stores of 0xf8, and the
   call of meta_fill_f8 at 0x81b0c), with the same post-state predicate, re-stepped with lib.Lib StepF as an
   ExecF.evtF under a universally quantified footprint RNG. The callee __asan_set_shadow_f8 is taken through its
   FOOTPRINT contract asan_set_shadow_f8_contract_F, in the SAME position where R7tail.r7_tail_evt takes the plain
   asan_set_shadow_f8_contract (the R19F / F13F shape), and that contract's own footprint premises are passed
   through unchanged: rng_bytes RNG (a forall-memory form), the image range, the callee's stack window
   [sp - ASAN_SET_SHADOW_K, sp) and the filled shadow range [S3 + 68, S3 + 255).
   The segment's own regions are the ones its own premises name: the four spill cells [A + 112] / [A + 128] /
   [A + 144] / [A + 152], the identity record at IDa, the row words at row + 266 and row + 56, the five shadow
   bytes its instrumented checks read, and the 19 frame-shadow bytes [S3 + 272, S3 + 291) the 14 `sb` write.
   R7tail.v itself is unchanged apart from comment text.

   ONE BOUND PREMISE (the of_F_bounded rule): r7_tail_evt states no bound on sp, so the callee's window premise
   `ExecF.rng RNG (bv_unsigned sp - ASAN_SET_SHADOW_K) ASAN_SET_SHADOW_K` cannot be discharged at RNG_all
   (ExecF.rng_all needs 0 <= lo). The corollary is therefore r7_tail_evt_of_F_bounded, with
   `0 <= bv_unsigned sp - ASAN_SET_SHADOW_K` inserted right after the source premises, and no verbatim pin. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcFrag RcEmit
  RcEmitLib RcSynth RcSynthLib RcLay RcFin RcFinLib RcIdentModel RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
(* The run's own import block of R7tail.v (the one that precedes r7_tail_evt), in its order. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d
  YO09 YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt2_b2 Tac_rt_b2 Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_c asan_set_shadow memset
  reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import RoAdapt.
(* The segment file, and the callee's footprint contract (a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R7tail.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_cF.
(* Last but YK11: StepF's step / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMS (lib.Lib's MState). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* R7tail.r7t_br / r7t_sr / r7t_sb with the evtF goal shape: the helper names the re-run changes, same bodies. *)
Ltac r7tF_br := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by
                (symmetry; first [apply r7t_eqb_refl | apply r7t_zxb_nz; assumption | reflexivity]); cbv iota
            | replace c with false by (symmetry; reflexivity); cbv iota ]
  | _ => idtac end.
Ltac r7tF_st := step; r7tF_br.
Ltac r7tF_sr X := rewrite (LMS.unsigned_lit X) by lia; rewrite rc_shr3.
Ltac r7tF_sb := step;
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 _)) _) => rewrite r7t_le1_m8; mem_after_store
  | _ => idtac end.

Lemma r7_tail_evt_F : asan_set_shadow_f8_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A IDa row S3 : Z) (v128 v144 : word)
         (h2 h36 : byte) (w0 w1 w2 w3 : word) (j1 j2 jsh jfl : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 IDa -> s10 = Z_to_bv 64 2147450880 ->
    s3 = Z_to_bv 64 S3 -> s7 = Z_to_bv 64 6 ->
    0 <= A -> A + 416 <= 2 ^ 47 -> 0 <= IDa -> IDa + 38 <= 2 ^ 47 -> 0 <= row -> row + 296 <= 2 ^ 47 ->
    2147450880 <= S3 -> S3 + 392 <= 2 ^ 47 -> S3 + 392 <= A ->
    (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
    ro_cells rsegs m (A + 112) [C8 (Z_to_bv 64 row)] -> ro_cells rsegs m (A + 128) [C8 v128] ->
    ro_cells rsegs m (A + 144) [C8 v144] -> ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 (S3 + 68))] ->
    ro_cells rsegs m IDa [C2 w0; C1 h2; CB 19 j1; C2 w1; C2 w2; C2 w3; CB 8 j2; C1 h36] ->
    bv_unsigned h2 <> 0 -> bv_unsigned h36 <> 0 ->
    ro_cells rsegs m (row + 266) [C2 w0; C2 w1; C2 w2; C2 w3] ->
    ro_cells rsegs m (row + 56) [C4 (Z_to_bv 64 0)] ->
    ro_cells rsegs m ((row + 266) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 268) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 270) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 272) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 56) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (S3 + 68) [CB 187 jsh] -> rw_cells rsegs m (S3 + 272) [CB 19 jfl] ->
    length jsh = 187%nat -> length jfl = 19%nat ->
    asan_cells m -> mem_inv rsegs m ->
    (* footprint: the segment's own regions, then the callee's (asan_set_shadow_f8_contract_F) *)
    ExecF.rng RNG (A + 112) 8 -> ExecF.rng RNG (A + 128) 8 -> ExecF.rng RNG (A + 144) 8 ->
    ExecF.rng RNG (A + 152) 8 ->
    ExecF.rng RNG IDa 38 ->
    ExecF.rng RNG (row + 266) 8 -> ExecF.rng RNG (row + 56) 4 ->
    ExecF.rng RNG ((row + 266) / 8 + 2147450880) 1 ->
    ExecF.rng RNG ((row + 268) / 8 + 2147450880) 1 ->
    ExecF.rng RNG ((row + 270) / 8 + 2147450880) 1 ->
    ExecF.rng RNG ((row + 272) / 8 + 2147450880) 1 ->
    ExecF.rng RNG ((row + 56) / 8 + 2147450880) 1 ->
    ExecF.rng RNG (S3 + 272) 19 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - ASAN_SET_SHADOW_K) ASAN_SET_SHADOW_K ->
    ExecF.rng RNG (S3 + 68) 187 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 27 = v144 /\
         munch [(S3 + 68, S3 + 255); (S3 + 272, S3 + 291)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (S3 + 68) [CB 187 (repeat (Z_to_bv 8 0xf8) 187)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros SSF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl -> -> -> -> -> -> HA0 HA1 HI0 HI1 HR0 HR1
    HS0 HS1 HSA HSH CA CA128 CA144 CA152 CI Hh2 Hh36 CR CR56 S266 S268 S270 S272 S56 RWsh RWfl Ljsh Ljfl HAC HMI
    R112 R128 R144 R152 RID Rrow Rrow56 Rs266 Rs268 Rs270 Rs272 Rs56 Rsh272 Rbytes Rimg Rwin Rsh68.
  unfold asan_set_shadow_f8_contract_F, asan_set_shadow_contract_F, ASAN_SET_SHADOW_F8 in SSF.
  pose proof (munch_refl [(S3 + 68, S3 + 255); (S3 + 272, S3 + 291)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r7tF_st.                             (* 815ec beqz a0 -> 8194c *)
  r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st.                       (* 8194c .. 8195c -> 81990 *)
  r7tF_st. r7tF_st. r7tF_st.           (* 81990 lbu a0,2(s5) ; 81994 ld s11,144(s1) ; 81998 bnez a0 *)
  r7tF_st. r7tF_st. r7tF_st. r7tF_sr (row + 266). r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st.
  r7tF_st. r7tF_st.                    (* 819cc lbu a0,36(s5) ; 819d0 bnez a0 *)
  r7tF_st. r7tF_st. r7tF_st. r7tF_sr (row + 268). r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st.
  r7tF_st. r7tF_st. r7tF_st. r7tF_sr (row + 270). r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st.
  r7tF_st. r7tF_st. r7tF_st. r7tF_sr (row + 272). r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st. r7tF_st.
  r7tF_st. r7tF_st. r7tF_st. r7tF_sr (row + 56). r7tF_st. r7tF_st. r7tF_st.
  r7tF_st. r7tF_st.                    (* 81a78 lw a0,0(a0) ; 81a7c beqz a0 -> 81ac8 *)
  r7tF_st. do 14 r7tF_sb.              (* 81ac8 li s2,-8 ; the 14 frame-shadow stores *)
  r7tF_st. r7tF_st. r7tF_st.           (* 81b04 li a1,187 ; 81b08 ld a0,152(s1) ; 81b0c jal meta_fill_f8 *)
  eapply ExecF.evtF_cut.
  { eapply SSF with (junk := jsh).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSH.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
      change (Z.to_nat 187) with 187%nat. exact RWsh.
    - eapply fl_asan_cells; [exact HAC | exact MU |]. intros x Hx. unfold RT_LO, RT_HI in Hx.
      cbn. split; [lia | split; [lia | exact Logic.I]].
    - exact HMI.
    - exact Rbytes.
    - exact Rimg.
    - exact Rwin.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Rsh68. }
  intros ms' PO. unfold asan_set_shadow_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2
                  & RW2).
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in MU2, RW2 by lia.
  replace (ret_pc (Z_to_bv 64 0x81b10)) with (Z_to_bv 64 0x81b10)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    intros x Hx. cbn in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact Logic.I]. }
  split; [eapply wmono_trans; [exact WM | exact WM2]|].
  split; [exact MI2|].
  change (Z.to_nat 187) with 187%nat in RW2. exact RW2.
Qed.

(* R7tail.r7_tail_evt's statement after its callee premise, re-derived from r7_tail_evt_F at ExecF.RNG_all, with
   the one bound premise the source does not state (the of_F_bounded rule): the callee's stack window needs
   0 <= bv_unsigned sp - ASAN_SET_SHADOW_K. Every other rng premise is rng_all from the source's own bounds. *)
Lemma r7_tail_evt_of_F_bounded : asan_set_shadow_f8_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A IDa row S3 : Z) (v128 v144 : word)
         (h2 h36 : byte) (w0 w1 w2 w3 : word) (j1 j2 jsh jfl : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 IDa -> s10 = Z_to_bv 64 2147450880 ->
    s3 = Z_to_bv 64 S3 -> s7 = Z_to_bv 64 6 ->
    0 <= A -> A + 416 <= 2 ^ 47 -> 0 <= IDa -> IDa + 38 <= 2 ^ 47 -> 0 <= row -> row + 296 <= 2 ^ 47 ->
    2147450880 <= S3 -> S3 + 392 <= 2 ^ 47 -> S3 + 392 <= A ->
    (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
    ro_cells rsegs m (A + 112) [C8 (Z_to_bv 64 row)] -> ro_cells rsegs m (A + 128) [C8 v128] ->
    ro_cells rsegs m (A + 144) [C8 v144] -> ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 (S3 + 68))] ->
    ro_cells rsegs m IDa [C2 w0; C1 h2; CB 19 j1; C2 w1; C2 w2; C2 w3; CB 8 j2; C1 h36] ->
    bv_unsigned h2 <> 0 -> bv_unsigned h36 <> 0 ->
    ro_cells rsegs m (row + 266) [C2 w0; C2 w1; C2 w2; C2 w3] ->
    ro_cells rsegs m (row + 56) [C4 (Z_to_bv 64 0)] ->
    ro_cells rsegs m ((row + 266) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 268) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 270) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 272) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 56) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (S3 + 68) [CB 187 jsh] -> rw_cells rsegs m (S3 + 272) [CB 19 jfl] ->
    length jsh = 187%nat -> length jfl = 19%nat ->
    asan_cells m -> mem_inv rsegs m ->
    0 <= bv_unsigned sp - ASAN_SET_SHADOW_K ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 27 = v144 /\
         munch [(S3 + 68, S3 + 255); (S3 + 272, S3 + 291)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (S3 + 68) [CB 187 (repeat (Z_to_bv 8 0xf8) 187)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros SSF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl Es1 Ea0 Es5 Es10 Es3 Es7 HA0 HA1 HI0 HI1
    HR0 HR1 HS0 HS1 HSA HSH CA CA128 CA144 CA152 CI Hh2 Hh36 CR CR56 S266 S268 S270 S272 S56 RWsh RWfl
    Ljsh Ljfl HAC HMI Hsp.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (r7_tail_evt_F SSF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl);
    try assumption.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_SET_SHADOW_K in *; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* The shape check of the of_F_bounded rule: r7_tail_evt_of_F_bounded is R7tail.r7_tail_evt's statement (after the
   callee premise, which is the footprint contract here) plus premises only - the added bound is never used to
   weaken anything. *)
Lemma r7_tail_evt_of_F_bounded_shape :
  ltac:(let T := type of R7tail.r7_tail_evt in
        lazymatch T with ?P -> ?A => exact A end) ->
  ltac:(let T := type of r7_tail_evt_of_F_bounded in
        lazymatch T with ?P -> ?A => exact A end).
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl; intros.
  apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl); assumption.
Qed.
