(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 741 of its 860 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R2.v, with its module paths, module names, addresses and numbers changed; 241 of its 367 lines of code are new or changed and 734 lines of the source are left out. *)
(* Segment P1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81c58, 0x81ca4], 20
   instructions, cut Inv_B81c58 (v1.9 pc 0x81c58) -> cut Inv_B81ca8 (v1.9 pc 0x81ca8) (plan-asan-ubsan.md section 2,
   row P1; section 4, SHf8 = meta_fill_f8, 0x55144).  rule 24: no function proved (a slot segment).
     0x81c58 beqz a0,81c60   a0 = 0 (the wrapper_strcmp result R21 leaves): taken, so the sink jump 0x81c5c
                             `j 82fa4` is not reached;
     0x81c60 li s2,-8        and the 14 stores 0x81c64 .. 0x81c98 write that byte (0xf8, "variable out of scope")
                             to the frame-shadow bytes S(fr) + 272 .. 276 and S(fr) + 282 .. 290 (s3 = S(fr));
     0x81c9c li a1,187; 0x81ca0 ld a0,8(s1)    the frame-shadow pointer Q = [A + 8] (stored 0x81634);
     0x81ca4 jal meta_fill_f8                  sets the 187 shadow bytes [Q, Q + 187) to 0xf8.
   The range has no instrumented shadow check and no UBSan trap.  The whole write set lies inside the frame's 392
   shadow bytes: the cut gives S(fr) <= Q and Q + 187 <= S(fr) + 328, and the stores are at S(fr) + 272 .. 290.
   p1_evt is the Lib-level run with the call taken on its lib/B contract (asan_set_shadow_c.v, a Section
   hypothesis, never its code); seg_P1 lifts it to the official cuts on the normalized memory (Tac_bp.bp_run, the
   contract needs mem_inv) and moves FRA / ENT by Tac_bp.bp_post with an empty callee window (K = 0: the
   contract's write set is the shadow range alone).  Both cuts carry the spills [A + 56] = fr + 3040,
   [A + 176] = fr + 2688, [A + 208] = fr + 2768, [A + 64] = fr + 3056, CUR g c0 (s7 / s9, kept by the callee), PRO
   and the kind-name table's addressability; the run writes only frame-shadow bytes, below [A, A + 448) and above
   the low shadow.  The poison block has two entries, 0x81c58 (seg_P1) and 0x81c60 (P1', seg_P1_bfc), with one run
   (p1_evt_pc); the bound Q + 187 <= Sfr fr + 328 on both entry cuts keeps the fill [Q, Q + 187) below our[]'s
   shadow byte.  v1.9.0 against the patched image: the pcs move +0x64, Q's slot is [A + 8] (patched [A + 16]) and
   CUR's n - c is in s9 (patched s8). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
Import ListNotations.
Open Scope Z_scope.

Module ASS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.

(* ---- the run from 0x81c60 (P1'): li s2,-8, the 14 shadow stores, li a1,187, ld a0,8(s1), jal meta_fill_f8 ---- *)
Lemma p1_evt_bfc : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs -> -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW.
  unfold ASS.asan_set_shadow_f8_contract, ASS.asan_set_shadow_contract, ASS.ASAN_SET_SHADOW_F8 in SET.
  cbv zeta in SET.
  do 19 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 272) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold RT_HI in HSrt.
  pose proof (munch_refl [(Sh + 272, Sh + 291)] m) as MU1.
  pose proof (munch_refl [(Sh + 272, Sh + 291); (Q, Q + 187)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  bp_sb. bp_sb. bp_sb. bp_sb. bp_sb.
  bp_sb. bp_sb. bp_sb. bp_sb. bp_sb.
  bp_sb. bp_sb. bp_sb. bp_sb.
  step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HRD1 : forall x, Sh + 272 <= x < Sh + 291 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 (Sh + 272) _ x HbC).
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : shadow_rw m1).
  { apply (bp_shadow_rw _ m m1 HSW MU1 WM). intros a Ha.
    destruct (Z_le_gt_dec (Sh + 272) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 291)) as [H2|H2]|].
    - right. exact (HRD1 a ltac:(lia)).
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  (* the 187 shadow bytes [Q, Q + 187) are read + writable: they are shadow bytes of the frame *)
  assert (HstkQ : stk rsegs m1 Q (Q + 187)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Hin : in_shadow a) by (replace a with (Q + (a - Q)) by lia; apply Hshq; lia).
    exact (HSW1 a Hin). }
  destruct (bp_stk_rw _ _ _ HstkQ ltac:(lia)) as (junkQ & RWQ).
  replace (Z.to_nat (Q + 187 - Q)) with 187%nat in RWQ by lia.
  assert (EQ1 : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply MState.unsigned_lit; lia).
  assert (EQ2 : bv_unsigned (Z_to_bv 64 187) = 187) by reflexivity.
  eapply evt_cut.
  { eapply SET with (junk := junkQ).
    all: rewrite ?EQ1, ?EQ2.
    - intros i Hi. apply Hshq. lia.
    - exact RWQ.
    - exact HAC1.
    - exact HMI. }
  intros ms' PO. unfold ASS.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & RW2).
  subst ms'.
  rewrite EQ1, EQ2 in MU2, RW2.
  change (Z.to_nat 187) with 187%nat in RW2.
  assert (HQb : bytes_at rsegs m' Q (repeat (Z_to_bv 8 0xf8) 187)).
  { destruct RW2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (Hsub : sub_fp [(Q, Q + 187)] [(Sh + 272, Sh + 291); (Q, Q + 187)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (RDfin : forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx.
    destruct (Z_le_gt_dec Q x) as [H1|H1]; [destruct (Z_lt_ge_dec x (Q + 187)) as [H2|H2]|].
    - apply (bp_ba_rd m' Q _ x HQb). rewrite repeat_length. lia.
    - destruct (HRD1 x ltac:(lia)) as (bq & Hbq). exists bq.
      unfold mrd in *. rewrite (MU2 (wa x)); [exact Hbq|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
    - destruct (HRD1 x ltac:(lia)) as (bq & Hbq). exists bq.
      unfold mrd in *. rewrite (MU2 (wa x)); [exact Hbq|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x81ca8)) with (Z_to_bv 64 0x81ca8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2) | exact RDfin].
Qed.

(* ---- the run from 0x81c58 (P1): beqz a0,81c60 taken (a0 = 0), then the 0x81c60 run ---- *)
Lemma p1_evt : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c58) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs Hs3 Hs1 -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW.
  step. if_true.
  exact (p1_evt_bfc SET ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
           s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW).
Qed.

(* Both entries of the poison block, 0x81c58 (P1) and 0x81c60 (P1'), reach 0x81ca8 by the same run. *)
Lemma p1_evt_pc : ASS.asan_set_shadow_f8_contract ->
  forall (pc : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    pc = 0x81c58 \/ pc = 0x81c60 ->
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros SET pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs [Hpc | Hpc] Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW; subst pc.
  - exact (p1_evt SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW).
  - exact (p1_evt_bfc SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW).
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

Section P1.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee meta_fill_f8 (SHf8@0x81ca4), taken on its lib/B contract, never on its code. *)
Hypothesis SETF8 : ASS.asan_set_shadow_f8_contract.

(* The poison block from either entry, 0x81c58 (Inv_B81c58) or 0x81c60 (Inv_B81c60, P1'): the run p1_evt_pc to
   0x81ca8. The two official cuts have one body (adopt 10 of a working branch: Q + 187 <= Sfr fr + 328, so the meta_fill_f8
   range [Q, Q + 187) misses our[]'s shadow byte Sfr fr + 328); this lemma takes its conjuncts. *)
Lemma p1_core : forall pc, pc = 0x81c58 \/ pc = 0x81c60 ->
  Hcut B APIf ra (Inv_B81ca8 B APIf ra) ->
  forall g regs mem md fr Q,
    FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md ->
    g_n g < 2 ^ 26 -> OURb g fr mem -> a0v regs 0 -> PRO fr regs mem ->
    spill regs mem 8 Q -> Sfr fr <= Q -> Q + 187 <= Sfr fr + 328 ->
    spill regs mem 56 (fr + 3040) -> spill regs mem 176 (fr + 2688) -> spill regs mem 208 (fr + 2768) ->
    spill regs mem 64 (fr + 3056) -> CUR g (c0 (g_in g)) regs -> addressable mem KNC.KIND_NAME 112 ->
    SR rsegs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros pc Hpc0 Hexit g regs mem md fr Q HFRA HENT Hgn HOUR Ha0 HPRO HQsp HQ1 HQ2 H56 H176 H208 H64 HCUR HKN.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  (* the spills name the spill base A of register 9 *)
  destruct H56 as (A1 & HA1 & Hq56).
  assert (HA1e : A1 = A)
    by (apply (bp_spill_A regs mem 56 (fr + 3040) A A1 HA1 Hq56 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A1.
  destruct HQsp as (A2 & HA2 & Hq8).
  assert (HA2e : A2 = A)
    by (apply (bp_spill_A regs mem 8 Q A A2 HA2 Hq8 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  (* the three record-pointer spills (adopt 6) name the same A *)
  assert (SPA : forall off v, 0 <= off <= 440 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Hoff (A3 & HA3 & Hq).
    assert (HA3e : A3 = A)
      by (apply (bp_spill_A regs mem off v A A3 HA3 Hq Hr9); unfold APPMEM_END in HAPP; lia).
    subst A3. exact Hq. }
  pose proof (SPA 176 (fr + 2688) ltac:(lia) H176) as Hq176.
  pose proof (SPA 208 (fr + 2768) ltac:(lia) H208) as Hq208.
  pose proof (SPA 64 (fr + 3056) ltac:(lia) H64) as Hq64.
  clear H176 H208 H64.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* the frame-shadow bytes of [Q, Q + 187) and of the stores are shadow bytes *)
  assert (Hshq : forall i, 0 <= i < 187 -> in_shadow (Q + i)).
  { intros i Hi. replace (Q + i) with (Sfr fr + (Q - Sfr fr + i)) by lia. apply bp_fsh; [exact Happ' | lia]. }
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  (* the 19 frame-shadow cells the stores hit, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite FRAME_SHADOW_val in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (bp_ba_sub mem (Sfr fr) sh 272 19 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 272) with (Sfr fr + 272) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 19 (skipn 272 sh)) = 19%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 272) (map C1 (firstn 19 (skipn 272 sh)))).
  { apply bp_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 19) with 19.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 272 + i)).
    { replace (Sfr fr + 272 + i) with (Sfr fr + (272 + i)) by lia. apply bp_fsh; [exact Happ' | lia]. }
    exact (proj1 (HSW0 _ Hin)). }
  (* the frame-shadow pointer spilled at [A + 8], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 8) [C8 (Z_to_bv 64 Q)]).
  { apply bp_ro8. unfold q64 in Hq8. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq8). }
  unfold rg in Hr19, Hr9, Ha0.
  unfold a0v, rg in Ha0.
  apply (bp_run regs (Z_to_bv 64 pc) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81ca8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       LF.munch [(Sfr fr + 272, Sfr fr + 291); (Q, Q + 187)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       (forall x, Sfr fr + 272 <= x < Sfr fr + 291 \/ Q <= x < Q + 187 ->
          exists b, mrd rsegs m0' (wa x) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p1_evt_pc SETF8 pc) with (Sh := Sfr fr) (Ab := A) (Q := Q)
        (xs := firstn 19 (skipn 272 sh)); try assumption; try (unfold RT_HI; lia).
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P26' & _ & P23' & P25' & MUq & WMq & RDq).
      exists R, (Z_to_bv 64 0x81ca8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact P23'|]. split; [exact P25'|].
      split; [exact MUq|]. split; [exact WMq | exact RDq].
  - intros R pc' m0' regs'' mem' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K23 & K25 & MU0 & WM0 & RD0)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    assert (RDW : forall x, ~ LF.outside [(Sfr fr + 272, Sfr fr + 291); (Q, Q + 187)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. cbn [LF.outside] in Hx.
      destruct (RD0 x ltac:(lia)) as (b & Hb). exists b.
      rewrite (mrd_rel rsegs mem' m0' _ HRel). exact Hb. }
    assert (HCOV : bp_cover fr (AC.aspZ regs - 0) (AC.aspZ regs)
                     [(Sfr fr + 272, Sfr fr + 291); (Q, Q + 187)]).
    { intros x Hx. cbn [LF.outside] in Hx. lia. }
    assert (HDJ : rt_disjoint [(Sfr fr + 272, Sfr fr + 291); (Q, Q + 187)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    destruct (bp_post B APIf ra empty FF g fr regs regs'' mem mem' md md'
                [(Sfr fr + 272, Sfr fr + 291); (Q, Q + 187)] 0 HFRA HENT ltac:(lia) MU WM Hsame HDJ HCOV
                RDW E2 E3 E4 E8 E9 E19 E26 Hmat) as (HFRA' & HENT').
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the spills, kept: [A, A + 448) is above the frame shadow the run writes *)
    assert (KS : forall off v, 0 <= off <= 440 -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KS 56 (fr + 3040) ltac:(lia) Hq56)|].
    split.
    { (* PRO: its spills are kept, and our[]'s shadow byte Sfr fr + 328 is above both written ranges
         (Q + 187 <= Sfr fr + 328, the local cut's bound) *)
      apply (bp_PRO_keep fr regs regs'' mem mem'); [| | exact HPRO].
      - intros off v Hoff Hs. exact (KS off v Hoff (SPA off v Hoff Hs)).
      - intros HOA. apply (bp_addr_keep _ mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
        rewrite (bp_our_sh fr i Hfrm Hi). cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KS 176 (fr + 2688) ltac:(lia) Hq176)|].
    split; [exact (KS 208 (fr + 2768) ltac:(lia) Hq208)|].
    split; [exact (KS 64 (fr + 3056) ltac:(lia) Hq64)|].
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
      unfold rg. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
    (* the kind-name table's shadow bytes lie in the low shadow, below the frame shadow *)
    apply (bp_addr_keep _ mem mem' KNC.KIND_NAME 112 HKN MU). intros i Hi.
    pose proof (bp_sa_lo (KNC.KIND_NAME + i) ltac:(unfold KNC.KIND_NAME; lia)) as Hk. unfold ASAN_K in Hk.
    cbn [LF.outside]. split; [lia | split; [lia | exact I]].
Qed.

(* S_P1. *)
Lemma seg_P1 : Hcut B APIf ra (Inv_B81ca8 B APIf ra) -> Hcut B APIf ra (Inv_B81c58 B APIf ra).
Proof.
  intros Hexit g c HInv.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & HPRO & (Q & HQsp & HQ1 & HQ2) &
                    H56 & H176 & H208 & H64 & HCUR & HKN).
  subst c. rewrite (proj1 FF).
  exact (p1_core 0x81c58 (or_introl eq_refl) Hexit g regs mem md fr Q HFRA HENT Hgn HOUR Ha0 HPRO HQsp HQ1 HQ2
           H56 H176 H208 H64 HCUR HKN).
Qed.

(* S_P1_bfc: P1's run from the other entry 0x81c60 (P1', reached also from R21's 0x81c0c beqz). *)
Lemma seg_P1_bfc : Hcut B APIf ra (Inv_B81ca8 B APIf ra) -> Hcut B APIf ra (Inv_B81c60 B APIf ra).
Proof.
  intros Hexit g c HInv.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & Ha0 & HPRO & (Q & HQsp & HQ1 & HQ2) &
                    H56 & H176 & H208 & H64 & HCUR & HKN).
  subst c. rewrite (proj1 FF).
  exact (p1_core 0x81c60 (or_intror eq_refl) Hexit g regs mem md fr Q HFRA HENT Hgn HOUR Ha0 HPRO HQsp HQ1 HQ2
           H56 H176 H208 H64 HCUR HKN).
Qed.

End P1.
