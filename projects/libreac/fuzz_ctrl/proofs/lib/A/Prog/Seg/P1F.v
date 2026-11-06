(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module names, addresses and numbers changed; 893 of its 1109 lines of code are new or changed and 180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P1.v; 333 of its 498 lines of code are new or changed and 944 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P1.v blob 783a7f55d96e at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives P1.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of P1.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the run lemmas of Seg/P1.v (segment P1, 0x81ac0 .. 0x81b10).
   P1.v has five run lemmas (statement concludes evt): p1_beqz (:260), p1_evt_on (:279), p1_evt (:369), p1_evt_ro_on (:525), p1_evt_ro (:578).
   Only p1_beqz is re-run here.
   BLOCKED: __asan_set_shadow_f8 has no _F contract of record. p1_evt (P1.v:369) and p1_evt_ro (P1.v:578) take
   asan_set_shadow_f8_contract (lib/A/Prog/asan_set_shadow_c.v) as their first premise, and the spec of record
   (segF-v19-spec.md (a working note, not in this delivery): memcpy / memset / set_shadow_* / memchr / strcmp) keeps such a
   run plain. They are left plain in P1.v; their statements are the source's, and their proofs now apply P1.v's p1_evt_on / p1_evt_ro_on.
   p1_beqz is the one step 0x81ac0 `beqz a0,0x81ac8` with a0 = 0. It makes no data access (instruction fetch is not
   an access), so p1_beqz_F appends NO rng premise: the statement is p1_beqz's with (RNG : ExecF.footprint) first and
   ExecF.evtF rsegs RNG in place of evt rsegs. P1.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 33 of its code lines changed or removed, 161 added. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import P1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
(* Last: StepF's step / if_true / if_false (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* ExecF / StepF re-open bv_scope on Import; this file's arithmetic is Z, as in P1.v. *)
Open Scope Z_scope.

(* The old engine's evt, named so that p1_beqz_of_F states P1.p1_beqz's text in a file where StepF is imported. *)
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- p1_beqz (P1.v:157): the beqz at 0x81ac0 with a0 = 0, one step to 0x81ac8, registers and memory unchanged.
   No data access, so no rng premise. ---- *)
Lemma p1_beqz_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ->.
  step. try if_true.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* P1.p1_beqz's statement as a corollary of p1_beqz_F at ExecF.RNG_all (no rng premise to discharge). *)
Lemma p1_beqz_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6) F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E.
  eapply ExecF.evtF_evt, (p1_beqz_F ExecF.RNG_all); exact E.
Qed.

(* The pin: p1_beqz_of_F's statement is P1.p1_beqz's, term for term (constr_eq: syntactic, not up to conversion). *)
Lemma p1_beqz_of_F_verbatim : True.
Proof. let A := type of P1.p1_beqz in let B := type of p1_beqz_of_F in constr_eq A B; exact I. Qed.

(* ================================================================================================================
   SPLIT STRETCHES (spec segF-v19-spec.md (a working note, not in this delivery), a Theorem Labs lane 00:45Z; shape fixed by a Theorem Labs lane 00:48Z) for P1.p1_evt
   (P1.v:369), whose only callee is __asan_set_shadow_f8: `jal` at 0x81b0c, entry ASAN_SET_SHADOW_F8 = 0x55008,
   return pc 0x81b10.  That routine has no _F contract of record, so the glue cuts at the call:
     p1_evt_pre_F   0x81ac8 -> the callee entry state (pc = 0x55008, ra = 0x81b10), no contract premise;
     p1_evt_post_F  a universally quantified start at the return pc 0x81b10 (zero instructions: the source run
                    ends there), premises = the machine-level facts the source script holds right after it
                    applies the contract;
     p1_evt_of_pre_post  the two stretches at ExecF.RNG_all plus the PLAIN contract, re-deriving P1.p1_evt.
   Both stretches are cut from P1.v's own script; no new reasoning.  P1.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 33 of its code lines changed or removed, 161 added.
   ================================================================================================================ *)

(* P1.v's p1_sb (P1.v:135) with the evtF goal head: one frame-shadow store `sb s2,K(s3)` (s3 = Sh), store_ok from
   the invariant p1_J, one step, the invariant for the written memory, which is then named.  Only the goal head
   changes; p1_J_store_ok / p1_J_store are P1.v's and are engine-independent. *)
Ltac p1F_sb K :=
  lazymatch goal with
  | HJ : p1_J ?m0 ?Sh ?mc, HSH : forall i, 0 <= i < 392 -> in_shadow (?Sh + i)
    |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mc (wa (Sh + K)) 1 = true)
        by exact (p1_J_store_ok m0 Sh mc (Sh + K) HJ (HSH K ltac:(lia)));
      step;
      lazymatch goal with
      | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?aa ?bb) _) =>
          let HJ' := fresh "HJ" in
          assert (HJ' : p1_J m0 Sh (write_to_mem mc aa bb))
            by (apply (p1_J_store m0 Sh mc (Sh + K) bb HJ);
                [ lia | exact (HSH K ltac:(lia))
                | first [ reflexivity | apply length_le1 | apply length_Z_to_le_bytes ] ]);
          try clear HS; clear HJ;
          let m' := fresh "mc" in
          set (m' := write_to_mem mc aa bb) in *; clearbody m'
      end
  end.

(* ---- Stretch 1: 0x81ac8 -> the callee entry 0x55008 (ra = 0x81b10).  The 14 one-byte frame-shadow stores all
   lie in [Sh, Sh + 392), the window the source premise `forall i, 0 <= i < 392 -> in_shadow (Sh + i)` names; the
   one load is the 8-byte spill the source premise `bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q))` names.  So the
   two rng premises are exactly those two regions. ---- *)
Lemma p1_evt_pre_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    ExecF.rng RNG Sh 392 ->
    ExecF.rng RNG (A + 152) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' s2' a0' a1' : word) (mc : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 ASAN_SET_SHADOW_F8) fc None mc (seg_rom rsegs) /\
         ra' = Z_to_bv 64 0x81b10 /\ bv_unsigned a0' = Q /\ bv_unsigned a1' = 187 /\ p1_J m Sh mc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q -> -> HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI RSH RSP.
  pose proof (in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  pose proof (p1_J_init m Sh HSW HMI) as HJ.
  (* li s2,-8 *)
  step.
  (* the 14 frame-shadow stores *)
  p1F_sb 285. p1F_sb 286. p1F_sb 287. p1F_sb 288. p1F_sb 276. p1F_sb 282. p1F_sb 283. p1F_sb 284.
  p1F_sb 289. p1F_sb 290. p1F_sb 272. p1F_sb 273. p1F_sb 274. p1F_sb 275.
  (* li a1,187 *)
  step.
  (* ld a0,152(s1): the spill is outside [Sh, Sh + 328), so it is kept *)
  lazymatch goal with
  | HJc : p1_J m Sh ?mc |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HR : ov_read_bytes rsegs mc (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 Q)));
      [ destruct HJc as (MUj & _ & _ & _);
        pose proof (bytes_at_transport rsegs [(Sh, Sh + 328)] m mc (A + 152) _ HSP MUj
                      ltac:(rewrite length_le8; exact HSEP)) as Hb;
        assert (HC : cells_at rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)])
          by (split; [split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]);
        pose proof (cells_at_read rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)] 0%nat (C8 (Z_to_bv 64 Q)) HC eq_refl)
          as E;
        cbn [csize cbytes Z.of_nat] in E; rewrite Z.add_0_r in E; exact E
      | ]
  end.
  step.
  clear HR.
  (* jal 0x55008: ra := 0x81b10 *)
  step.
  apply ExecF.evtF_done.
  lazymatch goal with
  | HJc : p1_J m Sh ?mc |- _ => do 4 eexists; exists mc; split; [reflexivity|]
  end.
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
    reflexivity | vm_compute; reflexivity]|].
  split; [first [vm_compute;
    reflexivity | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
    reflexivity]|].
  assumption.
Qed.

(* ---- Stretch 2: the return pc 0x81b10, where the source run ends, so the stretch takes no step.  Its premises
   are the machine-level facts P1.v's script holds right after `eapply SET`: the four conjuncts of p1_J at the call
   (munch / wmono / shadow_rw / mem_inv of the memory mc the 14 stores left), and the four of the callee post
   (munch / wmono / mem_inv / rw_cells of m'), with the two range bounds the final munch_weaken uses.  The callee
   post's existential memory is the universally bound m'.  No rng premise: no access. ---- *)
Lemma p1_evt_post_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m mc m' : word -> option byte) (Sh Q : Z) (bs : list byte),
    Sh <= Q -> Q + 187 <= Sh + 328 ->
    munch [(Sh, Sh + 328)] m mc -> wmono rsegs m mc -> shadow_rw mc -> mem_inv rsegs mc ->
    munch [(Q, Q + 187)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' Q [CB (Z.to_nat 187) bs] ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m'' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m'' /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\ shadow_rw m'')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mc m' Sh Q bs HQ1 HQ2 MUc WMc HSWc HMIc MU WM MI' RW.
  apply ExecF.evtF_done.
  do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MUc).
    apply (munch_weaken [(Q, Q + 187)]); [|exact MU].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WMc WM)|].
  split; [exact MI'|].
  exact (p1_shadow_rw_call _ m' Q 187 _ HSWc MU WM RW ltac:(lia)).
Qed.

(* ---- The two stretches at ExecF.RNG_all, joined by the PLAIN callee contract, re-derive P1.p1_evt.  The joining
   steps are P1.v's own: p1_rw_of_shadow for the callee's destination cell, asan_cells_kept for its asan_cells
   premise, and ret_pc_even for the return pc. ---- *)
Lemma p1_evt_of_pre_post : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI.
  unfold asan_set_shadow_f8_contract, asan_set_shadow_contract in SET. cbv zeta in SET.
  pose proof (in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  eapply evt_cut.
  { (* the spill's own bytes_at premise bounds [A + 152, A + 160): the source's premise, no new one *)
    pose proof HSP as HBnd. apply bytes_at_bound in HBnd. rewrite length_le8 in HBnd.
    eapply ExecF.evtF_evt.
    eapply (p1_evt_pre_F ExecF.RNG_all);
      [ exact E1 | exact E3 | exact HA | exact HQ1 | exact HQ2 | exact HSH | exact HSP | exact HSEP
      | exact HDRT | exact HAC | exact HSW | exact HMI
      | apply ExecF.rng_all; lia | apply ExecF.rng_all; lia ]. }
  intros ms' (ra' & s2' & a0' & a1' & mc & -> & Era & Ea0 & Ea1 & HJ).
  pose proof HJ as (MUc & WMc & HSWc & HMIc).
  assert (HQi : forall i, 0 <= i < Z.of_nat (Z.to_nat 187) -> in_shadow (Q + i))
    by (intros i Hi; replace (Q + i) with (Sh + (Q - Sh + i)) by lia; apply HSH; lia).
  destruct (p1_rw_of_shadow mc Q (Z.to_nat 187) HSWc HQi ltac:(lia) ltac:(lia)) as (junk & RWj).
  eapply evt_cut.
  { eapply SET with (junk := junk).
    - rewrite Ea0, Ea1. intros i Hi. replace (Q + i) with (Sh + (Q - Sh + i)) by lia. apply HSH. lia.
    - rewrite Ea0, Ea1. exact RWj.
    - exact (asan_cells_kept [(Sh, Sh + 328)] m mc HAC MUc HDRT).
    - exact HMIc. }
  intros ms'' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
               E & MU & WM & MI' & RW).
  subst ms''.
  rewrite Ea0, Ea1 in MU, RW.
  replace (ret_pc ra') with (Z_to_bv 64 0x81b10)
    by (rewrite Era; symmetry; apply ret_pc_even; [lia | reflexivity]).
  exact (ExecF.evtF_evt rsegs ExecF.RNG_all _ _
           (p1_evt_post_F ExecF.RNG_all ra' sp gp tp u0 u1 u2 s0 s1 a0' ua1 ua2 ua3 ua4 ua5 ua6 ua7 s2' s3 s4 s5
              s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m mc m' Sh Q _
              HQ1 HQ2 MUc WMc HSWc HMIc MU WM MI' RW)).
Qed.

(* The pin (the no-weakening check): p1_evt_of_pre_post's statement is P1.p1_evt's, term for term. *)
Lemma p1_evt_of_pre_post_verbatim : True.
Proof. let A := type of P1.p1_evt in let B := type of p1_evt_of_pre_post in constr_eq A B; exact I. Qed.

(* ================================================================================================================
   Route (C) twins (a Theorem Labs lane 09:20Z; frozen form a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery); R = the shadow bytes the run reads
   and stores through its shadow_rw premise, a Theorem Labs lane 10:33Z), on P1.v's own _on pieces (a Theorem Labs lane 89bc67ea2ac: p1_J_on,
   p1_J_init_on, p1_J_on_store_ok, p1_J_on_store, p1_rw_of_shadow_on, p1_shadow_rw_call_on, p1_evt_shadow_R,
   p1_evt_ro_shadow_R). The old stretches above are unchanged. The run reads no shadow byte (no shadow check between
   0x81ac8 and 0x81b10; __asan_set_shadow_f8's contract takes its destination as rw_cells and has no shadow_rw
   premise):
   - p1_evt_pre_F_on: R = the 14 frame-shadow store targets Sh + 272 .. 276 and Sh + 282 .. 290 (store_ok needs
     each present and writable); its post p1_J m Sh mc becomes p1_J_on m Sh mc (the POST form).
   - p1_evt_post_F_on: zero instructions, no shadow byte read or stored: the `shadow_rw mc` premise is DROPPED; the
     p1_J conjunct it was becomes p1_J_on's keep conjunct, and the post takes the POST form.
   - p1_evt_of_pre_post_on: R = P1.p1_evt_shadow_R Sh Q = the 14 store targets (stretch 1) and the callee's
     destination [Q, Q + 187), which p1_rw_of_shadow_on reads and needs writable to build the contract's rw_cells.
   ================================================================================================================ *)

(* The 14 frame-shadow store targets of stretch 1. *)
Definition p1_evt_pre_F_shadow_R (Sh : Z) : Z -> Prop :=
  fun a => Sh + 272 <= a < Sh + 277 \/ Sh + 282 <= a < Sh + 291.

(* p1F_sb on p1_J_on: store_ok from the run's region (P1.p1_J_on_store_ok), one step, p1_J_on for the written
   memory (P1.p1_J_on_store), which is then named. *)
Ltac p1F_sb_on K :=
  lazymatch goal with
  | HJ : p1_J_on ?m0 ?Sh ?mc, HSW : A.ShadowRwOn.shadow_rw_on (p1_evt_pre_F_shadow_R ?Sh) ?m0,
    HSH : forall i, 0 <= i < 392 -> in_shadow (?Sh + i)
    |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mc (wa (Sh + K)) 1 = true)
        by exact (p1_J_on_store_ok _ m0 Sh mc (Sh + K) HJ HSW
                    ltac:(unfold p1_evt_pre_F_shadow_R; first [left; lia | right; lia]) (HSH K ltac:(lia)));
      step;
      lazymatch goal with
      | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?aa ?bb) _) =>
          let HJ' := fresh "HJ" in
          assert (HJ' : p1_J_on m0 Sh (write_to_mem mc aa bb))
            by (apply (p1_J_on_store m0 Sh mc (Sh + K) bb HJ);
                [ lia | exact (HSH K ltac:(lia))
                | first [ reflexivity | apply length_le1 | apply length_Z_to_le_bytes ] | exact HS ]);
          try clear HS; clear HJ;
          let m' := fresh "mc" in
          set (m' := write_to_mem mc aa bb) in *; clearbody m'
      end
  end.

Lemma p1_evt_pre_F_on :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p1_evt_pre_F_shadow_R Sh) m -> mem_inv rsegs m ->
    ExecF.rng RNG Sh 392 ->
    ExecF.rng RNG (A + 152) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' s2' a0' a1' : word) (mc : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 ASAN_SET_SHADOW_F8) fc None mc (seg_rom rsegs) /\
         ra' = Z_to_bv 64 0x81b10 /\ bv_unsigned a0' = Q /\ bv_unsigned a1' = 187 /\ p1_J_on m Sh mc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q -> -> HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI RSH RSP.
  pose proof (in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  pose proof (p1_J_init_on m Sh HMI) as HJ.
  (* li s2,-8 *)
  step.
  (* the 14 frame-shadow stores *)
  p1F_sb_on 285. p1F_sb_on 286. p1F_sb_on 287. p1F_sb_on 288. p1F_sb_on 276. p1F_sb_on 282. p1F_sb_on 283.
  p1F_sb_on 284. p1F_sb_on 289. p1F_sb_on 290. p1F_sb_on 272. p1F_sb_on 273. p1F_sb_on 274. p1F_sb_on 275.
  (* li a1,187 *)
  step.
  (* ld a0,152(s1): the spill is outside [Sh, Sh + 328), so it is kept *)
  lazymatch goal with
  | HJc : p1_J_on m Sh ?mc |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HR : ov_read_bytes rsegs mc (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 Q)));
      [ destruct HJc as (MUj & _ & _ & _);
        pose proof (bytes_at_transport rsegs [(Sh, Sh + 328)] m mc (A + 152) _ HSP MUj
                      ltac:(rewrite length_le8; exact HSEP)) as Hb;
        assert (HC : cells_at rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)])
          by (split; [split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]);
        pose proof (cells_at_read rsegs mc (A + 152) [C8 (Z_to_bv 64 Q)] 0%nat (C8 (Z_to_bv 64 Q)) HC eq_refl)
          as E;
        cbn [csize cbytes Z.of_nat] in E; rewrite Z.add_0_r in E; exact E
      | ]
  end.
  step.
  clear HR.
  (* jal 0x55008: ra := 0x81b10 *)
  step.
  apply ExecF.evtF_done.
  lazymatch goal with
  | HJc : p1_J_on m Sh ?mc |- _ => do 4 eexists; exists mc; split; [reflexivity|]
  end.
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
    reflexivity | vm_compute; reflexivity]|].
  split; [first [vm_compute;
    reflexivity | rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia;
    reflexivity]|].
  assumption.
Qed.

Lemma p1_evt_post_F_on :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m mc m' : word -> option byte) (Sh Q : Z) (bs : list byte),
    Sh <= Q -> Q + 187 <= Sh + 328 ->
    munch [(Sh, Sh + 328)] m mc -> wmono rsegs m mc ->
    (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P mc) -> mem_inv rsegs mc ->
    munch [(Q, Q + 187)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' Q [CB (Z.to_nat 187) bs] ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m'' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m'' /\ wmono rsegs m m'' /\ mem_inv rsegs m'' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m''))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m mc m' Sh Q bs HQ1 HQ2 MUc WMc KPc HMIc MU WM MI' RW.
  apply ExecF.evtF_done.
  do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MUc).
    apply (munch_weaken [(Q, Q + 187)]); [|exact MU].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WMc WM)|].
  split; [exact MI'|].
  intros P HP. exact (p1_shadow_rw_call_on _ m' Q 187 _ MU WM RW ltac:(lia) P (KPc P HP)).
Qed.

Lemma p1_evt_of_pre_post_on : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p1_evt_shadow_R Sh Q) m -> mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HMI.
  unfold asan_set_shadow_f8_contract, asan_set_shadow_contract in SET. cbv zeta in SET.
  pose proof (in_shadow_range _ (HSH 0 ltac:(lia))) as HS0. rewrite Z.add_0_r in HS0.
  pose proof (in_shadow_range _ (HSH 391 ltac:(lia))) as HS391.
  assert (HSW1 : A.ShadowRwOn.shadow_rw_on (p1_evt_pre_F_shadow_R Sh) m).
  { apply (A.ShadowRwOn.shadow_rw_on_mono (p1_evt_shadow_R Sh Q)); [|exact HSW].
    intros x Hx. unfold p1_evt_pre_F_shadow_R in Hx. unfold p1_evt_shadow_R.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; left; exact Hx]. }
  eapply evt_cut.
  { (* the spill's own bytes_at premise bounds [A + 152, A + 160): the source's premise, no new one *)
    pose proof HSP as HBnd. apply bytes_at_bound in HBnd. rewrite length_le8 in HBnd.
    eapply ExecF.evtF_evt.
    eapply (p1_evt_pre_F_on ExecF.RNG_all);
      [ exact E1 | exact E3 | exact HA | exact HQ1 | exact HQ2 | exact HSH | exact HSP | exact HSEP
      | exact HDRT | exact HAC | exact HSW1 | exact HMI
      | apply ExecF.rng_all; lia | apply ExecF.rng_all; lia ]. }
  intros ms' (ra' & s2' & a0' & a1' & mc & -> & Era & Ea0 & Ea1 & HJ).
  pose proof HJ as (MUc & WMc & KPc & HMIc).
  assert (HQi : forall i, 0 <= i < Z.of_nat (Z.to_nat 187) -> in_shadow (Q + i))
    by (intros i Hi; replace (Q + i) with (Sh + (Q - Sh + i)) by lia; apply HSH; lia).
  assert (HSWq : A.ShadowRwOn.shadow_rw_on (p1_rw_of_shadow_shadow_R Q (Z.to_nat 187)) mc).
  { apply KPc. apply (A.ShadowRwOn.shadow_rw_on_mono (p1_evt_shadow_R Sh Q)); [|exact HSW].
    intros x Hx. unfold p1_evt_shadow_R. right; right; exact Hx. }
  destruct (p1_rw_of_shadow_on mc Q (Z.to_nat 187) HSWq HQi ltac:(lia) ltac:(lia)) as (junk & RWj).
  eapply evt_cut.
  { eapply SET with (junk := junk).
    - rewrite Ea0, Ea1. intros i Hi. replace (Q + i) with (Sh + (Q - Sh + i)) by lia. apply HSH. lia.
    - rewrite Ea0, Ea1. exact RWj.
    - exact (asan_cells_kept [(Sh, Sh + 328)] m mc HAC MUc HDRT).
    - exact HMIc. }
  intros ms'' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
               E & MU & WM & MI' & RW).
  subst ms''.
  rewrite Ea0, Ea1 in MU, RW.
  replace (ret_pc ra') with (Z_to_bv 64 0x81b10)
    by (rewrite Era; symmetry; apply ret_pc_even; [lia | reflexivity]).
  exact (ExecF.evtF_evt rsegs ExecF.RNG_all _ _
           (p1_evt_post_F_on ExecF.RNG_all ra' sp gp tp u0 u1 u2 s0 s1 a0' ua1 ua2 ua3 ua4 ua5 ua6 ua7 s2' s3 s4 s5
              s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m mc m' Sh Q _
              HQ1 HQ2 MUc WMc KPc HMIc MU WM MI' RW)).
Qed.

(* ---- p1_evt_ro (P1.v:383) is p1_evt on the normalized memory: its script applies p1_evt WHOLE under
   MemNorm.evt_normalize, and states no machine-level fact at the call, so it has no pre / post stretch of its own
   (the callee contract cannot be applied on the real memory, which carries no mem_inv - that is why p1_evt_ro
   exists).  What it does have is item 3: its own script, with p1_evt replaced by p1_evt_of_pre_post, re-derives it
   from the SAME two stretches plus the plain contract.  P1.v's imports from :259 are repeated here, in its order,
   because p1_evt_ro lives after them (Section Pre, Context {fx : FPState}, YK11's getr). ---- *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Section PreRo.
Context {fx : FPState}.

Lemma p1_evt_ro_of_pre_post : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (p1_evt_of_pre_post SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc (MemNorm.normalize rsegs m) A Sh Q E1 E3 HA HQ1 HQ2 HSH).
    + exact (proj1 (MemNorm.bytes_at_rel rsegs m _ _ _ REL) HSP).
    + exact HSEP.
    + exact HDRT.
    + exact (p1_cells_norm m _ REL HAC).
    + exact (p1_shadow_rw_norm m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MU0 & WM0 & _ & SW0) &
      MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    exact (p1_shadow_rw_back ms m0' Hmem SW0).
Qed.

(* Route (C) twin of p1_evt_ro_of_pre_post: p1_evt_of_pre_post_on on the normalized memory, its region R =
   P1.p1_evt_ro_shadow_R Sh Q (= p1_evt_shadow_R; normalize keeps every shadow byte) moved forward by
   A.ShadowRwOnT.shadow_rw_on_rel and each kept region carried back by A.ShadowRwOnT.shadow_rw_on_of_rel (in place
   of the transports P1.p1_shadow_rw_norm / p1_shadow_rw_back). *)
Lemma p1_evt_ro_of_pre_post_on : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Sh Q : Z),
    s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sh ->
    0 <= A < 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 328 ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 Q)) ->
    disjoint_from [(Sh, Sh + 328)] (A + 152) 8 ->
    disjoint_from [(Sh, Sh + 328)] RT_LO (RT_HI - RT_LO) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p1_evt_ro_shadow_R Sh Q) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(Sh, Sh + 328)] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\
         (forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Sh Q E1 E3 HA HQ1 HQ2 HSH HSP HSEP HDRT HAC HSW HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  - eapply MemNorm.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    apply (p1_evt_of_pre_post_on SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (MemNorm.normalize rsegs m) A Sh Q E1 E3 HA HQ1 HQ2 HSH).
    + exact (proj1 (MemNorm.bytes_at_rel rsegs m _ _ _ REL) HSP).
    + exact HSEP.
    + exact HDRT.
    + exact (p1_cells_norm m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
  - intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MU0 & WM0 & _ & SW0) &
      MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    intros P HP.
    exact (A.ShadowRwOnT.shadow_rw_on_of_rel P ms m0' Hmem (SW0 P (A.ShadowRwOnT.shadow_rw_on_rel P m _ REL HP))).
Qed.

End PreRo.

(* The pin: p1_evt_ro_of_pre_post's statement is P1.p1_evt_ro's, term for term. *)
Lemma p1_evt_ro_of_pre_post_verbatim : True.
Proof. let A := type of P1.p1_evt_ro in let B := type of p1_evt_ro_of_pre_post in constr_eq A B; exact I. Qed.
