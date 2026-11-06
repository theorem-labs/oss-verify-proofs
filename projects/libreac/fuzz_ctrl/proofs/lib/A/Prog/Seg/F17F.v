(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 176 of its 211 lines of code are new or changed and 361 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/Tac_b5.v, with its module paths and module names changed; 1788 of its 1832 lines of code are new or changed and 167 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F17.v, with its module names changed; 134 of its 217 lines of code are new or changed and 1749 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F17.v blob f83ca6832224 at d65d18383b1 (merged into this
   branch at fb15888292d; Seg/Tac_f17b.v blob 8a2efdcdf106 (the blob this tree had at release c5e779efe8c)).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f17_tail_of_pre_post re-derives F17.f17_tail from the two stretches at ExecF.RNG_all and the PLAIN
   callee contract; f17_tail_of_pre_post_verbatim checks by constr_eq that its type is the type of F17.f17_tail
   after F17's own first premise (Hypothesis HMC : asan_memcpy_c.asan_memcpy_contract, F17.v:486).
   Mechanical re-run, route (a) (lead 22:15Z), SPLIT STRETCHES (a Theorem Labs lane 00:45Z); input to the ported walk only. *)
(* SPLIT at the call __asan_memcpy (0x823d4, return 0x823d8): the callee had no _F of record on this tree then
   (asan_memcpy_contract_F was only a restated Section hypothesis in lib/A/Prog/declaration_ofF.v, reac_ctrl_parseF.v,
   build_dt1_singleF.v, reac_ctrl_identity_fragment_F.v and lib/A/Prog/Seg/R8F.v (both not in this delivery), which names a Theorem Labs lane as its owner).
   - f17_tail_pre_F : 0x823c8 -> the callee ENTRY state (pc = ASAN_MEMCPY, ra = 0x823d8, a0 = fr + 2880,
     a1 = phi + 27, a2 = n). One access: the 8-byte load at A + 32, so one rng premise. No contract premise.
   - f17_tail_post_F : the RETURN block 0x823d8 -> 0x823e8 from a concrete start at the return pc with the
     canonical register map Regs6ss.mkR_of regs. Its premises are the machine-level facts the source script holds
     right after it applies Tac_f17b.f17_mc: the register values it reads, [A+176], the writable spill window, and
     the callee post's existential memory as a universally bound `mem` with its munch / wmono / ro_agree / stk /
     bytes_at facts, each as stated in the source. Two accesses: the two 8-byte stores inside [A+88, A+120) and
     the 8-byte load at A + 176.
   DEVIATION from the spec's post_F template, reported to the lead: the float map and fcsr stay the source's
   binders (Fr, fc) instead of fp_regs / fp_csr. F17.f17_tail quantifies over them, so a start pinned at
   fp_regs / fp_csr would make f17_tail_of_pre_post weaker than F17.f17_tail and the no-weakening pin would fail.
   This is a strengthening of the template (instantiate Fr := fp_regs, fc := fp_csr for the walk); the register
   map is the canonical one the template asks for.
   The normalized-memory step is NOT a problem for the cut: MemNorm's normalize lives entirely inside
   Tac_f17b.f17_mc, whose own statement is a plain Lib.Exec run from the callee entry state to the return state
   over the real memory, so the cut points are states of the source script, not of the normalized run. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot F18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_f17b Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F17.
(* Required, NOT imported at file level: StepF's step / Exec names must not shadow the UL engine's, because
   f17_tail_of_pre_post below states F17.f17_tail's text, whose `evt` and `mkR` are the UL engine's. The two
   stretches live in Module PF, which imports them with module-local visibility. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module AW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW.SmLib.


Module PF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
(* ExecF / StepF open bv_scope; the stretches are stated in Z, as F17.v is. *)
(* The canonical register map, expanded (F20.v mkR_of_expand's text). *)
Lemma f17F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  LF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A concrete register map is its own canonical map. *)
Lemma f17F_mkR_of_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
  Regs6ss.mkR_of (LF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                     x25 x26 x27 x28 x29 x30 x31)
  = LF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31.
Proof. intros. reflexivity. Qed.

Open Scope Z_scope.

(* ---- Stretch 1: 0x823c8 `addi a1,s7,27` ; 0x823cc `ld a0,32(s1)` ; 0x823d0 `mv a2,s9` ;
   0x823d4 `jal __asan_memcpy`, up to the callee entry state. Cut from F17.f17_tail's own script (its first four
   steps and the HR32 read fact). ---- *)
Lemma f17_tail_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi fr n : Z),
  s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 n ->
  bytes_at rsegs m (A + 32) (le8 (Z_to_bv 64 (fr + 2880))) ->
  ExecF.rng RNG (A + 32) 8 ->
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (LF.mkR (Z_to_bv 64 0x823d8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                            (Z_to_bv 64 (fr + 2880)) (Z_to_bv 64 (phi + 27)) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 n) s10 s11 t3 t4 t5 t6)
                         Fr (Z_to_bv 64 ACPY.ASAN_MEMCPY) fc None m (seg_rom rsegs))
    (MS (LF.mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x823c8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi fr n E1 E7 E9 Hq32 G32.
  subst s1 s7 s9.
  assert (HR32 : ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 (fr + 2880)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 32) (le8 (Z_to_bv 64 (fr + 2880))) 0 8 Hq32
        ltac:(rewrite length_le8; cbn; lia)) as H.
    rewrite Z.add_0_r, skipn_O in H.
    rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia). exact H. }
  step. (* 0x823c8: addi a1,s7,27 *)
  step. (* 0x823cc: ld a0,32(s1) *)
  step. (* 0x823d0: mv a2,s9 *)
  step. (* 0x823d4: jal __asan_memcpy *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- Stretch 2: the return block 0x823d8 `addi a0,zero,1` ; 0x823dc `sd a0,104(s1)` ;
   0x823e0 `sd s9,112(s1)` ; 0x823e4 `ld s9,176(s1)`, to 0x823e8. Cut from F17.f17_tail's own script after the
   callee contract: its Hq176c / HwC transports and its HS104 / HS112 / HR176 facts, unchanged. ---- *)
Lemma f17_tail_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s2 s3 s4 s5 s6 s8 s10 s11 : word) (Fr : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (A phi fr n spz lo : Z) (src : list byte),
  getr regs 2 = sp -> getr regs 3 = gp -> getr regs 4 = tp -> getr regs 8 = s0 ->
  getr regs 9 = Z_to_bv 64 A -> getr regs 18 = s2 -> getr regs 19 = s3 -> getr regs 20 = s4 ->
  getr regs 21 = s5 -> getr regs 22 = s6 -> getr regs 23 = Z_to_bv 64 phi -> getr regs 24 = s8 ->
  getr regs 25 = Z_to_bv 64 n -> getr regs 26 = s10 -> getr regs 27 = s11 ->
  bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 64))) ->
  wr_at rsegs m (A + 88) 32 ->
  0 <= A -> A + 184 <= 2 ^ 64 -> 1 <= n <= 22 -> fr + FRAME_BYTES <= A -> spz <= A ->
  LF.munch [(fr + 2880, fr + 2880 + n); (spz - ACPY.ASAN_MEMCPY_K, spz)] m mem ->
  LF.wmono rsegs m mem -> ro_agree rsegs mem -> stk rsegs mem lo spz ->
  bytes_at rsegs mem (fr + 2880) src ->
  ExecF.rng RNG (A + 88) 32 -> ExecF.rng RNG (A + 176) 8 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                       (mc : word -> option byte),
       ms' = MS (LF.mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (fr + 64)) s10 s11 t3' t4' t5' t6')
                Fr (Z_to_bv 64 0x823e8) fc None
                (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                   (wa (A + 112)) (le8 (Z_to_bv 64 n))) (seg_rom rsegs) /\
       LF.munch [(fr + 2880, fr + 2880 + n); (spz - ACPY.ASAN_MEMCPY_K, spz)] m mc /\
       LF.wmono rsegs m mc /\ ro_agree rsegs mc /\ stk rsegs mc lo spz /\ bytes_at rsegs mc (fr + 2880) src)
    (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x823d8) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s2 s3 s4 s5 s6 s8 s10 s11 Fr fc m A phi fr n spz lo src
    E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27
    Hq176 HwA HA0 HAtop Hn HfrA HspA MU WM RO' ST' Bsrc G88 G176.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  rewrite f17F_mkR_of_expand, E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  (* the spill cells stay writable across the call (wmono) and the stores *)
  pose proof (LF.wr_at_transport rsegs m mem (A + 88) 32 HwA WM) as HwC.
  (* [A + 176] is above sp and above the frame, so neither the copy nor the call's scratch touches it *)
  assert (Hq176c : bytes_at rsegs mem (A + 176) (le8 (Z_to_bv 64 (fr + 64)))).
  { eapply fl_bytes; [exact Hq176 | exact MU |].
    rewrite length_le8. intros x Hx. cbn [LF.outside]. split; [lia|]. split; [lia | exact I]. }
  step. (* 0x823d8: addi a0,zero,1 *)
  assert (HS104 : store_ok rsegs mem (wa (A + 104)) 8 = true).
  { replace (A + 104) with (A + 88 + 16) by lia. apply (wr_at_store_ok rsegs mem (A + 88) 32 16 8 HwC); lia. }
  step. (* 0x823dc: sd a0,104(s1) *)
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    assert (HS112 : store_ok rsegs m2 (wa (A + 112)) 8 = true) by
      (replace (A + 112) with (A + 88 + 24) by lia;
       apply (wr_at_store_ok rsegs m2 (A + 88) 32 24 8);
       [ repeat apply wr_at_write; exact HwC | lia | lia ]) end.
  step. (* 0x823e0: sd s9,112(s1) *)
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?m3 _) =>
    assert (HR176 : ov_read_bytes rsegs m3 (wa (A + 176)) 8 = Some (le8 (Z_to_bv 64 (fr + 64)))) by
      (assert (Hb2 : bytes_at rsegs m3 (A + 176) (le8 (Z_to_bv 64 (fr + 64))));
       [ repeat (apply (bytes_at_write_other rsegs);
                 [| lia | rewrite length_le8; lia | rewrite !length_le8; lia]); exact Hq176c
       | pose proof (bytes_at_ov_read rsegs m3 (A + 176) (le8 (Z_to_bv 64 (fr + 64))) 0 8 Hb2
             ltac:(rewrite length_le8; cbn; lia)) as H;
         rewrite Z.add_0_r, skipn_O in H;
         rewrite firstn_all2 in H by (rewrite length_le8; cbn; lia); exact H ]) end.
  step. (* 0x823e4: ld s9,176(s1) *)
  apply ExecF.evtF_done.
  do 16 eexists. exists mem.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact ST' | exact Bsrc].
Qed.

End PF.

Section F17F.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
(* The plain callee contract, as F17.v:486 takes it. *)
Hypothesis HMC : ACPY.asan_memcpy_contract.

(* ---- The two stretches at RNG_all, with the plain contract between them, re-derive F17.f17_tail. ---- *)
Lemma f17_tail_of_pre_post :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word) (Fr : bvmap 5 word) fc (m : word -> option byte) A phi fr n spz lo (src : list byte),
  s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 n -> sp = Z_to_bv 64 spz ->
  bytes_at rsegs m (A + 32) (le8 (Z_to_bv 64 (fr + 2880))) ->
  bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 64))) ->
  bytes_at rsegs m (phi + 27) src -> length src = Z.to_nat n -> 1 <= n <= 22 ->
  addressable m (phi + 27) n -> addressable m (fr + 2880) n ->
  stk rsegs m (fr + 2880) (fr + 2880 + n) ->
  (phi + 27 + n <= fr + 2880 \/ fr + 2880 + n <= phi + 27) ->
  app_mem (phi + 27 + n) -> app_mem (fr + 2880 + n) -> app_mem (phi + 34) -> app_mem (fr + 2887) ->
  (fr + 2880 + n <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= fr + 2880) ->
  (phi + 27 + n <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= phi + 27) ->
  stk rsegs m lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo -> spz <= APPMEM_END ->
  AC.GT <= fr -> 0 <= phi ->
  ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
  0 <= A -> A + 184 <= 2 ^ 64 ->
  wr_at rsegs m (A + 88) 32 -> fr + FRAME_BYTES <= A -> spz <= A ->
  evt rsegs
    (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                       (mc : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (fr + 64)) s10 s11 t3' t4' t5' t6')
                   Fr (Z_to_bv 64 0x823e8) fc None
                   (write_to_mem (write_to_mem mc (wa (A + 104)) (le8 (Z_to_bv 64 1)))
                      (wa (A + 112)) (le8 (Z_to_bv 64 n))) (seg_rom rsegs) /\
       LF.munch [(fr + 2880, fr + 2880 + n); (spz - ACPY.ASAN_MEMCPY_K, spz)] m mc /\
       LF.wmono rsegs m mc /\ ro_agree rsegs mc /\ stk rsegs mc lo spz /\ bytes_at rsegs mc (fr + 2880) src)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x823c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A phi fr n spz lo src E1 E7 E9 Esp Hq32 Hq176 Hsrc Hlen Hn HadS HadD HstD Hdj HeaS HeaD HapS HapD
    HspD HspS HSTK HK HLO HSP HGT Hphi0 HRO HAC HSH HA0 HAtop HwA HfrA HspA.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  (* the whole run in the Lib engine, as F17.f17_tail's script does at the call *)
  apply F17.f17_lib_evt.
  (* stretch 1 at RNG_all *)
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (PF.f17_tail_pre_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A phi fr n E1 E7 E9 Hq32).
    pose proof Hq32 as (B32a & B32b & _). rewrite length_le8 in B32b.
    apply ExecF.rng_all; lia. }
  intros ms' ->.
  (* the call, with the plain contract on normalized memory: F17.f17_tail's own application *)
  eapply LE.evt_cut.
  { eapply (Tac_f17b.f17_mc HMC) with (D := fr + 2880) (S := phi + 27) (N := n) (spz := spz) (lo := lo)
      (src := src);
      [ reflexivity | reflexivity | reflexivity | exact Esp | lia | lia
      | unfold HIGHMEM_BEG in HLO; unfold AC.GT; lia | exact HSP | exact Hn | exact HRO | exact Hsrc | exact Hlen
      | exact HstD | exact Hdj | exact HadS | exact HadD | exact HeaS | exact HeaD
      | replace (phi + 27 + 7) with (phi + 34) by lia; exact HapS
      | replace (fr + 2880 + 7) with (fr + 2887) by lia; exact HapD
      | unfold AsanRT.RT_HI; lia | exact HspD | exact HspS | exact HSTK | exact HK | exact HLO | exact HAC
      | exact HSH ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc
              & E & MU & WM & RO' & ST' & Bsrc).
  subst ms'.
  replace (LM.ret_pc (Z_to_bv 64 533464)) with (Z_to_bv 64 0x823d8)
    by (symmetry; apply LM.ret_pc_even; [clear; lia | reflexivity]).
  (* stretch 2 at RNG_all, at the canonical form of the state the callee returned in *)
  rewrite <- (PF.f17F_mkR_of_mkR (Z_to_bv 64 0x823d8) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
    (Z_to_bv 64 (fr + 2880)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 n)
    s10 s11 t3' t4' t5' t6').
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (PF.f17_tail_post_F ExecF.RNG_all _ mc sp gp tp s0 s2 s3 s4 s5 s6 s8 s10 s11 Fr fc m A phi fr n spz lo src);
    try reflexivity; try assumption.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all;
    (pose proof Hq176 as (B176a & B176b & _); rewrite length_le8 in B176b; lia).
Qed.

(* The pin, inside the section so that both types are read against the same {fx} / {LS} / {rc} and against the
   same plain-contract premise (HMC is still a hypothesis here, so f17_tail_of_pre_post's type is the statement
   itself): f17_tail_of_pre_post states F17.f17_tail's text after F17's own first premise, the plain memcpy
   contract (F17.v:486, Hypothesis HMC), term for term (constr_eq: syntactic, not up to conversion). *)
Example f17_tail_of_pre_post_verbatim : True.
Proof.
  lazymatch type of F17.f17_tail with ?P -> ?A =>
    constr_eq P ACPY.asan_memcpy_contract;
    let B := type of f17_tail_of_pre_post in constr_eq A B
  end.
  exact I.
Qed.

End F17F.
