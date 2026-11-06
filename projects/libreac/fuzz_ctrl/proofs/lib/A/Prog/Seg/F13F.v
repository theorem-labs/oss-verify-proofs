(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its module paths, module names, addresses and numbers changed; 599 of its 664 lines of code are new or changed and 799 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F13.v 151fb000dc56 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F13.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F13.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/F13.v's three run lemmas (segment F13 = 0x82138 -> 0x82154, the call of
   reac_ctrl_identity_fragment at 0x82150):
   - f13_evt_F: F13.f13_evt (:757) as an ExecF.evtF under a footprint RNG. The segment's own accesses are the
     three spill loads [A+256] / [A+264] / [A+272], which the lemma's own premise
     `rw_cells rsegs m (A + 256) [C8 pa; C8 pn; C8 pp]` names as the 24 bytes [A+256, A+280): one rng premise.
     The callee enters through its footprint contract reac_ctrl_identity_fragment_contract_F
     (lib/A/Prog/reac_ctrl_identity_fragment_c.v) in the place of F13.f13_evt's plain contract premise; the
     callee's own rng premises are that contract's, passed through unchanged (rng_bytes, the image range
     [IMG_LO, IMG_HI), the callee window [sp - K, sp) with the 8-aligned shadow WORD span of that window
     (sh_word_rng, which holds the shadow of __asan_memcpy's frame), and the guarded buffer / shadow covers of
     frg, f, pa, pp, pn).
   - f13_evt_ro_F: F13.f13_evt_ro (:838), the same run on the memory the cut carries (ro_agree in place of
     mem_inv): f13_evt_F on the normalized memory, moved back by MemNormF.evtF_normalize_ro, exactly as
     F13.f13_evt_ro uses MemNorm.evt_normalize.
   F13.sl_run_lib (:736) is NOT re-run: it concludes SR, not evt, so it is out of the spec's scope (a Theorem Labs lane,
   2026-10-28); it stays plain and the ported walk reaches it through the twins above.
   F13.v itself is unchanged apart from comment text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes ExecF_all.
Import ListNotations.
(* As in F13.v: YK11 last among the term-level names (its seg_rom / getr). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* ---- The run 0x82138 -> 0x82150 (the call) -> 0x82154 under a footprint RNG. The callee contract premise is
   the footprint one, in the place of F13.f13_evt's plain one. ---- *)
Lemma f13_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract_F ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the segment's own access: the three spill loads inside [A + 256, A + 280) *)
    ExecF.rng RNG (A + 256) 24 ->
    (* the callee's regions (reac_ctrl_identity_fragment_contract_F's rng premises), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> ExecF.rng RNG frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       ExecF.rng RNG (shadow_addr frg / 8 * 8) (shadow_addr (frg + 49) / 8 * 8 + 8 - shadow_addr frg / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG f 72) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 71) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pa 2) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pp 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 7) / 8 * 8 + 8 - shadow_addr pp / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pn 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 7) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG -> -> -> -> Hfb Hfrgb Hlenb Hpab Hppb Hpnb
    Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond MI AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5
    G256 Gby Gimg Gstk Gstks Gfrg Gfrgs Gf Gfs Gpa Gpas Gpp Gpps Gpn Gpns.
  do 7 step.
  eapply ExecF.evtF_cut.
  { unfold reac_ctrl_identity_fragment_contract_F, REAC_CTRL_IDENTITY_FRAGMENT in HFRAG.
    eapply HFRAG with (RNG := RNG) (f := f) (fr := frg) (len := len) (pa := pa) (pp := pp) (pn := pn)
      (st := st) (g := gfrag).
    all: try assumption.
    all: try reflexivity. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & FGM & AC' & SW').
  subst ms2.
  replace (ret_pc (Z_to_bv 64 532820)) with (Z_to_bv 64 532820)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply ExecF.evtF_done.
  exists (Z_to_bv 64 532820), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact FGM|]. split; [exact AC' | exact SW'].
Qed.

(* F13.f13_evt's conclusion under the footprint contract: f13_evt_F at ExecF.RNG_all (rng_bytes RNG_all holds
   outright; each rng premise by ExecF.rng_all, its bounds from the lemma's own premises). *)
Lemma f13_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract_F ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    0 <= f < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2 Hfb Hfrgb Hlenb Hpab Hppb Hpnb
    Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond MI AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5.
  pose proof (rw_cells_bound rsegs m (A + 256)
    [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] Hc256) as HB256.
  cbn [cells_size csize Nat.add] in HB256.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f13_evt_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8
           s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2
           Hfb Hfrgb Hlenb Hpab Hppb Hpnb Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond MI AC0 SW HHM HAE Haddrfrg Hcond2
           HB1 HB2 HB3 HB4 HB5).
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - intros H1 H2 H3 H4 H5 H6. destruct (Haddrfrg H1 H2 H3 H4 H5 H6) as (Q0 & Q1 & Q2 & _).
    unfold APPMEM_END in Q2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5 H6. destruct (Haddrfrg H1 H2 H3 H4 H5 H6) as (Q0 & Q1 & Q2 & _).
    unfold APPMEM_END in Q2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qf as (F0 & F1 & F2 & _). unfold APPMEM_END in F2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qf as (F0 & F1 & F2 & _). unfold APPMEM_END in F2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qa as (A0 & A1 & A2 & _). unfold APPMEM_END in A2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qa as (A0 & A1 & A2 & _). unfold APPMEM_END in A2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qp as (P0 & P1 & P2 & _). unfold APPMEM_END in P2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qp as (P0 & P1 & P2 & _). unfold APPMEM_END in P2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qn as (N0 & N1 & N2 & _). unfold APPMEM_END in N2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. destruct (Hcond2 H1 H2 H3 H4 H5) as (Qf & Qa & Qp & Qn & _).
    destruct Qn as (N0 & N1 & N2 & _). unfold APPMEM_END in N2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- The same run on the memory the cut carries (ro_agree, not mem_inv): f13_evt_F on the normalized memory,
   moved back by MemNormF.evtF_normalize_ro, as F13.f13_evt_ro does with MemNorm.evt_normalize. ---- *)
Lemma f13_evt_ro_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract_F ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    6283264 <= f -> f + 72 < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    6283264 <= pa -> pa + 2 < 2 ^ 64 -> 6283264 <= pp -> pp + 8 < 2 ^ 64 ->
    6283264 <= pn -> pn + 8 < 2 ^ 64 -> 6283264 <= A -> A + 312 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 256) 24 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> ExecF.rng RNG frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       ExecF.rng RNG (shadow_addr frg / 8 * 8) (shadow_addr (frg + 49) / 8 * 8 + 8 - shadow_addr frg / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG f 72) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 71) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pa 2) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pp 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 7) / 8 * 8 + 8 - shadow_addr pp / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pn 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 7) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2 Hflo Hfhi Hfrgb Hlenb Hpalo Hpahi Hpplo Hpphi
    Hpnlo Hpnhi HAlo HAhi Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2
    HB1 HB2 HB3 HB4 HB5
    G256 Gby Gimg Gstk Gstks Gfrg Gfrgs Gf Gfs Gpa Gpas Gpp Gpps Gpn Gpns.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hsplo : 6283264 <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold HIGHMEM_BEG in HHM; lia).
  assert (Hsphi : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in HAE; lia).
  assert (Hro256 : forall i, 0 <= i < Z.of_nat (cells_size
              [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]) ->
            ro_addr rsegs (wa (A + 256 + i)) = false).
  { intros i Hi.
    change (Z.of_nat (cells_size [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]))
      with 24 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrof72 : forall i, 0 <= i < Z.of_nat (cells_size [CB 72 st]) ->
            ro_addr rsegs (wa (f + i)) = false).
  { intros i Hi. change (Z.of_nat (cells_size [CB 72 st])) with 72 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrostk : forall x, bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < bv_unsigned sp ->
            ro_addr rsegs (wa x) = false)
    by (intros x Hx; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropa : forall i, 0 <= i < 2 -> ro_addr rsegs (wa (pa + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropp : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pp + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropn : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pn + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  pose proof (f13_evt_F RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11
    t3 t4 t5 t6 Fr fc (normalize rsegs m) A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2
    ltac:(lia) Hfrgb Hlenb ltac:(lia) ltac:(lia) ltac:(lia)
    (RoAdapt.rel_rw_norm m _ (A + 256) _ REL Hro256 Hc256)
    Hsp16
    (RoAdapt.rel_stk_norm m _ _ _ REL Hrostk Hstk)
    Lg Lst
    ltac:(intros H1 H2 H3 H4 H5 H6; exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) (Hfrg H1 H2 H3 H4 H5 H6)))
    ltac:(intros H1 H2 H3 H4 H5;
          destruct (Hcond H1 H2 H3 H4 H5) as (Hrw & Ha2 & Ha8 & Ha8' & Hw2 & Hw8 & Hw8' & Hdj);
          split; [exact (RoAdapt.rel_rw_norm m _ f _ REL Hrof72 Hrw)|];
          split; [exact Ha2|]; split; [exact Ha8|]; split; [exact Ha8'|];
          split; [exact (wr_at_norm rsegs m _ pa 2 REL Hw2 Hropa)|];
          split; [exact (wr_at_norm rsegs m _ pp 8 REL Hw8 Hropp)|];
          split; [exact (wr_at_norm rsegs m _ pn 8 REL Hw8' Hropn)|];
          exact Hdj)
    (mem_inv_normalize rsegs m) (RoAdapt.rel_ac_norm m _ REL AC0) (RoAdapt.rel_sw_norm m _ REL SW)
    HHM HAE
    ltac:(intros H1 H2 H3 H4 H5 H6; exact (RoAdapt.rel_addr_norm m _ _ _ REL (Haddrfrg H1 H2 H3 H4 H5 H6)))
    ltac:(intros H1 H2 H3 H4 H5; destruct (Hcond2 H1 H2 H3 H4 H5) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6);
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q1)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q2)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q3)|];
          split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q4)|];
          split; [exact Q5 | exact Q6])
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB1) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB2)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB3) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB4)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB5)
    G256 Gby Gimg Gstk Gstks Gfrg Gfrgs Gf Gfs Gpa Gpas Gpp Gpps Gpn Gpns) as HC.
  pose proof (MNF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & FGM & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (RoAdapt.rel_stk_back memX m0' _ _ Hmr ST')|].
  split; [exact (F13.fg_mem_back f pa pp pn st gfrag _ memX m0' Hmr FGM)|].
  split; [exact (RoAdapt.rel_ac_back memX m0' Hmr AC') | exact (RoAdapt.rel_sw_back memX m0' Hmr SW')].
Qed.

(* F13.f13_evt_ro's conclusion under the footprint contract, by f13_evt_ro_F at ExecF.RNG_all. *)
Lemma f13_evt_ro_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract_F ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    6283264 <= f -> f + 72 < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    6283264 <= pa -> pa + 2 < 2 ^ 64 -> 6283264 <= pp -> pp + 8 < 2 ^ 64 ->
    6283264 <= pn -> pn + 8 < 2 ^ 64 -> 6283264 <= A -> A + 312 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2 Hflo Hfhi Hfrgb Hlenb Hpalo Hpahi Hpplo Hpphi
    Hpnlo Hpnhi HAlo HAhi Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2
    HB1 HB2 HB3 HB4 HB5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f13_evt_ro_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8
           s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2
           Hflo Hfhi Hfrgb Hlenb Hpalo Hpahi Hpplo Hpphi Hpnlo Hpnhi HAlo HAhi Hc256 Hsp16 Hstk Lg Lst Hfrg
           Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5).
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold REAC_CTRL_IDENTITY_FRAGMENT_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - intros H1 H2 H3 H4 H5 H6. destruct (Haddrfrg H1 H2 H3 H4 H5 H6) as (Q0 & Q1 & Q2 & _).
    unfold APPMEM_END in Q2. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5 H6. destruct (Haddrfrg H1 H2 H3 H4 H5 H6) as (Q0 & Q1 & Q2 & _).
    unfold APPMEM_END in Q2. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all; lia.
  - intros H1 H2 H3 H4 H5. apply ExecF.rng_all;
      unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* ---- The pins: each *_of_F states F13's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion). The two run corollaries differ from F13's lemmas only in the callee-contract premise, which
   names the _F contract in place of the plain one; both premises are checked by name too. ---- *)
Example f13_evt_of_F_verbatim : True.
Proof.
  assert (pin : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11
                        t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                       (A f frg len pa pp pn : Z) (st gfrag : list byte), True).
  { intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
      Fr fc m A f frg len pa pp pn st gfrag.
    lazymatch type of (F13.f13_evt ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8
                         s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag) with
    | ?P -> ?X =>
      lazymatch type of (f13_evt_of_F ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8
                           s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag) with
      | ?Q -> ?Y =>
        constr_eq P reac_ctrl_identity_fragment_contract;
        constr_eq Q reac_ctrl_identity_fragment_contract_F;
        constr_eq X Y
      end
    end.
    exact I. }
  exact I.
Qed.

Example f13_evt_ro_of_F_verbatim : True.
Proof.
  assert (pin : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11
                        t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                       (A f frg len pa pp pn : Z) (st gfrag : list byte), True).
  { intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
      Fr fc m A f frg len pa pp pn st gfrag.
    lazymatch type of (F13.f13_evt_ro ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8
                         s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag) with
    | ?P -> ?X =>
      lazymatch type of (f13_evt_ro_of_F ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v
                           s8 s9v s10 s11 t3 t4 t5 t6 Fr fc m A f frg len pa pp pn st gfrag) with
      | ?Q -> ?Y =>
        constr_eq P reac_ctrl_identity_fragment_contract;
        constr_eq Q reac_ctrl_identity_fragment_contract_F;
        constr_eq X Y
      end
    end.
    exact I. }
  exact I.
Qed.

(* ================= Route (C) twin (a Theorem Labs lane; a Theorem Labs lane 13:31Z: ACtlG/F13's L3 switch applies
   f13_evt_ro_F_on, and no other lemma of this file) =================
   f13_evt_ro_F_on is f13_evt_ro_F with three changes, every other premise and conjunct unchanged:
   - the callee premise is reac_ctrl_identity_fragment_contract_F_on (lib/A/Prog/reac_ctrl_identity_fragment_c.v), in
     the place of reac_ctrl_identity_fragment_contract_F;
   - `shadow_rw m` becomes `A.ShadowRwOn.shadow_rw_on (f13_evt_ro_shadow_R f frg len pa pp pn st gfrag) m`;
   - the post's `shadow_rw m'` becomes `forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'`.
   f13_evt_ro_F, f13_evt_F and the rest of this file are unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.

(* The shadow bytes f13_evt_ro_F_on reads or stores through its shadow premise. HOW R IS DERIVED. The run's own
   instructions [0x82138, 0x82150) (f13_evt_F's `do 7 step`) are the three spill loads [A+256] / [A+264] / [A+272]
   and register moves: their one own rng row, F13F.rng.tsv:20, is [A+256, A+280), application memory, so they read
   and store no shadow byte. The jal at 0x82150 enters reac_ctrl_identity_fragment_contract_F_on with
   (f, fr, len, pa, pp, pn, st, g) := (f, frg, len, pa, pp, pn, st, gfrag), and that contract's shadow premise is
   shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f frg len pa pp pn st gfrag). The move to the normalized memory
   (A.ShadowRwOnT.shadow_rw_on_normalize) and the move back (A.ShadowRwOnT.shadow_rw_on_of_rel) keep the region.
   So R is the callee's R at the call, and nothing else. The rows F13F.rng.tsv:25-33 (the guarded shadow covers of
   frg, f, pa, pp, pn, which WORKLIST's measured f13_evt_ro_shadow_R lists) are the callee's FOOTPRINT premises,
   which f13_evt_ro_F_on keeps unchanged; they are not the region of its shadow_rw premise. *)
Definition f13_evt_ro_shadow_R (f frg len pa pp pn : Z) (st gfrag : list byte) : Z -> Prop :=
  reac_ctrl_identity_fragment_shadow_R f frg len pa pp pn st gfrag.

(* f13_evt_ro_F under the callee's _F_on contract. Same script: the run 0x82138 -> 0x82154 is f13_evt_F's steps on
   the normalized memory (stated in the assert HC, the post's shadow conjunct the callee's transport), moved back by
   MemNormF.evtF_normalize_ro; RoAdapt.rel_sw_norm / rel_sw_back become A.ShadowRwOnT.shadow_rw_on_normalize /
   shadow_rw_on_of_rel. *)
Lemma f13_evt_ro_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A f frg len pa pp pn : Z) (st gfrag : list byte),
    reac_ctrl_identity_fragment_contract_F_on ->
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 f -> s7v = Z_to_bv 64 frg -> s2v = Z_to_bv 64 len ->
    6283264 <= f -> f + 72 < 2 ^ 64 -> 0 <= frg < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    6283264 <= pa -> pa + 2 < 2 ^ 64 -> 6283264 <= pp -> pp + 8 < 2 ^ 64 ->
    6283264 <= pn -> pn + 8 < 2 ^ 64 -> 6283264 <= A -> A + 312 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 256) [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)] ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length gfrag = 50%nat -> length st = 72%nat ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m frg gfrag) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    ro_agree rsegs m -> asan_cells m ->
    A.ShadowRwOn.shadow_rw_on (f13_evt_ro_shadow_R f frg len pa pp pn st gfrag) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 256) 24 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> ExecF.rng RNG frg 50) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       ExecF.rng RNG (shadow_addr frg / 8 * 8) (shadow_addr (frg + 49) / 8 * 8 + 8 - shadow_addr frg / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG f 72) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 71) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pa 2) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pp 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 7) / 8 * 8 + 8 - shadow_addr pp / 8 * 8)) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> ExecF.rng RNG pn 8) ->
    (f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       ExecF.rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 7) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m'
         /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A f frg len pa pp pn st gfrag HFRAG E1 E9 E7 E2 Hflo Hfhi Hfrgb Hlenb Hpalo Hpahi Hpplo Hpphi
    Hpnlo Hpnhi HAlo HAhi Hc256 Hsp16 Hstk Lg Lst Hfrg Hcond HRO AC0 SW HHM HAE Haddrfrg Hcond2
    HB1 HB2 HB3 HB4 HB5
    G256 Gby Gimg Gstk Gstks Gfrg Gfrgs Gf Gfs Gpa Gpas Gpp Gpps Gpn Gpns.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hsplo : 6283264 <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K)
    by (unfold HIGHMEM_BEG in HHM; lia).
  assert (Hsphi : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in HAE; lia).
  assert (Hro256 : forall i, 0 <= i < Z.of_nat (cells_size
              [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]) ->
            ro_addr rsegs (wa (A + 256 + i)) = false).
  { intros i Hi.
    change (Z.of_nat (cells_size [C8 (Z_to_bv 64 pa); C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp)]))
      with 24 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrof72 : forall i, 0 <= i < Z.of_nat (cells_size [CB 72 st]) ->
            ro_addr rsegs (wa (f + i)) = false).
  { intros i Hi. change (Z.of_nat (cells_size [CB 72 st])) with 72 in Hi.
    apply RoAdapt.ro_addr_false_hi. lia. }
  assert (Hrostk : forall x, bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < bv_unsigned sp ->
            ro_addr rsegs (wa x) = false)
    by (intros x Hx; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropa : forall i, 0 <= i < 2 -> ro_addr rsegs (wa (pa + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropp : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pp + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  assert (Hropn : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (pn + i)) = false)
    by (intros i Hi; apply RoAdapt.ro_addr_false_hi; lia).
  (* f13_evt_F's premises on the normalized memory, as f13_evt_ro_F passes them; the shadow premise by
     ShadowRwOnT.shadow_rw_on_normalize (in the place of RoAdapt.rel_sw_norm) *)
  assert (Hfb : 0 <= f < 2 ^ 64) by lia.
  assert (Hpab : 0 <= pa < 2 ^ 64) by lia.
  assert (Hppb : 0 <= pp < 2 ^ 64) by lia.
  assert (Hpnb : 0 <= pn < 2 ^ 64) by lia.
  pose proof (RoAdapt.rel_rw_norm m _ (A + 256) _ REL Hro256 Hc256) as Hc256n.
  pose proof (RoAdapt.rel_stk_norm m _ _ _ REL Hrostk Hstk) as Hstkn.
  assert (Hfrgn : f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
                  bytes_at rsegs (normalize rsegs m) frg gfrag)
    by (intros H1 H2 H3 H4 H5 H6; exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) (Hfrg H1 H2 H3 H4 H5 H6))).
  assert (Hcondn : f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs (normalize rsegs m) f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs (normalize rsegs m) pa 2 /\ wr_at rsegs (normalize rsegs m) pp 8 /\
       wr_at rsegs (normalize rsegs m) pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (frg, frg + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]).
  { intros H1 H2 H3 H4 H5.
    destruct (Hcond H1 H2 H3 H4 H5) as (Hrw & Ha2 & Ha8 & Ha8' & Hw2 & Hw8 & Hw8' & Hdj).
    split; [exact (RoAdapt.rel_rw_norm m _ f _ REL Hrof72 Hrw)|].
    split; [exact Ha2|]; split; [exact Ha8|]; split; [exact Ha8'|].
    split; [exact (wr_at_norm rsegs m _ pa 2 REL Hw2 Hropa)|].
    split; [exact (wr_at_norm rsegs m _ pp 8 REL Hw8 Hropp)|].
    split; [exact (wr_at_norm rsegs m _ pn 8 REL Hw8' Hropn)|].
    exact Hdj. }
  pose proof (mem_inv_normalize rsegs m) as MIn.
  pose proof (RoAdapt.rel_ac_norm m _ REL AC0) as ACn.
  pose proof (A.ShadowRwOnT.shadow_rw_on_normalize _ m HRO SW) as SWn.
  unfold f13_evt_ro_shadow_R in SWn.
  assert (Haddrfrgn : f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
                      addressable (normalize rsegs m) frg 50)
    by (intros H1 H2 H3 H4 H5 H6; exact (RoAdapt.rel_addr_norm m _ _ _ REL (Haddrfrg H1 H2 H3 H4 H5 H6))).
  assert (Hcond2n : f <> 0 -> frg <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable (normalize rsegs m) f 72 /\ addressable (normalize rsegs m) pa 2 /\
       addressable (normalize rsegs m) pp 8 /\ addressable (normalize rsegs m) pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]).
  { intros H1 H2 H3 H4 H5; destruct (Hcond2 H1 H2 H3 H4 H5) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q1)|].
    split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q2)|].
    split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q3)|].
    split; [exact (RoAdapt.rel_addr_norm m _ _ _ REL Q4)|].
    split; [exact Q5 | exact Q6]. }
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB1) as HB1n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB2) as HB2n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB3) as HB3n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB4) as HB4n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) HB5) as HB5n.
  (* the run on the normalized memory: f13_evt_F's script, the callee entered through its _F_on contract *)
  assert (HC : ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fg_ret (fg_class f frg pa pp pn len st gfrag)))
                       a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7v s8 (Z_to_bv 64 f) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82154) fc None m' (seg_rom rsegs)
         /\ munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp)
                     (fg_class f frg pa pp pn len st gfrag)) (normalize rsegs m) m'
         /\ wmono rsegs (normalize rsegs m) m' /\ mem_inv rsegs m'
         /\ stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp)
         /\ fg_mem f pa pp pn st gfrag (fg_class f frg pa pp pn len st gfrag) m'
         /\ asan_cells m'
         /\ (forall P : Z -> Prop,
               A.ShadowRwOn.shadow_rw_on P (normalize rsegs m) -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7v s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82138) fc None (normalize rsegs m) (seg_rom rsegs))).
  { clear Hc256 Hstk Hfrg Hcond AC0 SW Haddrfrg Hcond2 HB1 HB2 HB3 HB4 HB5.
    subst s1v s9v s7v s2v.
    do 7 step.
    eapply ExecF.evtF_cut.
    { unfold reac_ctrl_identity_fragment_contract_F_on, REAC_CTRL_IDENTITY_FRAGMENT in HFRAG.
      eapply HFRAG with (RNG := RNG) (f := f) (fr := frg) (len := len) (pa := pa) (pp := pp) (pn := pn)
        (st := st) (g := gfrag).
      all: try assumption.
      all: try reflexivity. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI' & ST' & FGM & AC' & SW').
    subst ms2.
    replace (ret_pc (Z_to_bv 64 532820)) with (Z_to_bv 64 532820)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    apply ExecF.evtF_done.
    exists (Z_to_bv 64 532820), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [exact FGM|]. split; [exact AC' | exact SW']. }
  pose proof (MNF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & FGM & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (RoAdapt.rel_stk_back memX m0' _ _ Hmr ST')|].
  split; [exact (F13.fg_mem_back f pa pp pn st gfrag _ memX m0' Hmr FGM)|].
  split; [exact (RoAdapt.rel_ac_back memX m0' Hmr AC')|].
  (* the shadow transport: P on m, to the normalized memory, through the callee's transport, and back *)
  intros P HP.
  exact (A.ShadowRwOnT.shadow_rw_on_of_rel P memX m0' Hmr
           (SW' P (A.ShadowRwOnT.shadow_rw_on_normalize P m HRO HP))).
Qed.
