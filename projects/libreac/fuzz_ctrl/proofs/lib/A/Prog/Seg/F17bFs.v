(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names and addresses changed; 1175 of its 1288 lines of code are new or changed and 1596 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F17b.v, with its module paths, module names, addresses and numbers changed; 1262 of its 1375 lines of code are new or changed and 1175 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F17.v blob 2530d1eeed7 (the blob this tree had at release c5e779efe8c) at db985828094 (a working branch,
   the F17.v of record, two Theorem Labs lanes 06:28Z; the same text as d65d18383b1's blob f83ca6832224 but for the renames
   to_exit_8233c -> to_exit_823e8, to_exit_821c4 -> to_exit_822a0 and comments, same line numbers), seg_F17b
   (:1383-2005), its inline run (:1400-1699); Seg/Tac_f17b.v blob 8a2efdcdf106 (the blob this tree had at release c5e779efe8c) (f17_mc :188); Seg/F17F.v (an earlier version, blob d417b8f2c573, not in this delivery)
   (a Theorem Labs lane's split stretches of F17.f17_tail, used unchanged).
   Callee: lib/A/Prog/asan_memcpy_cF.v 3ae84ac9bb40 (the blob this tree had at release c5e779efe8c) (asan_memcpy_contract_F), proved by lib/A/Prog/asan_memcpyF.v (an earlier version, blob 31ace5ece389, not in this delivery)
   (asan_memcpy_holds_F). MemNorm route: lib/A/MemNormF.v 9e5ea0ff243d (the blob this tree had at release c5e779efe8c) (evtF_normalize_ro).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare:
   - f17_mc_of_F re-derives Tac_f17b.f17_mc at ExecF.RNG_all from f17_mc_F with the footprint contract discharged by
     asan_memcpy_holds_F (the plain contract premise of f17_mc is kept in its place and used by nothing);
     f17_mc_of_F_verbatim checks by constr_eq that its type is the type of Tac_f17b.f17_mc.
   - seg_F17b_run_F is the EXTRACTION of seg_F17b's inline run (F10F shape, a Theorem Labs lane 04:25Z): F17.v states no
     named run lemma for 0x822a0 -> 0x823e8 (seg_F17b applies Tac_slot.sl_run to it inline, :1400), so there is no
     F17.<r> for a constr_eq pin.  seg_F17b_run_of_F re-derives the UL Exec.evt form of the same run (the form
     sl_run takes) from seg_F17b_run_F at ExecF.RNG_all, with the plain memcpy contract in the place of the source's
     Hypothesis HMC (F17.v:486).
   - THE PIN of the extracted run is the SOURCE TIE seg_F17b_src (auditor a Theorem Labs lane's condition, via a Theorem Labs lane
     04:52Z): its statement is `type of F17.seg_F17b` (taken by ltac, so it cannot drift), proved by F17.seg_F17b's own
     script (Seg/F17.v of record, :1386-1426 and :1700-2000, verbatim but for the section arguments the moved
     lemmas now take explicitly) with the inline run (:1427-1699) discharged from PF.seg_F17b_run_of_F.
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. rule 24: no function proved. *)
(* THE RUN (F17.v:1400-1699, seg_F17b's argument K of sl_run, taken verbatim but for the substitutions below).
   0x822a0 `ld a0,232(s1)`, `or a0,a0,s4`, `bnez a0,0x823e4` (the length / sum guard); on its fall-through the nine
   instrumented record-byte checks 0x822ac .. 0x823c4 (each a load of the metadata byte (X >> 3) + ASAN_K of a record
   byte X and a compare, then the byte test); every failed test branches to the join 0x823e4 `ld s9,176(s1)` and lands at
   0x823e8 with memory unchanged; when every test passes, the tail 0x823c8 .. 0x823e4 (F17.f17_tail) runs: the copy of
   gg[27 .. 27 + gg[26]) into the frame object first.sroa.7 = fr + 2880 by `jal __asan_memcpy` (0x823d4), the two
   spill stores [A+104] = 1, [A+112] = gg[26] and the join's load.
   SUBSTITUTIONS against the source's K (each the source's own value at that point):
     flen g j := L, t_g (g_in g) j := G (as F10F does), AC.aspZ regs := spz (getr regs 2 = Z_to_bv 64 spz, F17.v:1454),
     Sem.reg_get := getr (A.Reusable.YK11.getr regs r = Sem.reg_get regs r for r <> 0, by its definition),
     fp_regs / fp_csr := the binders F / fc (a strengthening, as F17F.v's stretches do),
     the callee stack window's low end AC.aspZ regs - FN_STACK := the binder lo with f17_tail's own three premises
     (stk rsegs mem lo spz, lo + ASAN_MEMCPY_K <= spz, HIGHMEM_BEG <= lo; F17.f17_tail :521, instantiated by the source
     at :1651), because FN_STACK (1 MiB) has no source at the cgif-form cut.
   THE TAIL is composed from a Theorem Labs lane's F17F.v stretches, NOT re-cut: F17F.PF.f17_tail_pre_F (0x823c8 -> callee entry),
   f17_mc_F below (the call, on MemNorm.normalize m through asan_memcpy_contract_F, the split rule's "lift straight"
   case: the callee's _F is proved, a Theorem Labs lane 04:2xZ), F17F.PF.f17_tail_post_F (0x823d8 -> 0x823e8).
   FOOTPRINT (ExecF.rng / sh_word_rng premises), see F17bFs.rng.tsv: the spills [A+232], [A+176], [A+200], [A+32],
   [A+88, A+120); on a long frame the record block [phi, phi + 50) and its shadow word span; the callee's regions
   (rng_bytes, the image, its stack window and that window's shadow, the destination's 22-byte maximum
   [fr + 2880, fr + 2902) and its shadow).  The record facts and its regions are stated under `50 <= L ->`: a short
   frame takes the guard exit at once and reads only [A+232] and [A+176] (image B's F17bF.v has the same split). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F17 F17F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_cF asan_memcpyF rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
(* Required, NOT imported at file level: StepF's step / Exec names must not shadow the UL engine's, because
   seg_F17b_src below replays F17.seg_F17b's own script, whose names are the UL engine's. The footprint lemmas
   live in Module PF, which imports ExecF / StepF with module-local visibility (F17F.v's layout). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
(* Route (C) (L3 of glue_seg_F17b): the region form of the call's contract and the region transports, Required
   qualified (not imported) and cited through the aliases SRO / SRT / ACPYO / ACPFO below; used only by the _on twins
   at the end of Module PF. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c_on asan_memcpy_cF_on.
Import ListNotations.
(* ctrl's unit copy of YK11 (getr, seg_rom), by its full path: the core's copy lib/Reusable/YK11 is in this file's
   closure too, so the short name would be ambiguous (porter 04:24Z / 04:33Z). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module RM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcModel.
Module ACPY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c.
Module ACPF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF.
Module RA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module IB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
(* Tac_f17b.v states f17_mc over lib/Lib/PropExec.v's seg_rom (it imports no YK11); f17_mc_F keeps that text. *)
Module LPX := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
(* Twin-module gate (a Theorem Labs lane's ctrlgate DUP, a Theorem Labs lane 07:01Z): every short name that a twin family defines is cited
   through one of these aliases, each to the constant `About` says the bare name expanded to at its place (in Module
   PF, after its Imports of ExecF / StepF: core Lib.Mem / Lib.Frame / Lib.MState / ExecF names; at file level, in
   Section Src: the UL engine's Mem / Frame / Exec names). *)
Module LMe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module XF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module AK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module AM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YM05.
Module AO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YO0d.
Module UM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module UF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.
Module BzMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SRT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module ACPYO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Module ACPFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.

Module PF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
(* After StepF: getr / seg_rom are ctrl's unit YK11's again (F10F.v's order). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* ---- Footprint helpers. ---- *)

(* A sub-range's 8-aligned shadow word span lies in the span of the range (rng_asan's rng_sh_sub, through
   sh_word_rng_iff_sh). *)
Lemma f17bF_sh_sub : forall RNG p n p' n', 0 <= n' -> p <= p' -> p' + n' <= p + n ->
  RA.sh_word_rng RNG p n -> RA.sh_word_rng RNG p' n'.
Proof.
  intros RNG p n p' n' Hn' Hp Hq H.
  apply RA.sh_word_rng_iff_sh. apply RA.sh_word_rng_iff_sh in H.
  destruct (Z.eq_dec n' 0) as [E|E]; [left; exact E|right].
  destruct H as [H|H]; [lia|].
  exact (RA.rng_sh_sub RNG p n p' n' Hn' Hp Hq H).
Qed.

(* The one metadata byte an instrumented check of a byte of [p, p + n) loads, in the address form the shadow load
   steps on ((X >> 3) + ASAN_K, F17.f17_shadow). *)
Lemma f17bF_sh_byte : forall RNG p n a, p <= a < p + n -> 0 <= a ->
  RA.sh_word_rng RNG p n -> XF.rng RNG (Z.shiftr a 3 + ASAN_K) 1.
Proof.
  intros RNG p n a Ha Ha0 H. apply RA.sh_word_rng_iff_sh in H.
  destruct H as [H|H]; [lia|].
  pose proof (RA.rng_sh_byte RNG p n a Ha H) as Hb.
  unfold shadow_addr in Hb. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. exact Hb.
Qed.

(* An 8-byte carried word, in the read form the load steps consume (F17.v :1479-1483). *)
Lemma f17bF_rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (LMe.wa a) 8 = Some (LMe.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (LMe.bytes_at_ov_read rsegs m a (LMe.le8 (Z_to_bv 64 v)) 0 8 H ltac:(rewrite LMe.length_le8; cbn; lia)) as HH.
  rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite LMe.length_le8; cbn; lia). exact HH.
Qed.

Lemma f17bF_q64_bounds : forall m a v, q64 m a v -> 0 <= a /\ a + 8 <= 2 ^ 64.
Proof. intros m a v (H0 & H1 & _). rewrite LMe.length_le8 in H1. change (Z.of_nat 8) with 8 in H1. lia. Qed.

(* ---- The call __asan_memcpy at 0x823d4: Tac_f17b.f17_mc (:188) under a footprint, with the footprint contract
   asan_memcpy_contract_F in the place of the plain contract, run on MemNorm.normalize m and moved back by
   MemNormF.evtF_normalize_ro (the evtF form of the MemNorm.evt_normalize that f17_mc uses).  The premises and the
   post are f17_mc's; the footprint premises are the contract's, appended. ---- *)
Lemma f17_mc_F : forall (RNG : XF.footprint), ACPF.asan_memcpy_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S N spz lo : Z) (src : list byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 N -> sp = Z_to_bv 64 spz ->
  0 <= S -> AC.GT <= D -> AC.GT <= lo -> spz <= APPMEM_END -> 1 <= N <= 22 ->
  ro_agree rsegs m ->
  LMe.bytes_at rsegs m S src -> length src = Z.to_nat N ->
  LF.stk rsegs m D (D + N) ->
  (S + N <= D \/ D + N <= S) ->
  addressable m S N -> addressable m D N ->
  app_mem (S + N) -> app_mem (D + N) -> app_mem (S + 7) -> app_mem (D + 7) ->
  RT_HI <= D ->
  (D + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= D) -> (S + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= S) ->
  LF.stk rsegs m lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  asan_cells m -> shadow_rw m ->
  RngBytes.rng_bytes RNG ->
  XF.rng RNG IB.IMG_LO (IB.IMG_HI - IB.IMG_LO) ->
  XF.rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  XF.rng RNG D N -> XF.rng RNG S N ->
  RA.sh_word_rng RNG D N -> RA.sh_word_rng RNG S N ->
  RA.sh_word_rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  evtF rsegs RNG
    (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
       ms = LM.MS (LF.mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (LM.ret_pc ra) fc None m' (LPX.seg_rom rsegs) /\
       LF.munch [(D, D + N); (spz - ACPY.ASAN_MEMCPY_K, spz)] m m' /\ LF.wmono rsegs m m' /\ ro_agree rsegs m' /\
       LF.stk rsegs m' lo spz /\ LMe.bytes_at rsegs m' D src)
    (LM.MS (LF.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACPY.ASAN_MEMCPY) fc None m (LPX.seg_rom rsegs)).
Proof.
  intros RNG HMC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m D S N spz lo src E0 E1 E2 Esp0 HS0 HDGT HloGT HspE HN HRO HBS HLs HSTD HDS HAS HAD HapSN HapDN
    HapS7 HapD7 HRT HDW HSW HSTK HloK Hlo HAC HSWr GRB GIMG GSTK GD GS GSD GSS GSK.
  subst a0 a1 a2 sp.
  assert (HGT0 : 0 <= AC.GT <= HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia).
  pose proof HapDN as HapDN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapDN'.
  pose proof HapSN as HapSN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapSN'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply LM.unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply LM.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply LM.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spz) = spz)
    by (apply LM.unsigned_lit; unfold ACPY.ASAN_MEMCPY_K, HIGHMEM_BEG, APPMEM_END in *; lia).
  destruct (Tac_f17b.f17m_stk_cb m D (D + N) D (Z.to_nat N) HSTD ltac:(lia) ltac:(lia)) as (junk & Hjl & HRW).
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  pose proof HMC as HM. unfold ACPF.asan_memcpy_contract_F in HM. cbv zeta in HM.
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (LPX.seg_rom rsegs) HRO).
    eapply HM with (RNG := RNG) (src := src) (junk := junk) (lo := lo).
    all: rewrite ?ED, ?ES, ?EN, ?Esp.
    - exact (bytes_at_normalize rsegs m _ _ HRO HBS).
    - exact HLs.
    - exact (Tac_f17b.f17m_rw_norm m _ _ HRO HDGT HRW).
    - right. destruct HDS as [Hd|Hd]; [left; exact Hd | right; exact Hd].
    - lia.
    - exact (Tac_f17b.f17m_addr_norm m _ _ HRO HAS).
    - exact (Tac_f17b.f17m_addr_norm m _ _ HRO HAD).
    - right. exact HapSN.
    - right. exact HapDN.
    - right. split; [exact HapS7 | exact HapD7].
    - right. exact HRT.
    - exact HDW.
    - exact HSW.
    - apply (Tac_f17b.f17m_stk_norm m _ _ HRO HloGT HSTK).
    - exact HloK.
    - exact Hlo.
    - exact HspE.
    - exact (Tac_f17b.f17m_cells_norm m HRO HAC).
    - exact (Tac_f17b.f17m_shadow_rw_norm m HRO HSWr).
    - exact (mem_inv_normalize rsegs m).
    - exact GRB.
    - exact GIMG.
    - exact GSTK.
    - exact GD.
    - exact GS.
    - exact GSD.
    - exact GSS.
    - exact GSK. }
  intros ms' (s0' & Hp & REL & SAME). unfold ACPY.asan_memcpy_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MUc & WMc & MIc & STc & RWc & BSc & ACc & SWc).
  subst s0'.
  rewrite ED, EN, Esp in MUc. rewrite Esp in STc. rewrite ED, EN in RWc.
  destruct (Tac_f17b.f17m_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
  split; [exact Ems|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME MUc)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME WMc)|].
  split; [exact (ro_agree_of_mem_rel rsegs (ms_mem ms') m0' HREL)|].
  split; [exact (Tac_f17b.f17m_stk_back (ms_mem ms') m0' _ _ HREL STc)|].
  exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m0' _ _ HREL) (Tac_f17b.f17m_cb_bytes m0' _ _ _ RWc)).
Qed.

(* Tac_f17b.f17_mc's statement, term for term: f17_mc_F at ExecF.RNG_all, with the footprint contract discharged by
   a Theorem Labs lane's proof asan_memcpy_holds_F (lib/A/Prog/asan_memcpyF.v), so that the plain asan_memcpy_contract premise
   of f17_mc is kept in its place and used by nothing. *)
Lemma f17_mc_of_F : ACPY.asan_memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S N spz lo : Z) (src : list byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 N -> sp = Z_to_bv 64 spz ->
  0 <= S -> AC.GT <= D -> AC.GT <= lo -> spz <= APPMEM_END -> 1 <= N <= 22 ->
  ro_agree rsegs m ->
  LMe.bytes_at rsegs m S src -> length src = Z.to_nat N ->
  LF.stk rsegs m D (D + N) ->
  (S + N <= D \/ D + N <= S) ->
  addressable m S N -> addressable m D N ->
  app_mem (S + N) -> app_mem (D + N) -> app_mem (S + 7) -> app_mem (D + 7) ->
  RT_HI <= D ->
  (D + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= D) -> (S + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= S) ->
  LF.stk rsegs m lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  asan_cells m -> shadow_rw m ->
  LE.evt rsegs
    (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
       ms = LM.MS (LF.mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (LM.ret_pc ra) fc None m' (LPX.seg_rom rsegs) /\
       LF.munch [(D, D + N); (spz - ACPY.ASAN_MEMCPY_K, spz)] m m' /\ LF.wmono rsegs m m' /\ ro_agree rsegs m' /\
       LF.stk rsegs m' lo spz /\ LMe.bytes_at rsegs m' D src)
    (LM.MS (LF.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACPY.ASAN_MEMCPY) fc None m (LPX.seg_rom rsegs)).
Proof.
  intros _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m D S N spz lo src E0 E1 E2 Esp0 HS0 HDGT HloGT HspE HN HRO HBS HLs HSTD HDS HAS HAD HapSN HapDN
    HapS7 HapD7 HRT HDW HSW HSTK HloK Hlo HAC HSWr.
  pose proof HapDN as HapDN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapDN'.
  pose proof HapSN as HapSN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapSN'.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HHv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAv : APPMEM_END = 0x800000000000) by reflexivity.
  apply (evtF_evt rsegs RNG_all).
  apply (f17_mc_F RNG_all asan_memcpyF.asan_memcpy_holds_F
           ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m D S N spz lo src E0 E1 E2 Esp0 HS0 HDGT HloGT HspE HN HRO HBS HLs HSTD HDS HAS HAD HapSN HapDN
           HapS7 HapD7 HRT HDW HSW HSTK HloK Hlo HAC HSWr).
  - intros ? ? _ _ _. exact I.
  - apply rng_all; unfold IB.IMG_LO, IB.IMG_HI; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply RA.sh_word_rng_all; lia.
  - apply RA.sh_word_rng_all; lia.
  - apply RA.sh_word_rng_all; lia.
Qed.

Example f17_mc_of_F_verbatim : True.
Proof.
  let A := type of Tac_f17b.f17_mc in let B := type of f17_mc_of_F in constr_eq A B.
  exact I.
Qed.

(* ---- The stepping tactics of seg_F17b's script (F17.v :1223-1373), over evtF. ---- *)
Ltac cbv_concl_iotaF :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in change_no_check g'.

(* F17.v or1_bnez_tk (:1223) *)
Ltac or1_bnez_tkF :=
  match goal with
  | |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        ((match goal with |- true = _ => symmetry | _ => idtac end);
         rewrite ?Bool.negb_true_iff;
         try unfold bv_eqb; apply Z.eqb_neq;
         rewrite ?bv_or_unsigned, ?BzMS.unsigned_lit_wrap; rewrite ?Z.mod_0_l by lia;
         first [ refine (proj2 (F17.f17_lor_odd _ _ _)); left; reflexivity
               | refine (proj2 (F17.f17_lor_odd _ _ _)); right; reflexivity
               | refine (proj1 (F17.f17_lor_odd _ _ _)); left; reflexivity
               | refine (proj1 (F17.f17_lor_odd _ _ _)); right; reflexivity ])
  end; cbv_concl_iotaF.

(* F17.v regeq (:1238), for the getr facts of K *)
Ltac regeqF :=
  first [ reflexivity
        | OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs;
          first [ reflexivity
                | symmetry; eassumption
                | eassumption
                | symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
                | apply Regs6ss.mkR_of_eqv; reflexivity ] ].

(* F17.v exit_K_step (:1248): the join's load and the exit into K's memory-unchanged arm *)
Ltac exit_K_stepF fop Hb :=
  step;
  apply evtF_done; hnf; do 3 eexists; split; [reflexivity|];
  split; [reflexivity|];
  do 13 (split; [regeqF|]);
  left; split; [reflexivity | exact (fop _ _ Hb)].

(* F17.v converge (:1257) *)
Ltac convergeF scratch Xe b OK BD :=
  match goal with
  | |- evtF ?segs ?RNG ?Q (LM.MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evtF segs RNG Q (LM.MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold LMe.sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iotaF;
           match goal with |- evtF _ _ _ (LM.MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold LMe.sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iotaF; step; step;
           match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (LM.unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iotaF; step;
           match goal with |- evtF _ _ _ (LM.MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

(* F17.v shadowcheck (:1284); RSH gives the one-byte footprint of the metadata byte of phi + kk *)
Ltac shadowcheckF phi mem Haddr RSH kk :=
  step; step;
  rewrite (LM.unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in let Rk := fresh "Rk" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (F17.f17_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  pose proof (RSH kk ltac:(lia)) as Rk;
  step; step; convergeF (Z_to_bv 5 12) (phi + kk) b OK BD.

(* F17.v converge_blt (:1295) *)
Ltac converge_bltF scratch Xe b OK BD :=
  match goal with
  | |- evtF ?segs ?RNG ?Q (LM.MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evtF segs RNG Q (LM.MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold LMe.sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iotaF;
           match goal with |- evtF _ _ _ (LM.MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold LMe.sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iotaF; step; step;
           match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (rewrite (LM.unsigned_lit Xe) by (unfold APPMEM_END in *; lia);
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iotaF;
           match goal with |- evtF _ _ _ (LM.MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro.

Ltac shadowcheck_bltF phi mem Haddr RSH kk :=
  step; step;
  rewrite (LM.unsigned_lit (phi + kk)) by (unfold APPMEM_END in *; lia);
  let Had := fresh "Had" in let b := fresh "b" in let HRsh := fresh "HRsh" in
  let OK := fresh "OK" in let BD := fresh "BD" in let Rk := fresh "Rk" in
  assert (Had : addressable mem (phi + kk) 1) by (apply (addressable_sub mem phi 50 kk 1 Haddr); lia);
  destruct (F17.f17_shadow mem (phi + kk) Had) as (b & HRsh & OK & BD);
  pose proof (RSH kk ltac:(lia)) as Rk;
  step; step; converge_bltF (Z_to_bv 5 12) (phi + kk) b OK BD.

(* F17.v clr1 (:1333) *)
Ltac clr1F := repeat match goal with
  | H : ov_read_bytes _ _ _ 1 = _ |- _ => clear H
  | H : bv_signed _ = 0 \/ _ |- _ => clear H
  | H : XF.rng _ (Z.shiftr _ 3 + _) 1 |- _ => clear H
  end.

(* F17.v frbc (:1342) *)
Ltac frbcF phi mem L Hrbb kk cc Hb fop :=
  let Hrr := fresh "Hrr" in let HH := fresh "HH" in
  assert (Hrr : ov_read_bytes rsegs mem (LMe.wa (phi + kk)) 1 = Some (firstn 1 (skipn (Z.to_nat kk) L))) by
    (pose proof (LMe.bytes_at_ov_read rsegs mem phi L (Z.to_nat kk) 1 Hrbb ltac:(lia)) as HH;
     replace (phi + Z.of_nat (Z.to_nat kk)) with (phi + kk) in HH by lia; exact HH);
  step; step; step;
  destruct (RF.bat L kk =? cc) eqn:Hb;
  [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by
        (symmetry; rewrite (F17.f17_bne_val L kk cc ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iotaF
  | match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        (symmetry; rewrite (F17.f17_bne_val L kk cc ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iotaF; exit_K_stepF fop Hb ].

(* F17.v frbnzc (:1359) *)
Ltac frbnzcF phi mem L Hrbb kk Hb fop :=
  let Hrr := fresh "Hrr" in let HH := fresh "HH" in
  assert (Hrr : ov_read_bytes rsegs mem (LMe.wa (phi + kk)) 1 = Some (firstn 1 (skipn (Z.to_nat kk) L))) by
    (pose proof (LMe.bytes_at_ov_read rsegs mem phi L (Z.to_nat kk) 1 Hrbb ltac:(lia)) as HH;
     replace (phi + Z.of_nat (Z.to_nat kk)) with (phi + kk) in HH by lia; exact HH);
  step; step;
  destruct (RF.bat L kk =? 0) eqn:Hb;
  [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by
        (symmetry; rewrite (F17.f17_bne_val L kk 0 ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iotaF
  | match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by
        (symmetry; rewrite (F17.f17_bne_val L kk 0 ltac:(lia) ltac:(lia) ltac:(lia)), Hb; reflexivity) end;
    cbv_concl_iotaF; exit_K_stepF fop Hb ].

(* ---- The run of seg_F17b, 0x822a0 -> 0x823e8 (F17.v :1400-1699). ---- *)
Lemma seg_F17b_run_F : forall (RNG : XF.footprint), ACPF.asan_memcpy_contract_F ->
  forall (regs F : bvmap 5 word) (fc : bv 32) (mem : word -> option byte)
         (A phi fr L spz lo : Z) (G : list byte) (s : bool),
  (* the cut's registers: sp, s1 = A, s4 = 1 - sum_ok, s7 = phi, s10 = ASAN_K *)
  AK.getr regs 2 = Z_to_bv 64 spz -> AK.getr regs 9 = Z_to_bv 64 A -> AK.getr regs 20 = Z_to_bv 64 (1 - b2z s) ->
  AK.getr regs 23 = Z_to_bv 64 phi -> AK.getr regs 26 = Z_to_bv 64 ASAN_K ->
  (* the spill window and the spills the run reads *)
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  q64 mem (A + 232) (if 50 <=? L then 0 else 1) -> q64 mem (A + 176) (fr + 64) ->
  q64 mem (A + 200) (phi + 18) -> q64 mem (A + 32) (fr + 2880) ->
  (* the record, on a long frame only (a short frame takes the guard exit at once) *)
  (50 <= L ->
     s = (RM.blocksum (skipn 18 G) =? 0) /\ length G = 50%nat /\ LMe.bytes_at rsegs mem phi G /\
     addressable mem phi 50 /\ (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
     (phi + 50 <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= phi)) ->
  (* the frame object first.sroa.7 and the frame *)
  addressable mem (fr + 2880) 35 -> LF.stk rsegs mem fr (fr + FRAME_BYTES) ->
  AC.GT <= fr -> fr + FRAME_BYTES <= A -> spz <= A ->
  (fr + FRAME_BYTES <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= fr) ->
  LMe.wr_at rsegs mem (A + 88) 32 ->
  (* the callee's stack window (F17.f17_tail's own premises) and the runtime facts it asks *)
  LF.stk rsegs mem lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  ro_agree rsegs mem -> asan_cells mem -> shadow_rw mem ->
  (* the footprint *)
  XF.rng RNG (A + 232) 8 -> XF.rng RNG (A + 176) 8 -> XF.rng RNG (A + 200) 8 -> XF.rng RNG (A + 32) 8 ->
  XF.rng RNG (A + 88) 32 ->
  (50 <= L -> XF.rng RNG phi 50 /\ RA.sh_word_rng RNG phi 50) ->
  RngBytes.rng_bytes RNG -> XF.rng RNG IB.IMG_LO (IB.IMG_HI - IB.IMG_LO) ->
  XF.rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  RA.sh_word_rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  XF.rng RNG (fr + 2880) 22 -> RA.sh_word_rng RNG (fr + 2880) 22 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R F pc' fc None mem' (AK.seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x823e8 /\
       AK.getr R 2 = AK.getr regs 2 /\ AK.getr R 3 = AK.getr regs 3 /\ AK.getr R 4 = AK.getr regs 4 /\
       AK.getr R 8 = AK.getr regs 8 /\ AK.getr R 9 = AK.getr regs 9 /\ AK.getr R 19 = AK.getr regs 19 /\
       AK.getr R 26 = AK.getr regs 26 /\ AK.getr R 21 = AK.getr regs 21 /\ AK.getr R 23 = AK.getr regs 23 /\
       AK.getr R 24 = AK.getr regs 24 /\ AK.getr R 22 = AK.getr regs 22 /\
       AK.getr R 18 = AK.getr regs 18 /\ AK.getr R 25 = Z_to_bv 64 (fr + 64) /\
       ((mem' = mem /\ f_opens L G = false) \/
        (f_opens L G = true /\
         exists mc : word -> option byte,
           LF.munch [(fr + 2880, fr + 2880 + RF.bat G 26);
                     (spz - ACPY.ASAN_MEMCPY_K, spz)] mem mc /\
           LF.wmono rsegs mem mc /\ ro_agree rsegs mc /\
           LF.stk rsegs mc lo spz /\
           LMe.bytes_at rsegs mc (fr + 2880) (firstn (Z.to_nat (RF.bat G 26)) (skipn 27 G)) /\
           mem' = write_to_mem (write_to_mem mc (LMe.wa (A + 104)) (LMe.le8 (Z_to_bv 64 1)))
                    (LMe.wa (A + 112)) (LMe.le8 (Z_to_bv 64 (RF.bat G 26))))))
    (LM.MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x822a0) fc None mem (AK.seg_rom rsegs)).
Proof.
  intros RNG MCPY regs F fc mem A phi fr L spz lo G s E2 E9 E20 E23 E26 Happ Q232 Q176 Q200 Q32 HLONG
    Had35 Hstkfr HGTfr HfrA HspA Hplace Hwr HSTK HK HLO HRO HAC HSW
    G232 G176 G200 G32 G88 GLONG GRB GIMG GSTK GSSTK GD GSD.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  assert (HAr0 : HIGHMEM_BEG <= A + 88 /\ A + 120 <= APPMEM_END)
    by (split; [exact (proj1 (Happ (A + 88) ltac:(lia))) | pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia]).
  assert (HHv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAv : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by (rewrite <- E9; unfold AK.getr; reflexivity).
  assert (Hs23r : Sem.reg_get regs (23%bv) = Z_to_bv 64 phi) by (rewrite <- E23; unfold AK.getr; reflexivity).
  assert (Hs26r : Sem.reg_get regs (26%bv) = Z_to_bv 64 ASAN_K) by (rewrite <- E26; unfold AK.getr; reflexivity).
  assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A)
                 (bvmap_set (23%bv) (Z_to_bv 64 phi)
                   (bvmap_set (26%bv) (Z_to_bv 64 ASAN_K) (Regs6ss.mkR_of regs)))
                = Regs6ss.mkR_of regs)
    by (rewrite <- Hs9r, <- Hs23r, <- Hs26r; cbn; reflexivity).
  rewrite <- IDW.
  pose proof (f17bF_rd8 mem (A + 176) (fr + 64) Q176) as HR176.
  destruct (50 <=? L) eqn:Ebig.
  2:{ (* short arm: [s1+232] = 1, so a0 = 1 | s4 has bit 0 set and `bnez a0, 0x823e4` is TAKEN, into the join
         `ld s9,176(s1)` and on to 0x823e8 (memory unchanged) *)
      pose proof (f17bF_rd8 mem (A + 232) 1 Q232) as HR232.
      step. (* 0x822a0: ld a0,232(s1) : a0 = 1 *)
      step. (* 0x822a4: or a0,a0,s4 *)
      step. (* 0x822a8: bnez a0,823e4 -- taken *)
      or1_bnez_tkF.
      exit_K_stepF F17.f17_fop_len Ebig. }
  (* long arm: 50 <= L, so the record facts hold *)
  assert (HfL : 50 <= L) by (apply Z.leb_le; exact Ebig).
  destruct (HLONG HfL) as (Hs & Hrblen & Hrbb & Haddr & Hfrph & Hphsp).
  destruct (GLONG HfL) as (Grec & Gsrec).
  pose proof (f17bF_rd8 mem (A + 232) 0 Q232) as HR232.
  step. (* 0x822a0: ld a0,232(s1) : 0 on the long arm *)
  step. (* 0x822a4: or a0,a0,s4 *)
  step. (* 0x822a8: bnez a0,823e4 : NOT taken exactly when s4 = 0, i.e. the block sum is 0 *)
  match goal with
  | |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with
      | context [Z.lor 0 (bv_unsigned (Sem.reg_get ?R ?r))] =>
          assert (Hs20r : Sem.reg_get R r = Z_to_bv 64 (1 - b2z s)) by
            (transitivity (Sem.reg_get regs r);
             [ symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
             | rewrite <- E20; unfold AK.getr; reflexivity ])
      end
  end.
  destruct s eqn:ESUM;
    (match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
       first [ replace c with true by (symmetry; rewrite Hs20r; vm_compute; reflexivity)
             | replace c with false by (symmetry; rewrite Hs20r; vm_compute; reflexivity) ]
     end; cbv_concl_iotaF).
  - (* s4 = 0: the guard's branch is not taken and the opens_record body at 0x822ac runs; its nine byte tests
       decide f_opens *)
    assert (Hbs : (RM.blocksum (skipn 18 G) =? 0) = true) by (symmetry; exact Hs).
    pose proof Haddr as Haddr'. destruct Haddr' as (Hphi0 & _ & HphiE & _).
    assert (RSH : forall k, 16 <= k <= 26 -> XF.rng RNG (Z.shiftr (phi + k) 3 + ASAN_K) 1)
      by (intros k Hk; apply (f17bF_sh_byte RNG phi 50 (phi + k)); [lia | lia | exact Gsrec]).
    (* check 1 (0x822ac .. 0x822c8): phi+16, const 205 *)
    step. (* 0x822ac: addi a0,s7,16 *)
    shadowcheckF phi mem Haddr RSH 16.
    frbcF phi mem G Hrbb 16 205 Hb16 F17.f17_fop_16. clr1F.
    (* check 2 (0x822cc .. 0x822ec): phi+17, const 234; `ld a3,200(s1)` (the phi + 18 pointer) between the
       shadow load and its bnez *)
    pose proof (f17bF_rd8 mem (A + 200) (phi + 18) Q200) as HR200.
    step. (* 0x822cc: addi a0,s7,17 *)
    step. step. (* srli a1,a0,3 ; add a1,a1,s10 *)
    rewrite (LM.unsigned_lit (phi + 17)) by (unfold APPMEM_END in HphiE; lia).
    assert (Had17 : addressable mem (phi + 17) 1) by (apply (addressable_sub mem phi 50 17 1 Haddr); lia).
    destruct (F17.f17_shadow mem (phi + 17) Had17) as (b17 & HRsh17 & OK17 & BD17).
    pose proof (RSH 17 ltac:(lia)) as R17.
    step. (* 0x822d8: lb a1,0(a1) *)
    step. (* 0x822dc: ld a3,200(s1) : a3 = phi + 18 *)
    step. (* 0x822e0: bnez a1,.. *)
    convergeF (Z_to_bv 5 12) (phi + 17) b17 OK17 BD17.
    frbcF phi mem G Hrbb 17 234 Hb17 F17.f17_fop_17. clr1F.
    (* check 3 (0x822f0 .. 0x82308): the byte at a3 = phi+18, const 4; the shadow byte goes to a0 *)
    step. step. (* srli a0,a3,3 ; add a0,a0,s10 *)
    rewrite (LM.unsigned_lit (phi + 18)) by (unfold APPMEM_END in *; lia).
    assert (Had18 : addressable mem (phi + 18) 1) by (apply (addressable_sub mem phi 50 18 1 Haddr); lia).
    destruct (F17.f17_shadow mem (phi + 18) Had18) as (b18 & HRsh18 & OK18 & BD18).
    pose proof (RSH 18 ltac:(lia)) as R18.
    step. (* 0x822f8: lb a0,0(a0) *)
    step. (* 0x822fc: bnez a0,.. *)
    convergeF (Z_to_bv 5 11) (phi + 18) b18 OK18 BD18.
    frbcF phi mem G Hrbb 18 4 Hb18 F17.f17_fop_18. clr1F.
    (* check 4: phi+19, const 1 *)
    step. shadowcheckF phi mem Haddr RSH 19. frbcF phi mem G Hrbb 19 1 Hb19 F17.f17_fop_19. clr1F.
    (* check 5: phi+22, bnez a0 (exit if != 0) *)
    step. shadowcheckF phi mem Haddr RSH 22. frbnzcF phi mem G Hrbb 22 Hb22 F17.f17_fop_22. clr1F.
    (* check 6: phi+23, const 2 *)
    step. shadowcheckF phi mem Haddr RSH 23. frbcF phi mem G Hrbb 23 2 Hb23 F17.f17_fop_23. clr1F.
    (* check 7: phi+24, bnez a0 *)
    step. shadowcheckF phi mem Haddr RSH 24. frbnzcF phi mem G Hrbb 24 Hb24 F17.f17_fop_24. clr1F.
    (* check 8: phi+25, const 254 *)
    step. shadowcheckF phi mem Haddr RSH 25. frbcF phi mem G Hrbb 25 254 Hb25 F17.f17_fop_25. clr1F.
    (* check 9: phi+26, range check (b[8] - 23 >=u -22) *)
    step. shadowcheck_bltF phi mem Haddr RSH 26.
    assert (Hrr26 : ov_read_bytes rsegs mem (LMe.wa (phi + 26)) 1
                      = Some (firstn 1 (skipn (Z.to_nat 26) G))).
    { pose proof (LMe.bytes_at_ov_read rsegs mem phi G (Z.to_nat 26) 1 Hrbb ltac:(lia)) as H.
      replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
    step. (* lbu s9,0(a0) *)
    step. (* addi a0,s9,-23 *)
    step. (* li a1,-22 *)
    step. (* bltu a0,a1,823e4 : the range test 1 <= gg[26] <= 22 *)
    destruct ((1 <=? RF.bat G 26) && (RF.bat G 26 <=? 22)) eqn:Hb26;
    [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by
          (symmetry; rewrite (F17.f17_bltu_val G 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
      cbv_concl_iotaF
    | match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by
          (symmetry; rewrite (F17.f17_bltu_val G 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
      cbv_concl_iotaF; exit_K_stepF F17.f17_fop_26 Hb26 ].
    clr1F.
    (* ---- the record opens: 0x823c8 .. 0x823e4 is F17.f17_tail, composed here from F17F.v's two stretches and
       the call (f17_mc_F), as F17F.f17_tail_of_pre_post composes them at RNG_all. ---- *)
    assert (H50t : (50 <=? L) = true) by exact Ebig.
    assert (Hop : f_opens L G = true)
      by exact (F17.f17_fopens_true L G H50t Hb16 Hb17 Hb18 Hb19 Hb22 Hb23 Hb24 Hb25 Hb26 Hbs).
    assert (Hn26 : 1 <= RF.bat G 26 <= 22)
      by (apply andb_prop in Hb26 as (Hl1 & Hl2); apply Z.leb_le in Hl1; apply Z.leb_le in Hl2; lia).
    set (n := RF.bat G 26) in *.
    set (src := firstn (Z.to_nat n) (skipn 27 G)).
    pose proof (ba_sub mem phi G 27 (Z.to_nat n) Hrbb ltac:(rewrite Hrblen; lia)) as Hsrc.
    replace (phi + Z.of_nat 27) with (phi + 27) in Hsrc by lia.
    fold src in Hsrc.
    assert (Hsrcl : length src = Z.to_nat n)
      by (unfold src; rewrite length_firstn, length_skipn, Hrblen; lia).
    assert (HadS : addressable mem (phi + 27) n)
      by (apply (addressable_sub mem phi 50 27 n Haddr); lia).
    assert (HadD : addressable mem (fr + 2880) n).
    { pose proof (addressable_sub mem (fr + 2880) 35 0 n Had35 ltac:(lia) ltac:(lia) ltac:(lia)) as HadD0.
      rewrite Z.add_0_r in HadD0. exact HadD0. }
    assert (HstD : LF.stk rsegs mem (fr + 2880) (fr + 2880 + n)).
    { destruct (LF.stk_split rsegs mem fr (fr + 2880) (fr + FRAME_BYTES) Hstkfr ltac:(lia)) as (_ & Hs1').
      destruct (LF.stk_split rsegs mem (fr + 2880) (fr + 2880 + n) (fr + FRAME_BYTES) Hs1' ltac:(lia))
        as (Hs2' & _).
      exact Hs2'. }
    assert (Hdj : phi + 27 + n <= fr + 2880 \/ fr + 2880 + n <= phi + 27) by (destruct Hfrph; lia).
    assert (HappP : forall a, phi <= a < phi + 50 -> app_mem a).
    { intros a Ha. pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab (a - phi) ltac:(lia)) as (Hap & _).
      replace (phi + (a - phi)) with a in Hap by lia. exact Hap. }
    assert (HappD : forall a, fr + 2880 <= a < fr + 2915 -> app_mem a).
    { intros a Ha. pose proof Had35 as (_ & _ & _ & Hab). destruct (Hab (a - (fr + 2880)) ltac:(lia)) as (Hap & _).
      replace (fr + 2880 + (a - (fr + 2880))) with a in Hap by lia. exact Hap. }
    pose proof (HappP (phi + 49) ltac:(lia)) as Hap49. unfold app_mem, LOWMEM_END in Hap49.
    (* s9 holds the loaded byte raw; f17_tail_pre_F names it as the model's gg[26] *)
    rewrite (F17.f17_byte_word G 26 ltac:(lia) ltac:(lia)). fold n.
    (* stretch 1: 0x823c8 .. the callee entry (F17F.PF.f17_tail_pre_F) *)
    match goal with |- evtF _ _ _ (LM.MS ?R0 ?F0 _ ?fc0 _ _ _) =>
      eapply evtF_cut;
      [ apply (F17F.PF.f17_tail_pre_F RNG (Sem.reg_get R0 1) (Sem.reg_get R0 2) (Sem.reg_get R0 3) (Sem.reg_get R0 4)
                (Sem.reg_get R0 5) (Sem.reg_get R0 6) (Sem.reg_get R0 7) (Sem.reg_get R0 8)
                (Sem.reg_get R0 9) (Sem.reg_get R0 10) (Sem.reg_get R0 11) (Sem.reg_get R0 12)
                (Sem.reg_get R0 13) (Sem.reg_get R0 14) (Sem.reg_get R0 15) (Sem.reg_get R0 16)
                (Sem.reg_get R0 17) (Sem.reg_get R0 18) (Sem.reg_get R0 19) (Sem.reg_get R0 20)
                (Sem.reg_get R0 21) (Sem.reg_get R0 22) (Sem.reg_get R0 23) (Sem.reg_get R0 24)
                (Sem.reg_get R0 25) (Sem.reg_get R0 26) (Sem.reg_get R0 27) (Sem.reg_get R0 28)
                (Sem.reg_get R0 29) (Sem.reg_get R0 30) (Sem.reg_get R0 31) F0 fc0 mem A phi fr n)
      | ] end;
      [ reflexivity | reflexivity | reflexivity | exact Q32 | exact G32 | ].
    intros ms' ->.
    (* the call (f17_mc_F), with a0 = fr + 2880, a1 = phi + 27, a2 = n, ra = 0x823d8 *)
    eapply evtF_cut.
    { eapply (f17_mc_F RNG MCPY) with (D := fr + 2880) (S := phi + 27) (N := n) (spz := spz) (lo := lo)
        (src := src);
        [ reflexivity | reflexivity | reflexivity | exact E2 | lia | lia | lia | lia | exact Hn26 | exact HRO
        | exact Hsrc | exact Hsrcl | exact HstD | exact Hdj | exact HadS | exact HadD
        | apply HappP; lia | apply HappD; lia
        | replace (phi + 27 + 7) with (phi + 34) by lia; apply HappP; lia
        | replace (fr + 2880 + 7) with (fr + 2887) by lia; apply HappD; lia
        | unfold RT_HI; lia | destruct Hplace; [left|right]; lia | destruct Hphsp; [left|right]; lia
        | exact HSTK | exact HK | exact HLO | exact HAC | exact HSW | exact GRB | exact GIMG | exact GSTK
        | apply (rng_sub' RNG (fr + 2880) 22); [exact GD | lia]
        | apply (rng_sub' RNG phi 50); [exact Grec | lia]
        | apply (f17bF_sh_sub RNG (fr + 2880) 22); [lia | lia | lia | exact GSD]
        | apply (f17bF_sh_sub RNG phi 50); [lia | lia | lia | exact Gsrec]
        | exact GSSTK ]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc
                & E & MU & WM & RO' & ST' & Bsrc).
    subst ms'.
    replace (LM.ret_pc (Z_to_bv 64 533464)) with (Z_to_bv 64 0x823d8)
      by (symmetry; apply LM.ret_pc_even; [clear; lia | reflexivity]).
    (* stretch 2: the return block 0x823d8 .. 0x823e8 (F17F.PF.f17_tail_post_F), from the canonical form of the state
       the callee returned in *)
    match goal with |- evtF _ _ _ (LM.MS (LF.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15
                                            ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30
                                            ?x31) _ _ _ _ _ _) =>
      rewrite <- (F17F.PF.f17F_mkR_of_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    end.
    eapply evtF_mono.
    { eapply (F17F.PF.f17_tail_post_F RNG _ mc _ _ _ _ _ _ _ _ _ _ _ _ F fc mem A phi fr n spz lo src);
        try reflexivity; try assumption; lia. }
    intros ms' (ra' & a0' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4''
                & t5'' & t6'' & mc' & -> & MUc & WMc & ROc & STc & BSc).
    hnf. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 13 (split; [regeqF|]).
    right. split; [exact Hop|]. exists mc'.
    split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|]. split; [exact STc|]. split; [exact BSc|].
    reflexivity.
  - (* s4 <> 0: the block sum is nonzero, so the record does not open; the guard's bnez was taken into the
       join 0x823e4 (memory unchanged) *)
    assert (Hbs : (RM.blocksum (skipn 18 G) =? 0) = false) by (symmetry; exact Hs).
    exit_K_stepF F17.f17_fop_bs Hbs.
Qed.

(* The UL engine's Exec.evt form of the same run (the premise Tac_slot.sl_run takes, as seg_F17b states it inline),
   from seg_F17b_run_F at ExecF.RNG_all, with a Theorem Labs lane's asan_memcpy_holds_F for the footprint contract; the plain
   contract premise stands where the source's Hypothesis HMC (F17.v:486) stands and is used by nothing.  Every
   rng premise of seg_F17b_run_F is bounded by the run's own premises, so no `_of_F_bounded` form is needed. *)
Lemma seg_F17b_run_of_F : ACPY.asan_memcpy_contract ->
  forall (regs F : bvmap 5 word) (fc : bv 32) (mem : word -> option byte)
         (A phi fr L spz lo : Z) (G : list byte) (s : bool),
  AK.getr regs 2 = Z_to_bv 64 spz -> AK.getr regs 9 = Z_to_bv 64 A -> AK.getr regs 20 = Z_to_bv 64 (1 - b2z s) ->
  AK.getr regs 23 = Z_to_bv 64 phi -> AK.getr regs 26 = Z_to_bv 64 ASAN_K ->
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  q64 mem (A + 232) (if 50 <=? L then 0 else 1) -> q64 mem (A + 176) (fr + 64) ->
  q64 mem (A + 200) (phi + 18) -> q64 mem (A + 32) (fr + 2880) ->
  (50 <= L ->
     s = (RM.blocksum (skipn 18 G) =? 0) /\ length G = 50%nat /\ LMe.bytes_at rsegs mem phi G /\
     addressable mem phi 50 /\ (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
     (phi + 50 <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= phi)) ->
  addressable mem (fr + 2880) 35 -> LF.stk rsegs mem fr (fr + FRAME_BYTES) ->
  AC.GT <= fr -> fr + FRAME_BYTES <= A -> spz <= A ->
  (fr + FRAME_BYTES <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= fr) ->
  LMe.wr_at rsegs mem (A + 88) 32 ->
  LF.stk rsegs mem lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  ro_agree rsegs mem -> asan_cells mem -> shadow_rw mem ->
  UE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R F pc' fc None mem' (AK.seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x823e8 /\
       AK.getr R 2 = AK.getr regs 2 /\ AK.getr R 3 = AK.getr regs 3 /\ AK.getr R 4 = AK.getr regs 4 /\
       AK.getr R 8 = AK.getr regs 8 /\ AK.getr R 9 = AK.getr regs 9 /\ AK.getr R 19 = AK.getr regs 19 /\
       AK.getr R 26 = AK.getr regs 26 /\ AK.getr R 21 = AK.getr regs 21 /\ AK.getr R 23 = AK.getr regs 23 /\
       AK.getr R 24 = AK.getr regs 24 /\ AK.getr R 22 = AK.getr regs 22 /\
       AK.getr R 18 = AK.getr regs 18 /\ AK.getr R 25 = Z_to_bv 64 (fr + 64) /\
       ((mem' = mem /\ f_opens L G = false) \/
        (f_opens L G = true /\
         exists mc : word -> option byte,
           LF.munch [(fr + 2880, fr + 2880 + RF.bat G 26);
                     (spz - ACPY.ASAN_MEMCPY_K, spz)] mem mc /\
           LF.wmono rsegs mem mc /\ ro_agree rsegs mc /\
           LF.stk rsegs mc lo spz /\
           LMe.bytes_at rsegs mc (fr + 2880) (firstn (Z.to_nat (RF.bat G 26)) (skipn 27 G)) /\
           mem' = write_to_mem (write_to_mem mc (LMe.wa (A + 104)) (LMe.le8 (Z_to_bv 64 1)))
                    (LMe.wa (A + 112)) (LMe.le8 (Z_to_bv 64 (RF.bat G 26))))))
    (LM.MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x822a0) fc None mem (AK.seg_rom rsegs)).
Proof.
  intros _ regs F fc mem A phi fr L spz lo G s E2 E9 E20 E23 E26 Happ Q232 Q176 Q200 Q32 HLONG
    Had35 Hstkfr HGTfr HfrA HspA Hplace Hwr HSTK HK HLO HRO HAC HSW.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  assert (HHv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAv : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
  pose proof (Happ (A + 88) ltac:(lia)) as HA88. pose proof (Happ (A + 119) ltac:(lia)) as HA119.
  apply F17.f17_lib_evt, (evtF_evt rsegs RNG_all).
  apply (seg_F17b_run_F RNG_all asan_memcpyF.asan_memcpy_holds_F regs F fc mem A phi fr L spz lo G s
           E2 E9 E20 E23 E26 Happ Q232 Q176 Q200 Q32 HLONG Had35 Hstkfr HGTfr HfrA HspA Hplace Hwr
           HSTK HK HLO HRO HAC HSW).
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - intros HL. destruct (HLONG HL) as (_ & _ & _ & (Hp0 & _ & HpE & _) & _).
    split; [apply rng_all; lia | apply RA.sh_word_rng_all; lia].
  - intros ? ? _ _ _. exact I.
  - apply rng_all; unfold IB.IMG_LO, IB.IMG_HI; lia.
  - apply rng_all; lia.
  - apply RA.sh_word_rng_all; lia.
  - apply rng_all; lia.
  - apply RA.sh_word_rng_all; lia.
Qed.

(* ---- ROUTE (C) TWINS (L3 of glue_seg_F17b; a Theorem Labs lane, the writer of this file, 2026-10-29).  The
   call f17_mc_F and the run seg_F17b_run_F above, each with the region form of the callee's contract,
   ACPFO.asan_memcpy_contract_F_on (a Theorem Labs lane, lib/A/Prog/asan_memcpy_cF_on.v; proved by
   asan_memcpyF_on.asan_memcpy_holds_F_on), in the place of asan_memcpy_contract_F, and the universal premise
   `shadow_rw m` replaced by `SRO.shadow_rw_on R m`, R the callee's own region at the call,
   ACPYO.asan_memcpy_shadow_R a0 a1 a2 (asan_memcpy_c_on.v:25: the aligned shadow-word spans of the source [S, S + N)
   and of the destination [D, D + N)).  Premises, posts and scripts are the originals' but for that premise, the
   contract's name and its post's name (asan_memcpy_post_on: the same conjuncts; its last one, the forall-P
   transport, is not used here).  The region crosses MemNorm.normalize by SRT.shadow_rw_on_normalize (from ro_agree:
   the MemNorm route's condition), in the place of Tac_f17b.f17m_shadow_rw_norm; the contract's mem_inv premise is
   met at normalize m (mem_inv_normalize), as in f17_mc_F.  The run's nine record checks read their metadata bytes
   through `addressable` (F17.f17_shadow), never through shadow_rw: the call is the run's one shadow consumer, so the
   run's region f17b_run_shadow_R is the call's region under the call's path guard (the record opens).  The
   originals above are unchanged. ---- *)
Lemma f17_mc_F_on : forall (RNG : XF.footprint), ACPFO.asan_memcpy_contract_F_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D S N spz lo : Z) (src : list byte),
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 N -> sp = Z_to_bv 64 spz ->
  0 <= S -> AC.GT <= D -> AC.GT <= lo -> spz <= APPMEM_END -> 1 <= N <= 22 ->
  ro_agree rsegs m ->
  LMe.bytes_at rsegs m S src -> length src = Z.to_nat N ->
  LF.stk rsegs m D (D + N) ->
  (S + N <= D \/ D + N <= S) ->
  addressable m S N -> addressable m D N ->
  app_mem (S + N) -> app_mem (D + N) -> app_mem (S + 7) -> app_mem (D + 7) ->
  RT_HI <= D ->
  (D + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= D) -> (S + N <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= S) ->
  LF.stk rsegs m lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  asan_cells m -> SRO.shadow_rw_on (ACPYO.asan_memcpy_shadow_R a0 a1 a2) m ->
  RngBytes.rng_bytes RNG ->
  XF.rng RNG IB.IMG_LO (IB.IMG_HI - IB.IMG_LO) ->
  XF.rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  XF.rng RNG D N -> XF.rng RNG S N ->
  RA.sh_word_rng RNG D N -> RA.sh_word_rng RNG S N ->
  RA.sh_word_rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  evtF rsegs RNG
    (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
       ms = LM.MS (LF.mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (LM.ret_pc ra) fc None m' (LPX.seg_rom rsegs) /\
       LF.munch [(D, D + N); (spz - ACPY.ASAN_MEMCPY_K, spz)] m m' /\ LF.wmono rsegs m m' /\ ro_agree rsegs m' /\
       LF.stk rsegs m' lo spz /\ LMe.bytes_at rsegs m' D src)
    (LM.MS (LF.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACPY.ASAN_MEMCPY) fc None m (LPX.seg_rom rsegs)).
Proof.
  intros RNG HMC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m D S N spz lo src E0 E1 E2 Esp0 HS0 HDGT HloGT HspE HN HRO HBS HLs HSTD HDS HAS HAD HapSN HapDN
    HapS7 HapD7 HRT HDW HSW HSTK HloK Hlo HAC HSWr GRB GIMG GSTK GD GS GSD GSS GSK.
  subst a0 a1 a2 sp.
  assert (HGT0 : 0 <= AC.GT <= HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia).
  pose proof HapDN as HapDN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapDN'.
  pose proof HapSN as HapSN'. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HapSN'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply LM.unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply LM.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply LM.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spz) = spz)
    by (apply LM.unsigned_lit; unfold ACPY.ASAN_MEMCPY_K, HIGHMEM_BEG, APPMEM_END in *; lia).
  destruct (Tac_f17b.f17m_stk_cb m D (D + N) D (Z.to_nat N) HSTD ltac:(lia) ltac:(lia)) as (junk & Hjl & HRW).
  pose proof (mem_rel_normalize rsegs m HRO) as REL0.
  pose proof HMC as HM. unfold ACPFO.asan_memcpy_contract_F_on in HM. cbv zeta in HM.
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (LPX.seg_rom rsegs) HRO).
    eapply HM with (RNG := RNG) (src := src) (junk := junk) (lo := lo).
    all: rewrite ?ED, ?ES, ?EN, ?Esp.
    - exact (bytes_at_normalize rsegs m _ _ HRO HBS).
    - exact HLs.
    - exact (Tac_f17b.f17m_rw_norm m _ _ HRO HDGT HRW).
    - right. destruct HDS as [Hd|Hd]; [left; exact Hd | right; exact Hd].
    - lia.
    - exact (Tac_f17b.f17m_addr_norm m _ _ HRO HAS).
    - exact (Tac_f17b.f17m_addr_norm m _ _ HRO HAD).
    - right. exact HapSN.
    - right. exact HapDN.
    - right. split; [exact HapS7 | exact HapD7].
    - right. exact HRT.
    - exact HDW.
    - exact HSW.
    - apply (Tac_f17b.f17m_stk_norm m _ _ HRO HloGT HSTK).
    - exact HloK.
    - exact Hlo.
    - exact HspE.
    - exact (Tac_f17b.f17m_cells_norm m HRO HAC).
    - exact (SRT.shadow_rw_on_normalize _ m HRO HSWr).
    - exact (mem_inv_normalize rsegs m).
    - exact GRB.
    - exact GIMG.
    - exact GSTK.
    - exact GD.
    - exact GS.
    - exact GSD.
    - exact GSS.
    - exact GSK. }
  intros ms' (s0' & Hp & REL & SAME). unfold ACPYO.asan_memcpy_post_on in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MUc & WMc & MIc & STc & RWc & BSc & ACc & SWc).
  subst s0'.
  rewrite ED, EN, Esp in MUc. rewrite Esp in STc. rewrite ED, EN in RWc.
  destruct (Tac_f17b.f17m_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
  split; [exact Ems|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME MUc)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem ms') m0' REL0 HREL SAME WMc)|].
  split; [exact (ro_agree_of_mem_rel rsegs (ms_mem ms') m0' HREL)|].
  split; [exact (Tac_f17b.f17m_stk_back (ms_mem ms') m0' _ _ HREL STc)|].
  exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m0' _ _ HREL) (Tac_f17b.f17m_cb_bytes m0' _ _ _ RWc)).
Qed.

(* The run's region: the call's region at the call (a0 = fr + 2880, a1 = phi + 27, a2 = gg[26]; the run's a0 / a1 /
   a2 at 0x823d4) under the call's path guard, the record opens (f_opens L G = true; on the eight other arms the run
   reads and writes no shadow byte). *)
Definition f17b_run_shadow_R (L : Z) (G : list byte) (phi fr : Z) (a : Z) : Prop :=
  f_opens L G = true /\
  ACPYO.asan_memcpy_shadow_R (Z_to_bv 64 (fr + 2880)) (Z_to_bv 64 (phi + 27)) (Z_to_bv 64 (RF.bat G 26)) a.

Lemma seg_F17b_run_F_on : forall (RNG : XF.footprint), ACPFO.asan_memcpy_contract_F_on ->
  forall (regs F : bvmap 5 word) (fc : bv 32) (mem : word -> option byte)
         (A phi fr L spz lo : Z) (G : list byte) (s : bool),
  (* the cut's registers: sp, s1 = A, s4 = 1 - sum_ok, s7 = phi, s10 = ASAN_K *)
  AK.getr regs 2 = Z_to_bv 64 spz -> AK.getr regs 9 = Z_to_bv 64 A -> AK.getr regs 20 = Z_to_bv 64 (1 - b2z s) ->
  AK.getr regs 23 = Z_to_bv 64 phi -> AK.getr regs 26 = Z_to_bv 64 ASAN_K ->
  (* the spill window and the spills the run reads *)
  (forall a, A + 88 <= a < A + 120 -> HIGHMEM_BEG <= a < APPMEM_END) ->
  q64 mem (A + 232) (if 50 <=? L then 0 else 1) -> q64 mem (A + 176) (fr + 64) ->
  q64 mem (A + 200) (phi + 18) -> q64 mem (A + 32) (fr + 2880) ->
  (* the record, on a long frame only (a short frame takes the guard exit at once) *)
  (50 <= L ->
     s = (RM.blocksum (skipn 18 G) =? 0) /\ length G = 50%nat /\ LMe.bytes_at rsegs mem phi G /\
     addressable mem phi 50 /\ (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
     (phi + 50 <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= phi)) ->
  (* the frame object first.sroa.7 and the frame *)
  addressable mem (fr + 2880) 35 -> LF.stk rsegs mem fr (fr + FRAME_BYTES) ->
  AC.GT <= fr -> fr + FRAME_BYTES <= A -> spz <= A ->
  (fr + FRAME_BYTES <= spz - ACPY.ASAN_MEMCPY_K \/ spz <= fr) ->
  LMe.wr_at rsegs mem (A + 88) 32 ->
  (* the callee's stack window (F17.f17_tail's own premises) and the runtime facts it asks *)
  LF.stk rsegs mem lo spz -> lo + ACPY.ASAN_MEMCPY_K <= spz -> HIGHMEM_BEG <= lo ->
  ro_agree rsegs mem -> asan_cells mem -> SRO.shadow_rw_on (f17b_run_shadow_R L G phi fr) mem ->
  (* the footprint *)
  XF.rng RNG (A + 232) 8 -> XF.rng RNG (A + 176) 8 -> XF.rng RNG (A + 200) 8 -> XF.rng RNG (A + 32) 8 ->
  XF.rng RNG (A + 88) 32 ->
  (50 <= L -> XF.rng RNG phi 50 /\ RA.sh_word_rng RNG phi 50) ->
  RngBytes.rng_bytes RNG -> XF.rng RNG IB.IMG_LO (IB.IMG_HI - IB.IMG_LO) ->
  XF.rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  RA.sh_word_rng RNG (spz - ACPY.ASAN_MEMCPY_K) ACPY.ASAN_MEMCPY_K ->
  XF.rng RNG (fr + 2880) 22 -> RA.sh_word_rng RNG (fr + 2880) 22 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R F pc' fc None mem' (AK.seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x823e8 /\
       AK.getr R 2 = AK.getr regs 2 /\ AK.getr R 3 = AK.getr regs 3 /\ AK.getr R 4 = AK.getr regs 4 /\
       AK.getr R 8 = AK.getr regs 8 /\ AK.getr R 9 = AK.getr regs 9 /\ AK.getr R 19 = AK.getr regs 19 /\
       AK.getr R 26 = AK.getr regs 26 /\ AK.getr R 21 = AK.getr regs 21 /\ AK.getr R 23 = AK.getr regs 23 /\
       AK.getr R 24 = AK.getr regs 24 /\ AK.getr R 22 = AK.getr regs 22 /\
       AK.getr R 18 = AK.getr regs 18 /\ AK.getr R 25 = Z_to_bv 64 (fr + 64) /\
       ((mem' = mem /\ f_opens L G = false) \/
        (f_opens L G = true /\
         exists mc : word -> option byte,
           LF.munch [(fr + 2880, fr + 2880 + RF.bat G 26);
                     (spz - ACPY.ASAN_MEMCPY_K, spz)] mem mc /\
           LF.wmono rsegs mem mc /\ ro_agree rsegs mc /\
           LF.stk rsegs mc lo spz /\
           LMe.bytes_at rsegs mc (fr + 2880) (firstn (Z.to_nat (RF.bat G 26)) (skipn 27 G)) /\
           mem' = write_to_mem (write_to_mem mc (LMe.wa (A + 104)) (LMe.le8 (Z_to_bv 64 1)))
                    (LMe.wa (A + 112)) (LMe.le8 (Z_to_bv 64 (RF.bat G 26))))))
    (LM.MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x822a0) fc None mem (AK.seg_rom rsegs)).
Proof.
  intros RNG MCPY regs F fc mem A phi fr L spz lo G s E2 E9 E20 E23 E26 Happ Q232 Q176 Q200 Q32 HLONG
    Had35 Hstkfr HGTfr HfrA HspA Hplace Hwr HSTK HK HLO HRO HAC HSW
    G232 G176 G200 G32 G88 GLONG GRB GIMG GSTK GSSTK GD GSD.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB.
  assert (HAr0 : HIGHMEM_BEG <= A + 88 /\ A + 120 <= APPMEM_END)
    by (split; [exact (proj1 (Happ (A + 88) ltac:(lia))) | pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia]).
  assert (HHv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAv : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HKv : ACPY.ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hs9r : Sem.reg_get regs (9%bv) = Z_to_bv 64 A) by (rewrite <- E9; unfold AK.getr; reflexivity).
  assert (Hs23r : Sem.reg_get regs (23%bv) = Z_to_bv 64 phi) by (rewrite <- E23; unfold AK.getr; reflexivity).
  assert (Hs26r : Sem.reg_get regs (26%bv) = Z_to_bv 64 ASAN_K) by (rewrite <- E26; unfold AK.getr; reflexivity).
  assert (IDW : bvmap_set (9%bv) (Z_to_bv 64 A)
                 (bvmap_set (23%bv) (Z_to_bv 64 phi)
                   (bvmap_set (26%bv) (Z_to_bv 64 ASAN_K) (Regs6ss.mkR_of regs)))
                = Regs6ss.mkR_of regs)
    by (rewrite <- Hs9r, <- Hs23r, <- Hs26r; cbn; reflexivity).
  rewrite <- IDW.
  pose proof (f17bF_rd8 mem (A + 176) (fr + 64) Q176) as HR176.
  destruct (50 <=? L) eqn:Ebig.
  2:{ (* short arm: [s1+232] = 1, so a0 = 1 | s4 has bit 0 set and `bnez a0, 0x823e4` is TAKEN, into the join
         `ld s9,176(s1)` and on to 0x823e8 (memory unchanged) *)
      pose proof (f17bF_rd8 mem (A + 232) 1 Q232) as HR232.
      step. (* 0x822a0: ld a0,232(s1) : a0 = 1 *)
      step. (* 0x822a4: or a0,a0,s4 *)
      step. (* 0x822a8: bnez a0,823e4 -- taken *)
      or1_bnez_tkF.
      exit_K_stepF F17.f17_fop_len Ebig. }
  (* long arm: 50 <= L, so the record facts hold *)
  assert (HfL : 50 <= L) by (apply Z.leb_le; exact Ebig).
  destruct (HLONG HfL) as (Hs & Hrblen & Hrbb & Haddr & Hfrph & Hphsp).
  destruct (GLONG HfL) as (Grec & Gsrec).
  pose proof (f17bF_rd8 mem (A + 232) 0 Q232) as HR232.
  step. (* 0x822a0: ld a0,232(s1) : 0 on the long arm *)
  step. (* 0x822a4: or a0,a0,s4 *)
  step. (* 0x822a8: bnez a0,823e4 : NOT taken exactly when s4 = 0, i.e. the block sum is 0 *)
  match goal with
  | |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with
      | context [Z.lor 0 (bv_unsigned (Sem.reg_get ?R ?r))] =>
          assert (Hs20r : Sem.reg_get R r = Z_to_bv 64 (1 - b2z s)) by
            (transitivity (Sem.reg_get regs r);
             [ symmetry; apply Regs6ss.mkR_of_eqv; reflexivity
             | rewrite <- E20; unfold AK.getr; reflexivity ])
      end
  end.
  destruct s eqn:ESUM;
    (match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
       first [ replace c with true by (symmetry; rewrite Hs20r; vm_compute; reflexivity)
             | replace c with false by (symmetry; rewrite Hs20r; vm_compute; reflexivity) ]
     end; cbv_concl_iotaF).
  - (* s4 = 0: the guard's branch is not taken and the opens_record body at 0x822ac runs; its nine byte tests
       decide f_opens *)
    assert (Hbs : (RM.blocksum (skipn 18 G) =? 0) = true) by (symmetry; exact Hs).
    pose proof Haddr as Haddr'. destruct Haddr' as (Hphi0 & _ & HphiE & _).
    assert (RSH : forall k, 16 <= k <= 26 -> XF.rng RNG (Z.shiftr (phi + k) 3 + ASAN_K) 1)
      by (intros k Hk; apply (f17bF_sh_byte RNG phi 50 (phi + k)); [lia | lia | exact Gsrec]).
    (* check 1 (0x822ac .. 0x822c8): phi+16, const 205 *)
    step. (* 0x822ac: addi a0,s7,16 *)
    shadowcheckF phi mem Haddr RSH 16.
    frbcF phi mem G Hrbb 16 205 Hb16 F17.f17_fop_16. clr1F.
    (* check 2 (0x822cc .. 0x822ec): phi+17, const 234; `ld a3,200(s1)` (the phi + 18 pointer) between the
       shadow load and its bnez *)
    pose proof (f17bF_rd8 mem (A + 200) (phi + 18) Q200) as HR200.
    step. (* 0x822cc: addi a0,s7,17 *)
    step. step. (* srli a1,a0,3 ; add a1,a1,s10 *)
    rewrite (LM.unsigned_lit (phi + 17)) by (unfold APPMEM_END in HphiE; lia).
    assert (Had17 : addressable mem (phi + 17) 1) by (apply (addressable_sub mem phi 50 17 1 Haddr); lia).
    destruct (F17.f17_shadow mem (phi + 17) Had17) as (b17 & HRsh17 & OK17 & BD17).
    pose proof (RSH 17 ltac:(lia)) as R17.
    step. (* 0x822d8: lb a1,0(a1) *)
    step. (* 0x822dc: ld a3,200(s1) : a3 = phi + 18 *)
    step. (* 0x822e0: bnez a1,.. *)
    convergeF (Z_to_bv 5 12) (phi + 17) b17 OK17 BD17.
    frbcF phi mem G Hrbb 17 234 Hb17 F17.f17_fop_17. clr1F.
    (* check 3 (0x822f0 .. 0x82308): the byte at a3 = phi+18, const 4; the shadow byte goes to a0 *)
    step. step. (* srli a0,a3,3 ; add a0,a0,s10 *)
    rewrite (LM.unsigned_lit (phi + 18)) by (unfold APPMEM_END in *; lia).
    assert (Had18 : addressable mem (phi + 18) 1) by (apply (addressable_sub mem phi 50 18 1 Haddr); lia).
    destruct (F17.f17_shadow mem (phi + 18) Had18) as (b18 & HRsh18 & OK18 & BD18).
    pose proof (RSH 18 ltac:(lia)) as R18.
    step. (* 0x822f8: lb a0,0(a0) *)
    step. (* 0x822fc: bnez a0,.. *)
    convergeF (Z_to_bv 5 11) (phi + 18) b18 OK18 BD18.
    frbcF phi mem G Hrbb 18 4 Hb18 F17.f17_fop_18. clr1F.
    (* check 4: phi+19, const 1 *)
    step. shadowcheckF phi mem Haddr RSH 19. frbcF phi mem G Hrbb 19 1 Hb19 F17.f17_fop_19. clr1F.
    (* check 5: phi+22, bnez a0 (exit if != 0) *)
    step. shadowcheckF phi mem Haddr RSH 22. frbnzcF phi mem G Hrbb 22 Hb22 F17.f17_fop_22. clr1F.
    (* check 6: phi+23, const 2 *)
    step. shadowcheckF phi mem Haddr RSH 23. frbcF phi mem G Hrbb 23 2 Hb23 F17.f17_fop_23. clr1F.
    (* check 7: phi+24, bnez a0 *)
    step. shadowcheckF phi mem Haddr RSH 24. frbnzcF phi mem G Hrbb 24 Hb24 F17.f17_fop_24. clr1F.
    (* check 8: phi+25, const 254 *)
    step. shadowcheckF phi mem Haddr RSH 25. frbcF phi mem G Hrbb 25 254 Hb25 F17.f17_fop_25. clr1F.
    (* check 9: phi+26, range check (b[8] - 23 >=u -22) *)
    step. shadowcheck_bltF phi mem Haddr RSH 26.
    assert (Hrr26 : ov_read_bytes rsegs mem (LMe.wa (phi + 26)) 1
                      = Some (firstn 1 (skipn (Z.to_nat 26) G))).
    { pose proof (LMe.bytes_at_ov_read rsegs mem phi G (Z.to_nat 26) 1 Hrbb ltac:(lia)) as H.
      replace (phi + Z.of_nat (Z.to_nat 26)) with (phi + 26) in H by lia. exact H. }
    step. (* lbu s9,0(a0) *)
    step. (* addi a0,s9,-23 *)
    step. (* li a1,-22 *)
    step. (* bltu a0,a1,823e4 : the range test 1 <= gg[26] <= 22 *)
    destruct ((1 <=? RF.bat G 26) && (RF.bat G 26 <=? 22)) eqn:Hb26;
    [ match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by
          (symmetry; rewrite (F17.f17_bltu_val G 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
      cbv_concl_iotaF
    | match goal with |- evtF _ _ _ (LM.MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by
          (symmetry; rewrite (F17.f17_bltu_val G 26 ltac:(lia) ltac:(lia)), Hb26; reflexivity) end;
      cbv_concl_iotaF; exit_K_stepF F17.f17_fop_26 Hb26 ].
    clr1F.
    (* ---- the record opens: 0x823c8 .. 0x823e4 is F17.f17_tail, composed here from F17F.v's two stretches and
       the call (f17_mc_F_on), as F17F.f17_tail_of_pre_post composes them at RNG_all. ---- *)
    assert (H50t : (50 <=? L) = true) by exact Ebig.
    assert (Hop : f_opens L G = true)
      by exact (F17.f17_fopens_true L G H50t Hb16 Hb17 Hb18 Hb19 Hb22 Hb23 Hb24 Hb25 Hb26 Hbs).
    assert (Hn26 : 1 <= RF.bat G 26 <= 22)
      by (apply andb_prop in Hb26 as (Hl1 & Hl2); apply Z.leb_le in Hl1; apply Z.leb_le in Hl2; lia).
    set (n := RF.bat G 26) in *.
    set (src := firstn (Z.to_nat n) (skipn 27 G)).
    pose proof (ba_sub mem phi G 27 (Z.to_nat n) Hrbb ltac:(rewrite Hrblen; lia)) as Hsrc.
    replace (phi + Z.of_nat 27) with (phi + 27) in Hsrc by lia.
    fold src in Hsrc.
    assert (Hsrcl : length src = Z.to_nat n)
      by (unfold src; rewrite length_firstn, length_skipn, Hrblen; lia).
    assert (HadS : addressable mem (phi + 27) n)
      by (apply (addressable_sub mem phi 50 27 n Haddr); lia).
    assert (HadD : addressable mem (fr + 2880) n).
    { pose proof (addressable_sub mem (fr + 2880) 35 0 n Had35 ltac:(lia) ltac:(lia) ltac:(lia)) as HadD0.
      rewrite Z.add_0_r in HadD0. exact HadD0. }
    assert (HstD : LF.stk rsegs mem (fr + 2880) (fr + 2880 + n)).
    { destruct (LF.stk_split rsegs mem fr (fr + 2880) (fr + FRAME_BYTES) Hstkfr ltac:(lia)) as (_ & Hs1').
      destruct (LF.stk_split rsegs mem (fr + 2880) (fr + 2880 + n) (fr + FRAME_BYTES) Hs1' ltac:(lia))
        as (Hs2' & _).
      exact Hs2'. }
    assert (Hdj : phi + 27 + n <= fr + 2880 \/ fr + 2880 + n <= phi + 27) by (destruct Hfrph; lia).
    assert (HappP : forall a, phi <= a < phi + 50 -> app_mem a).
    { intros a Ha. pose proof Haddr as (_ & _ & _ & Hab). destruct (Hab (a - phi) ltac:(lia)) as (Hap & _).
      replace (phi + (a - phi)) with a in Hap by lia. exact Hap. }
    assert (HappD : forall a, fr + 2880 <= a < fr + 2915 -> app_mem a).
    { intros a Ha. pose proof Had35 as (_ & _ & _ & Hab). destruct (Hab (a - (fr + 2880)) ltac:(lia)) as (Hap & _).
      replace (fr + 2880 + (a - (fr + 2880))) with a in Hap by lia. exact Hap. }
    pose proof (HappP (phi + 49) ltac:(lia)) as Hap49. unfold app_mem, LOWMEM_END in Hap49.
    (* s9 holds the loaded byte raw; f17_tail_pre_F names it as the model's gg[26] *)
    rewrite (F17.f17_byte_word G 26 ltac:(lia) ltac:(lia)). fold n.
    (* stretch 1: 0x823c8 .. the callee entry (F17F.PF.f17_tail_pre_F) *)
    match goal with |- evtF _ _ _ (LM.MS ?R0 ?F0 _ ?fc0 _ _ _) =>
      eapply evtF_cut;
      [ apply (F17F.PF.f17_tail_pre_F RNG (Sem.reg_get R0 1) (Sem.reg_get R0 2) (Sem.reg_get R0 3) (Sem.reg_get R0 4)
                (Sem.reg_get R0 5) (Sem.reg_get R0 6) (Sem.reg_get R0 7) (Sem.reg_get R0 8)
                (Sem.reg_get R0 9) (Sem.reg_get R0 10) (Sem.reg_get R0 11) (Sem.reg_get R0 12)
                (Sem.reg_get R0 13) (Sem.reg_get R0 14) (Sem.reg_get R0 15) (Sem.reg_get R0 16)
                (Sem.reg_get R0 17) (Sem.reg_get R0 18) (Sem.reg_get R0 19) (Sem.reg_get R0 20)
                (Sem.reg_get R0 21) (Sem.reg_get R0 22) (Sem.reg_get R0 23) (Sem.reg_get R0 24)
                (Sem.reg_get R0 25) (Sem.reg_get R0 26) (Sem.reg_get R0 27) (Sem.reg_get R0 28)
                (Sem.reg_get R0 29) (Sem.reg_get R0 30) (Sem.reg_get R0 31) F0 fc0 mem A phi fr n)
      | ] end;
      [ reflexivity | reflexivity | reflexivity | exact Q32 | exact G32 | ].
    intros ms' ->.
    (* the call (f17_mc_F_on), with a0 = fr + 2880, a1 = phi + 27, a2 = n, ra = 0x823d8; its region premise is the
       run's region at Hop *)
    eapply evtF_cut.
    { eapply (f17_mc_F_on RNG MCPY) with (D := fr + 2880) (S := phi + 27) (N := n) (spz := spz) (lo := lo)
        (src := src);
        [ reflexivity | reflexivity | reflexivity | exact E2 | lia | lia | lia | lia | exact Hn26 | exact HRO
        | exact Hsrc | exact Hsrcl | exact HstD | exact Hdj | exact HadS | exact HadD
        | apply HappP; lia | apply HappD; lia
        | replace (phi + 27 + 7) with (phi + 34) by lia; apply HappP; lia
        | replace (fr + 2880 + 7) with (fr + 2887) by lia; apply HappD; lia
        | unfold RT_HI; lia | destruct Hplace; [left|right]; lia | destruct Hphsp; [left|right]; lia
        | exact HSTK | exact HK | exact HLO | exact HAC
        | apply (SRO.shadow_rw_on_mono (f17b_run_shadow_R L G phi fr) _ mem);
            [intros a Ha; unfold f17b_run_shadow_R; split; [exact Hop | exact Ha] | exact HSW]
        | exact GRB | exact GIMG | exact GSTK
        | apply (rng_sub' RNG (fr + 2880) 22); [exact GD | lia]
        | apply (rng_sub' RNG phi 50); [exact Grec | lia]
        | apply (f17bF_sh_sub RNG (fr + 2880) 22); [lia | lia | lia | exact GSD]
        | apply (f17bF_sh_sub RNG phi 50); [lia | lia | lia | exact Gsrec]
        | exact GSSTK ]. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc
                & E & MU & WM & RO' & ST' & Bsrc).
    subst ms'.
    replace (LM.ret_pc (Z_to_bv 64 533464)) with (Z_to_bv 64 0x823d8)
      by (symmetry; apply LM.ret_pc_even; [clear; lia | reflexivity]).
    (* stretch 2: the return block 0x823d8 .. 0x823e8 (F17F.PF.f17_tail_post_F), from the canonical form of the state
       the callee returned in *)
    match goal with |- evtF _ _ _ (LM.MS (LF.mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15
                                            ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30
                                            ?x31) _ _ _ _ _ _) =>
      rewrite <- (F17F.PF.f17F_mkR_of_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    end.
    eapply evtF_mono.
    { eapply (F17F.PF.f17_tail_post_F RNG _ mc _ _ _ _ _ _ _ _ _ _ _ _ F fc mem A phi fr n spz lo src);
        try reflexivity; try assumption; lia. }
    intros ms' (ra' & a0' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4''
                & t5'' & t6'' & mc' & -> & MUc & WMc & ROc & STc & BSc).
    hnf. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 13 (split; [regeqF|]).
    right. split; [exact Hop|]. exists mc'.
    split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|]. split; [exact STc|]. split; [exact BSc|].
    reflexivity.
  - (* s4 <> 0: the block sum is nonzero, so the record does not open; the guard's bnez was taken into the
       join 0x823e4 (memory unchanged) *)
    assert (Hbs : (RM.blocksum (skipn 18 G) =? 0) = false) by (symmetry; exact Hs).
    exit_K_stepF F17.f17_fop_bs Hbs.
Qed.

End PF.

(* ---- THE SOURCE TIE (the pin of the extracted run, see the header): F17.seg_F17b's statement, proved by
   seg_F17b's own script (Seg/F17.v :1386-1426 and :1700-2000 at d65d18383b1) with its inline run discharged from
   PF.seg_F17b_run_of_F.  Section Src restates F17.v's Section F17 (:475-486); after it closes, seg_F17b_src0 takes
   the same arguments as F17.seg_F17b, and seg_F17b_src is stated as `type of F17.seg_F17b`.  The moved section
   lemmas of F17.v (fra_spill, f17_blk_out, f17_cp_fra, ent_store1, fra_store1, to_exit_823e8) take their section
   arguments B APIf ra (empty FF) explicitly here; nothing else in the script changes. ---- *)
Section Src.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState} {LS : lib_shape} {rc : AM.RunCeil}.
Variable B : AO.malloc_syms.
Variable APIf : forall rc : AM.RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HMC : ACPY.asan_memcpy_contract.

Lemma seg_F17b_src0 : forall j : nat,
  Hat B APIf ra (Inv_A823e8_at B APIf ra) j -> Hat B APIf ra (Inv_A822a0_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (eq_refl : FRAME_BYTES = 3136) as HFB. pose proof (eq_refl : FRAME_SHADOW = 392) as HFS.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hj & HHB & HFLSI & HLK &
    Hs7 & Hs22 & Hrec40 & (A & Hs1 & Hv232 & Hb192 & Hq136 & Hq120 & Hq176 & Happ & Hw240 & Hs24 & Hrecg &
    HL12) & Hs18 & Hrecb & H152 & H280 & HIFS3 & Hs20).
  subst c.
  rewrite SEGS.
  (* FRA's spill-base / frame placement and the writable spill window (fra_spill). *)
  assert (Hs9g : AK.getr regs (9%bv) = Z_to_bv 64 A) by (unfold rg in Hs1; exact Hs1).
  destruct (F17.fra_spill B APIf ra g fr _ regs mem md A HFRA Hs9g Happ) as (HspA & HfrA & Hwr & HWlo & HWhi).
  assert (Hdisj : A + 416 <= fr \/ fr + FRAME_BYTES <= A) by (right; exact HfrA).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hrest).
  eapply (sl_run regs (Z_to_bv 64 0x822a0) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x823e8 /\
       Sem.reg_get R 2 = Sem.reg_get regs 2 /\ Sem.reg_get R 3 = Sem.reg_get regs 3 /\ Sem.reg_get R 4 = Sem.reg_get regs 4 /\
       Sem.reg_get R 8 = Sem.reg_get regs 8 /\ Sem.reg_get R 9 = Sem.reg_get regs 9 /\ Sem.reg_get R 19 = Sem.reg_get regs 19 /\
       Sem.reg_get R 26 = Sem.reg_get regs 26 /\ Sem.reg_get R 21 = Sem.reg_get regs 21 /\ Sem.reg_get R 23 = Sem.reg_get regs 23 /\
       Sem.reg_get R 24 = Sem.reg_get regs 24 /\ Sem.reg_get R 22 = Sem.reg_get regs 22 /\
       Sem.reg_get R 18 = Sem.reg_get regs 18 /\ Sem.reg_get R 25 = Z_to_bv 64 (fr + 64) /\
       (* The memory changes exactly on the arm where the record opens (f_opens true): the memcpy at 0x823d4
          writes the first fragment's body into first.sroa.7 = fr + 2880 (and its own stack scratch), then
          0x823dc / 0x823e0 store have = 1 and n = gg[26] into [A + 104] / [A + 112]. On every other arm the
          memory is untouched. The intermediate memory mc is the call's; what the continuation needs of it is
          named here (the copy's write set, ro_agree, the sp-anchored stack window, the copied bytes), since the
          call's own post is not available past the run. *)
       ((mem' = mem /\ f_opens (flen g j) (t_g (g_in g) j) = false) \/
        (f_opens (flen g j) (t_g (g_in g) j) = true /\
         exists mc : word -> option byte,
           LF.munch [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                     (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs)] mem mc /\
           LF.wmono rsegs mem mc /\ ro_agree rsegs mc /\
           UF.stk rsegs mc (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
           UM.bytes_at rsegs mc (fr + 2880)
             (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j))) /\
           mem' = write_to_mem (write_to_mem mc (UM.wa (A + 104)) (UM.le8 (Z_to_bv 64 1)))
                    (UM.wa (A + 112)) (UM.le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the inline run (F17.v :1427-1699): PF.seg_F17b_run_of_F, the extracted footprint run at RNG_all in the UL
       engine's evt; its premises are the facts the source's stepping reads off the cut and FRA, taken by the
       source's own steps (:1428-1453, :1494-1501, :1606-1638) *)
    assert (HAr0 : HIGHMEM_BEG <= A + 88 /\ A + 120 <= APPMEM_END)
      by (split; [exact (proj1 (Happ (A + 88) ltac:(lia)))
                 | pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia]).
    assert (Hq32 : q64 mem (A + 32) (fr + 2880)).
    { pose proof HFLSI as HP. unfold FLSI, FLSH, PRO in HP.
      destruct HP as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P32) & _) & _).
      exact (F17.f17_spill_q regs mem 32 (fr + 2880) A P32 Hs1
               ltac:(clear - HAr0; unfold HIGHMEM_BEG in *; lia) ltac:(lia)
               ltac:(clear - HAr0; unfold APPMEM_END in *; lia)). }
    pose proof HIFS3 as (_ & _ & (_ & _ & _ & Hbad35 & _)).
    pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
    pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
    pose proof (fra_stk B APIf ra g fr _ regs mem md HFRA) as Hstkfr.
    pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
    pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
    pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
    pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH)
      as Hstkhigh.
    destruct Hrest as (Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hrest2).
    assert (Hsp2 : AK.getr regs 2 = Z_to_bv 64 (AC.aspZ regs)) by (rewrite Haspz; rewrite <- Hr2; reflexivity).
    pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K; lia)) as HplK.
    assert (HplK' : fr + FRAME_BYTES <= AC.aspZ regs - ACPY.ASAN_MEMCPY_K \/ AC.aspZ regs <= fr)
      by (destruct HplK as [P|P]; [left|right]; lia).
    assert (HLONG : 50 <= flen g j ->
       t_sum_ok (g_in g) j = (RM.blocksum (skipn 18 (t_g (g_in g) j)) =? 0) /\ length (t_g (g_in g) j) = 50%nat /\
       UM.bytes_at rsegs mem phi (t_g (g_in g) j) /\ addressable mem phi 50 /\
       (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
       (phi + 50 <= AC.aspZ regs - ACPY.ASAN_MEMCPY_K \/ AC.aspZ regs <= phi)).
    { intros HfL.
      assert (Ebig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; unfold flen in HfL; exact HfL).
      destruct (Hrec40 HfL) as (Haddr & _). destruct (Hrecb HfL) as (Hrbb & _ & _).
      assert (Hblkm : forall x, phi <= x < phi + 50 ->
                x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= x < fr + FRAME_BYTES)).
      { intros x Hx. apply (F17.f17_blk_out B APIf ra g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA).
        - unfold hb1. apply in_or_app. left. left. reflexivity.
        - unfold AC.a_size. lia. }
      split; [symmetry; exact (F17.f17_sumok_bs (g_in g) j Ebig)|].
      split; [apply f18_t_g_length|].
      split; [exact Hrbb|]. split; [exact Haddr|].
      split.
      { destruct (Z_le_gt_dec (phi + 50) fr) as [D1|D1]; [left; exact D1|].
        destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [D2|D2]; [right; exact D2|].
        exfalso. destruct (Hblkm (Z.max phi fr) ltac:(lia)) as (_ & Hnf). apply Hnf. lia. }
      pose proof (Hblkm (phi + 49) ltac:(lia)) as (Hphilo & _).
      left. unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K in Hwlo |- *. lia. }
    assert (HK' : AC.aspZ regs - FN_STACK + ACPY.ASAN_MEMCPY_K <= AC.aspZ regs)
      by (unfold FN_STACK, AF.SLOT_STACK, ACPY.ASAN_MEMCPY_K; lia).
    assert (HLO' : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK) by lia.
    eapply UE.evt_mono.
    { exact (PF.seg_F17b_run_of_F HMC regs fp_regs fp_csr mem A phi fr (flen g j) (AC.aspZ regs)
               (AC.aspZ regs - FN_STACK) (t_g (g_in g) j) (t_sum_ok (g_in g) j)
               Hsp2 Hs9g Hs20 Hs7 Hr26 Happ Hv232 Hq176 Hb192 Hq32 HLONG Hbad35 Hstkfr HGTfr HfrA HspA HplK' Hwr
               Hwstk HK' HLO' Hro HAC0 HSW0). }
    intros ms (R & pc' & mem' & E & HKr). exists R, pc', mem'. split; [rewrite E; reflexivity | exact HKr].
  - (* continuation: assemble the official F18 entry cut Inv_A823e8_at (turn j) at 0x823e8 from K *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E21 & E23 & E24 & E22 & E18 & E25 &
      Hmem) Hreg Hmat.
    subst pc'.
    assert (G2 : AK.getr regs' 2 = AK.getr regs 2)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G3 : AK.getr regs' 3 = AK.getr regs 3)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G4 : AK.getr regs' 4 = AK.getr regs 4)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G8 : AK.getr regs' 8 = AK.getr regs 8)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G9 : AK.getr regs' 9 = AK.getr regs 9)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G19 : AK.getr regs' 19 = AK.getr regs 19)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G21 : AK.getr regs' 21 = AK.getr regs 21)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G23 : AK.getr regs' 23 = AK.getr regs 23)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G24 : AK.getr regs' 24 = AK.getr regs 24)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G22 : AK.getr regs' 22 = AK.getr regs 22)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G26 : AK.getr regs' 26 = AK.getr regs 26)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G18 : AK.getr regs' 18 = AK.getr regs 18)
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (G25 : AK.getr regs' 25 = Z_to_bv 64 (fr + 64))
      by ((etransitivity; [apply Hreg|]); unfold AK.getr; cbn [bv_eqb negb]; eassumption).
    assert (ASP : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite G2; reflexivity).
    assert (HAlo : HIGHMEM_BEG <= A + 88) by exact (proj1 (Happ (A + 88) ltac:(lia))).
    assert (HAhi : A + 120 <= APPMEM_END) by (pose proof (Happ (A + 119) ltac:(lia)) as Hap; lia).
    assert (HAr : 0 <= A < 2 ^ 64) by (clear - HAlo HAhi; unfold HIGHMEM_BEG, APPMEM_END in *; lia).
    assert (HAtop : A + 120 <= 2 ^ 64) by (clear - HAhi; unfold APPMEM_END in *; lia).
    pose proof (eq_refl : ACPY.ASAN_MEMCPY_K = 2224) as HKv.
    pose proof (eq_refl : AF.SLOT_STACK = 1048576) as HSS.
    pose proof (eq_refl : FN_STACK = AF.SLOT_STACK - 4096) as HFN.
    pose proof (eq_refl : HIGHMEM_BEG = 0x10007fff8000) as HHBv.
    pose proof (eq_refl : APPMEM_END = 0x800000000000) as HAEv.
    pose proof (eq_refl : AC.GT = 0x5fe000) as HGTv.
    pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
    pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hplace & _).
    pose proof (Hplace ACPY.ASAN_MEMCPY_K ltac:(lia)) as HplK.
    pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
    pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH)
      as Hstkhigh.
    (* Both exits: a write set W whose bytes lie in the frame object first.sroa.7 [fr + 2880, fr + 2902), in the
       callee's stack scratch [sp - K, sp) or in the first-fragment spills [A + 104, A + 120). W is app memory, the
       frame stays byte-backed, FRA and ENT move (f17_cp_fra across the copy, fra_store1 / ent_store1 across the
       two spill stores, then sl_fra_move / ent_mat), and LT = IFS g fr (S j) holds of turn S j. *)
    assert (COM : exists W, LF.munch W mem mem' /\ LF.wmono rsegs mem mem' /\ all_app W /\
                  (forall x, ~ LF.outside W x ->
                     (fr + 2880 <= x < fr + 2902) \/
                     (AC.aspZ regs - ACPY.ASAN_MEMCPY_K <= x < AC.aspZ regs) \/ (A + 104 <= x < A + 120)) /\
                  UF.stk rsegs mem' fr (fr + FRAME_BYTES) /\
                  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' /\
                  LT g fr j regs' mem').
    { destruct HIFS3 as (HID & HFG & HFSj).
      destruct Hmem as [(-> & Hopf) | (Hopt & mc & MUc & WMc & ROc & STc & BSc & ->)].
      - exists []. split; [apply LF.munch_refl|]. split; [apply LF.wmono_refl|].
        split; [cbn [all_app]; exact I|].
        split; [intros x Hx; exfalso; apply Hx; exact I|].
        split; [exact (fra_stk B APIf ra g fr _ regs mem md HFRA)|].
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HENT | exact Hmat]|].
        (* the record did not open: the first-fragment state of turn S j is turn j's (f17_fsj_false) *)
        split; [exact HID|]. split; [exact HFG|].
        exact (F17.f17_fsj_regs g fr (S j) regs regs' mem (F17.f17_fsj_false g fr j regs mem Hopf HFSj) G9).
      - assert (Hn26 : 1 <= RF.bat (t_g (g_in g) j) 26 <= 22).
        { pose proof Hopt as Ho. unfold f_opens in Ho. apply andb_prop in Ho as (Ho1 & _).
          exact (f18_fr_fg_n _ _ Ho1). }
        assert (Hrbl : length (t_g (g_in g) j) = 50%nat) by apply f18_t_g_length.
        assert (BSl : length (firstn (Z.to_nat (RF.bat (t_g (g_in g) j) 26)) (skipn 27 (t_g (g_in g) j)))
                        = Z.to_nat (RF.bat (t_g (g_in g) j) 26))
          by (rewrite length_firstn, length_skipn, Hrbl; lia).
        (* the copy (mem -> mc): FRA, ENT and the frame's bytes by f17_cp_fra *)
        assert (HDst : forall x, fr + 2880 <= x < fr + 2880 + RF.bat (t_g (g_in g) j) 26 ->
                         exists b, UM.mrd rsegs mc (UM.wa x) = Some b).
        { intros x Hx. apply (F17.f17_ba_rd mc (fr + 2880) _ x BSc). rewrite BSl. lia. }
        destruct (F17.f17_cp_fra B APIf ra empty FF g fr _ regs mem mc md (RF.bat (t_g (g_in g) j) 26) HFRA HENT ltac:(lia)
                    MUc WMc ROc STc HDst) as (HFRAc & HENTc & HSTKc).
        (* the two spill stores (mc -> mem') *)
        pose proof (F17.fra_store1 B APIf ra empty FF g fr _ regs mc md A 104 (Z_to_bv 64 1) HFRAc Hs9g Hdisj Happ
                      ltac:(lia) ltac:(lia)) as HF1.
        pose proof (F17.ent_store1 B APIf ra g fr _ regs mc md A 104 (Z_to_bv 64 1) HFRAc HENTc Hs9g Happ
                      ltac:(lia) ltac:(lia)) as HE1.
        pose proof (F17.fra_store1 B APIf ra empty FF g fr _ regs _ md A 112 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)) HF1 Hs9g Hdisj
                      Happ ltac:(lia) ltac:(lia)) as HF2.
        pose proof (F17.ent_store1 B APIf ra g fr _ regs _ md A 112 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)) HF1 HE1 Hs9g
                      Happ ltac:(lia) ltac:(lia)) as HE2.
        assert (MU2 : LF.munch [(A + 104, A + 120)] mc
                        (write_to_mem (write_to_mem mc (UM.wa (A + 104)) (UM.le8 (Z_to_bv 64 1)))
                           (UM.wa (A + 112)) (UM.le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))).
        { apply LF.munch_write; [ apply LF.munch_write; [ apply LF.munch_refl | | | ] | | | ];
            try (rewrite UM.length_le8); try (cbn [LF.inside]; left);
            clear - HAlo HAhi; unfold APPMEM_END, LOWMEM_END, HIGHMEM_BEG in *; lia. }
        assert (WM2 : LF.wmono rsegs mc
                        (write_to_mem (write_to_mem mc (UM.wa (A + 104)) (UM.le8 (Z_to_bv 64 1)))
                           (UM.wa (A + 112)) (UM.le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26)))))
          by (repeat apply LF.wmono_write; apply LF.wmono_refl).
        assert (MU : LF.munch [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                               (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] mem
                       (write_to_mem (write_to_mem mc (UM.wa (A + 104)) (UM.le8 (Z_to_bv 64 1)))
                          (UM.wa (A + 112)) (UM.le8 (Z_to_bv 64 (RF.bat (t_g (g_in g) j) 26))))).
        { apply (LF.munch_trans _ mem mc).
          - apply (LF.munch_weaken [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                                    (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs)]); [|exact MUc].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (H1 & H2 & _).
            split; [exact H1|]. split; [exact H2 | exact I].
          - apply (LF.munch_weaken [(A + 104, A + 120)]); [|exact MU2].
            intros x Hx. cbn [LF.outside] in Hx |- *. destruct Hx as (_ & _ & H3 & _).
            split; [exact H3 | exact I]. }
        assert (HAW' : all_app [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                                (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)]).
        { cbn [all_app]. split; [intros a Ha; apply Happfr; lia|].
          split; [intros a Ha; unfold app_mem; right; lia|].
          split; [intros a Ha; unfold app_mem; right; apply Happ; lia | exact I]. }
        exists [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)].
        split; [exact MU|].
        split; [exact (LF.wmono_trans rsegs _ _ _ WMc WM2)|].
        split; [exact HAW'|].
        split.
        { intros x Hx. destruct (F17.f17_in3 _ _ _ _ _ _ x Hx) as [Hw|[Hw|Hw]]; [left | right; left | right; right];
            lia. }
        split.
        { (* the frame stays byte-backed across the two stores (they are above it) *)
          apply (LF.stk_transport rsegs [(A + 104, A + 120)] mc _ fr (fr + FRAME_BYTES) HSTKc MU2 WM2).
          intros x Hx. left. cbn [LF.outside]. split; [lia | exact I]. }
        split; [exact (sl_fra_move B APIf ra g fr _ regs regs' _ md md' HF2 G2 G3 G4 G8 G9 G19 G26 Hmat)|].
        split; [eapply ent_mat; [exact HE2 | exact Hmat]|].
        (* the record opened: the two frame records are untouched (they lie in the frame below first.sroa.7,
           apart from the callee window and below the spill window), and the first-fragment state is turn S j's:
           [A + 104] = 1 and [A + 112] = gg[26] off the two stores, the copied body at fr + 2880 *)
        assert (HRW : forall x, fr + 2688 <= x < fr + 2840 ->
                  LF.outside [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                              (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] x).
        { intros x Hx. cbn [LF.outside]. split; [lia|]. split; [destruct HplK as [P|P]; lia|].
          split; [lia | exact I]. }
        destruct (F17.f17_idfg_keep g fr j mem _ _ HID HFG MU HRW) as (HID' & HFG').
        split; [exact HID'|]. split; [exact HFG'|].
        apply (F17.f17_fsj_true g fr j regs' _ Hopt).
        + (* [A + 104] = 1 *)
          exists A. split; [unfold rg; rewrite G9; exact Hs1|]. apply F17.f17_q64_ba.
          apply F17.f17_w8_other; [apply F17.f17_w8_same | | | ]; clear - HAr HAtop; lia.
        + (* [A + 112] = gg[26] *)
          exists A. split; [unfold rg; rewrite G9; exact Hs1|]. apply F17.f17_q64_ba.
          apply F17.f17_w8_same; clear - HAr HAtop; lia.
        + (* the copied body at fr + 2880, which the two stores (above the frame) miss *)
          eapply fl_bytes; [exact BSc | exact MU2 |]. rewrite BSl. intros x Hx.
          cbn [LF.outside]. split; [lia | exact I].
        + (* first.sroa.7 stays addressable: W is app memory *)
          destruct HFSj as (_ & _ & _ & Hbad & _).
          exact (sl_addr_keep mem _ [(fr + 2880, fr + 2880 + RF.bat (t_g (g_in g) j) 26);
                   (AC.aspZ regs - ACPY.ASAN_MEMCPY_K, AC.aspZ regs); (A + 104, A + 120)] (fr + 2880) 35 Hbad MU HAW'). }
    destruct COM as (W & MU & WM & HAW & HWin & HSTKfr' & HFRA' & HENT' & HLT).
    assert (HWout : forall x, (x < fr + 2880 \/ fr + 2902 <= x) ->
                      (x < AC.aspZ regs - ACPY.ASAN_MEMCPY_K \/ AC.aspZ regs <= x) ->
                      (x < A + 104 \/ A + 120 <= x) -> LF.outside W x).
    { intros x H1 H2 H3. destruct (Tac_f17b.f17m_outside_dec W x) as [Ho|Ho]; [exact Ho|].
      exfalso. destruct (HWin x Ho) as [Hw|[Hw|Hw]]; lia. }
    (* no shadow byte is written: W is app memory *)
    assert (HWsh : forall x, in_shadow x -> LF.outside W x).
    { intros x Hx. apply HWout.
      - destruct (Z_lt_le_dec x (fr + 2880)) as [L|L]; [left; exact L|].
        destruct (Z_lt_le_dec x (fr + 2902)) as [L2|L2]; [|right; exact L2].
        exfalso. pose proof (Happfr x ltac:(lia)) as Hap. unfold app_mem in Hap. unfold in_shadow in Hx.
        unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hap, Hx. lia.
      - left. unfold in_shadow in Hx. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hx. lia.
      - left. unfold in_shadow in Hx. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hx. lia. }
    assert (MK : meta_kept mem mem') by exact (munch_meta _ mem mem' MU HAW).
    (* The heap block [phi, phi + a_size len_j) is live (in hb), so it ends at or below stklo, below the callee
       window and the spill window, and none of its bytes is a frame byte (f17_blk_out): W misses every record
       byte. *)
    assert (Hblk : forall x, phi <= x < phi + AC.a_size (flen g j) -> LF.outside W x).
    { intros x Hx.
      destruct (F17.f17_blk_out B APIf ra g fr _ regs mem md phi (AC.a_size (flen g j)) x HFRA
                  ltac:(unfold hb1; apply in_or_app; left; left; reflexivity) Hx) as (Hlo & Hnf).
      apply HWout; lia. }
    assert (HFLSI' : FLSI g j fr regs' mem').
    { apply (F17.flsi_cp g j fr regs regs' mem mem' W HFLSI G9 MU HAW WM).
      - intros A' HA' off x Ho Hd Hx.
        destruct (F17.f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia.
      - exact HSTKfr'.
      - (* the input block is a live heap block of the entry (when it is not empty) *)
        intros x Hx. pose proof HFLSI as HP. unfold FLSI in HP. destruct HP as (_ & _ & _ & _ & (Hin & _ & _) & _).
        assert (Hn0 : 0 < g_n g) by (rewrite g_n_len; lia).
        destruct (F17.f17_blk_out B APIf ra g fr _ regs mem md (g_p g) (g_n g) x HFRA
                    (in_or_app _ _ _ (or_intror (Hin Hn0))) ltac:(rewrite g_n_len; lia)) as (Hlo & Hnf).
        apply HWout; lia. }
    destruct Hw240 as (w240 & Hw240q & Hw240r & Hw240t & Hw240f).
    apply (F17.to_exit_823e8 B APIf ra empty FF j Hexit).
    exists phi, regs', mem', md', fr. rewrite SEGS.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Haddrp). split; [exact Hphinz|]. exact (addressable_kept mem mem' _ _ Haddrp MK). }
    split; [exact HFLSI'|].
    split.
    { destruct HLK as (HLj & HL21 & HLour). split; [exact HLj|]. split.
      - unfold rg in *. rewrite G21. exact HL21.
      - unfold OURb in *. eapply fl_bytes; [exact HLour | exact MU |]. rewrite OUR_length.
        intros x Hx. apply HWout; destruct HplK as [P|P]; lia. }
    split.
    { exists A, w240.
      split; [unfold rg; rewrite G9; exact Hs1|].
      split; [exact HAr|].
      split; [rewrite ASP; exact HspA|].
      split; [unfold rg; rewrite G23; exact Hs7|].
      split; [unfold rg; rewrite G24; exact Hs24|].
      split; [unfold rg; rewrite G22; exact Hs22|].
      split.
      { intro HfL. destruct (Hrecg HfL) as (HRI & _ & Hrecw).
        apply (rec_inv0_kept g j fr phi A mem mem' W HRI MU).
        - intros x Hx. apply Hblk. unfold AC.a_size. lia.
        - intros x Hx. apply HWout; lia. }
      split; [unfold q64 in Hq136 |- *; eapply fl_bytes; [exact Hq136 | exact MU |];
              rewrite UM.length_le8; intros x Hx; apply HWout; lia|].
      split; [unfold q64 in Hq120 |- *; eapply fl_bytes; [exact Hq120 | exact MU |];
              rewrite UM.length_le8; intros x Hx; apply HWout; lia|].
      split; [unfold q64 in Hq176 |- *; eapply fl_bytes; [exact Hq176 | exact MU |];
              rewrite UM.length_le8; intros x Hx; apply HWout; lia|].
      split.
      { unfold q64 in Hw240q |- *. eapply fl_bytes; [exact Hw240q | exact MU |].
        rewrite UM.length_le8. intros x Hx. apply HWout; lia. }
      split; [exact Hw240r|].
      split; [exact Hw240f|].
      (* t_8819 holds only on the long arm (t_8819 = t_big && ..), so the guarded record facts hold *)
      intro E8819.
      assert (HfL : 50 <= flen g j).
      { pose proof E8819 as E0. unfold t_8819, t_big in E0. apply andb_prop in E0 as [E1 _].
        apply andb_prop in E1 as [E1' _]. apply Z.leb_le in E1'. unfold flen. exact E1'. }
      destruct (Hrec40 HfL) as (Haddr & _).
      destruct (Hrecg HfL) as (HRI0 & Hphiw & Hrecw).
      destruct (HL12 E8819) as (HRP & (ls & rs & HLq & HLb & HLl & HRb & HRl & HLm & HLad) &
        (ls2 & rs2 & HL2q & HL2b & HL2l & HR2b & HR2l & HL2m & HL2ad)).
      destruct (ba_first6 mem (fr + 186) ls HLb HLl) as (HLb6 & HLl6).
      destruct (ba_first6 mem phi rs HRb HRl) as (HRb6 & HRl6).
      destruct (ba_first6 mem (fr + 180) ls2 HL2b HL2l) as (HL2b6 & HL2l6).
      destruct (ba_first6 mem (phi + 6) rs2 HR2b HR2l) as (HR2b6 & HR2l6).
      split; [exact (Hw240t E8819)|].
      (* push 15: the parse-made record facts; W misses the record bytes, every shadow byte and fr + 196 *)
      split.
      { destruct HRI0 as (_ & _ & _ & _ & Hpap & _).
        apply (F17.f17_rec_parse_kept g j fr phi mem mem' W HRP Hpap MU).
        - intros x Hx. apply Hblk. unfold AC.a_size. lia.
        - exact HWsh.
        - intros x Hx. apply HWout; destruct HplK as [P|P]; lia. }
      exists (firstn 6 ls), (firstn 6 rs), (firstn 6 ls2), (firstn 6 rs2).
      split.
      { unfold q64 in HLq |- *. eapply fl_bytes; [exact HLq | exact MU |].
        rewrite UM.length_le8. intros x Hx. apply HWout; lia. }
      split.
      { eapply fl_bytes; [exact HLb6 | exact MU |]. rewrite HLl6. intros x Hx.
        apply HWout; destruct HplK as [P|P]; lia. }
      split; [rewrite HLl6; lia|].
      split.
      { eapply fl_bytes; [exact HRb6 | exact MU |]. rewrite HRl6. intros x Hx. apply Hblk. unfold AC.a_size. lia. }
      split; [rewrite HRl6; lia|].
      split; [rewrite memcmp_firstn; exact HLm|].
      split; [exact (addressable_kept mem mem' (fr + 186) 6 HLad MK)|].
      split.
      { pose proof (addressable_sub mem phi 50 0 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) as Had6.
        rewrite Z.add_0_r in Had6. exact (addressable_kept mem mem' phi 6 Had6 MK). }
      split; [rewrite ASP; exact Hphiw|].
      split.
      { unfold q64 in HL2q |- *. eapply fl_bytes; [exact HL2q | exact MU |].
        rewrite UM.length_le8. intros x Hx. apply HWout; lia. }
      split.
      { eapply fl_bytes; [exact HL2b6 | exact MU |]. rewrite HL2l6. intros x Hx.
        apply HWout; destruct HplK as [P|P]; lia. }
      split; [rewrite HL2l6; lia|].
      split.
      { eapply fl_bytes; [exact HR2b6 | exact MU |]. rewrite HR2l6. intros x Hx. apply Hblk. unfold AC.a_size. lia. }
      split; [rewrite HR2l6; lia|].
      split; [rewrite memcmp_firstn; exact HL2m|].
      split; [exact (addressable_kept mem mem' (fr + 180) 6 HL2ad MK)|].
      exact (addressable_kept mem mem' (phi + 6) 6
               (addressable_sub mem phi 50 6 6 Haddr ltac:(lia) ltac:(lia) ltac:(lia)) MK). }
    (* push 6c8 tail: s2 kept, s9 = fr + 64, the record bytes (inside the live heap block, so off W) and the two
       per-turn spills (offsets 152 / 280, off W) *)
    split; [unfold rg; rewrite G18; exact Hs18|].
    split; [unfold rg; exact G25|].
    split.
    { intro HfL. destruct (Hrecb HfL) as (Hbg & Hbp & Hlp).
      assert (Lg : (length (t_g (g_in g) j) <= 50)%nat) by (unfold t_g, fr50; rewrite firstn_length; lia).
      split; [eapply fl_bytes; [exact Hbg | exact MU |]; intros x Hx; apply Hblk; unfold AC.a_size; lia|].
      split; [eapply fl_bytes; [exact Hbp | exact MU |]; intros x Hx; apply Hblk; unfold AC.a_size; lia
             | exact Hlp]. }
    split.
    { apply (F17.spill_keep regs regs' mem mem' W 152 _ H152 G9 MU).
      intros A' HA' x Hx.
      destruct (F17.f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia. }
    split.
    { apply (F17.spill_keep regs regs' mem mem' W 280 _ H280 G9 MU).
      intros A' HA' x Hx.
      destruct (F17.f17_rg9_wrap regs A A' Hs1 HAr HA') as [E|[E|E]]; [subst A' | |]; apply HWout; lia. }
    (* push 12B: LT = IFS g fr (S j), from IFS3 and the arm's own f_opens value (COM) *)
    exact HLT.
Qed.
End Src.

(* `type of @F17.seg_F17b`: the statement with its section arguments as F17.v closes them (the implicit ones
   included), so the tie cannot drift from the source. *)
Lemma seg_F17b_src : ltac:(let T := type of @F17.seg_F17b in exact T).
Proof. exact @seg_F17b_src0. Qed.
