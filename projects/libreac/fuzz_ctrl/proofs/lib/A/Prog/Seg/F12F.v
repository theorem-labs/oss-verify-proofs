(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module paths, module names and addresses changed; 1186 of its 1253 lines of code are new or changed and 3168 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F12.v blob a5148873612a (the same blob at the union
   6a74d5929d2, at the base fdd2ed9f9d7 of a Theorem Labs lane's working branch and at the glue base eb89fed7fac).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), lib/A/MemNormF.v 9e5ea0ff243d (the blob this tree had at release c5e779efe8c);
   the callee's footprint contract lib/A/Prog/asan_memcpy_cF.v 3ae84ac9bb40 (the blob this tree had at release c5e779efe8c) and its proof
   lib/A/Prog/asan_memcpyF.v (an earlier version, blob 31ace5ece389, not in this delivery) (asan_memcpy_holds_F, a Theorem Labs lane).
   Written by a Theorem Labs lane (one writer), on the brief of a Theorem Labs lane's segment-F spec
   (segF-v19-spec.md (a working note, not in this delivery)); mechanical re-run, route (a) (lead 22:15Z); input to the ported
   walk only.  rule 24: no function proved (a mechanical re-run of two already-proved inline segment runs).

   NO constr_eq PIN, AND WHY: Seg/F12.v states no run lemma; its two runs sit inline as the Exec.evt premise of
   Tac_b5.sl_run_lib inside the cut lemmas f12_run (F12.v:933) and f12_entry2 (F12.v:1645), so no F12.<r> has an
   evt type to pin against; this file follows the precedent of a Theorem Labs lane's own Seg/F10F.v (each inline run stated
   as its _F over MS (Regs6ss.mkR_of regs) .., with its old form at ExecF.RNG_all, no pin).

   WHAT REPLACES THE PIN (a Theorem Labs lane's compiled tie, a Theorem Labs lane's derivation to the segment):
   - f12_run_src : exactly the closed type of F12.f12_run, and f12_entry2_src : exactly the closed type of
     F12.f12_entry2 (both stated `ltac:(let T := type of (@F12.<r>) in exact T)`), each re-proved by F12.v's own
     script for that lemma with ONE change: the inline evt premise of sl_run_lib is discharged from this file's old
     form (f12_run_of_F / f12_entry2_of_F) instead of being stepped.  They compile only if the old forms give
     exactly the runs the source cut lemmas consume, which is what a pin asserts.
   - seg_F12_src : exactly the closed type of F12.seg_F12, derived from f12_run_src, f12_entry2_src and F12.f12_entry1
     (a no-step lemma, below), as F12.seg_F12's own proof derives it from f12_run / f12_entry2 / f12_entry1.  So the
     segment's own cut lemma follows from the _F runs at ExecF.RNG_all.
   - BOTH TIES ARE EXACT (no extra hypothesis in front).  F12.v's Section S carries `Hypothesis HMCPY :
     asan_memcpy_contract` (F12.v:741), the PLAIN contract, and only asan_memcpy_contract_of_F (F -> plain) links the
     two forms; but the footprint contract is PROVED and closed on the base (asan_memcpyF.v:240 asan_memcpy_holds_F,
     the same discharge F2F.v / R8F.v / F23F.v use), so f12_run_of_F needs no memcpy hypothesis at all, and HMCPY
     stays a binder of f12_run_src's (and seg_F12_src's) statement that the proof does not use.  f12_entry2's
     stretch calls nothing, so its tie never involved the contract.

   SOURCE LINES EACH _F RE-STATES (the by-script instruction comparison of each against these lines is in the
   commit message):
   - f12_run_F: the run F12.v:1073-1222 (the second premise of the sl_run_lib application F12.v:1059-1071, inside
     f12_run F12.v:933-1627), 0x820fc -> 0x82138: `sd s9,152(s1)`, the nine `sb zero,k(s3)` stores of the frame's
     metadata bytes S(fr)+42 .. S(fr)+50, `li a2,72`, the two spill loads [A+184] / [A+192], `mv a1,s9` and
     `jal __asan_memcpy` at 0x82134 (checked_memcpy, 0x52028).  The call enters through asan_memcpy_contract_F
     (lib/A/Prog/asan_memcpy_cF.v:46) in the place of F12.v's HMCPY, on the normalized memory by
     MemNormF.evtF_normalize_ro exactly where F12.v uses MemNorm.evt_normalize (F12.v:1146-1147): NO split.
   - f12_entry2_F: the run F12.v:1661-1671 (the second premise of the sl_run_lib application F12.v:1652-1659, inside
     f12_entry2 F12.v:1645-1692), 0x820f8 -> 0x820fc: one
     `bltz a0` with a0 = v, 0 <= v < 2^63, not taken.  Register-only: no rng premise.
   - f12_entry1 (F12.v:1630-1641) is a NO-STEP lemma (zero-step lemma, no run): it steps no instruction and only
     drops `ir = false` from the body, so there is nothing to re-run over StepF; F12F.rng.tsv (a working note, not in this delivery) records it with kind
     `none` (a Theorem Labs lane's word for a run that needs no footprint premise), and seg_F12_src cites F12.f12_entry1
     itself.

   GENERALISATIONS (as F10F.v does; each is instantiated back in the tie):
   - in the post, `q64 mem' (A + 152) (b2z (t_tfill (g_in g) j))` is `q64 mem' (A + 152) v25` with the premise
     `rg regs 25 v25` (F12.v's Hs9, b5_K's s9; the store at 0x820fc writes s9);
   - `t_FG (g_in g) j` (F12.v:1035 `set (st := ..)`) is a bound `st` with `length st = 72%nat`;
   - the facts F12.v:937-1058 derives from the cut before the run are premises in the form the run uses, except
     the spill band `wr_at rsegs mem (A + 64) 224` (F12.v:1015), narrowed to the stored word
     `wr_at rsegs mem (A + 152) 8` (the tie re-derives it by F12.f12_wrsub), the frame-metadata writability,
     derived inside from `shadow_rw mem` as F12.v:1009-1018 does, and fra_app's `AC.GT <= fr`, stated as
     `IMG_HI <= fr` (ImgBounds, the same 6283264);
   - the callee window: F12.v fixes the contract's `lo` to `sp - FN_STACK` (F12.v:1148, FRA's whole 1 MB window
     via fra_win); here `lo` is a binder with exactly the contract's own premises `HIGHMEM_BEG <= lo`,
     `lo + ASAN_MEMCPY_K <= sp` and `stk rsegs mem lo sp` (and `stk rsegs mem' lo sp` in the post), so a caller
     whose stack window is smaller (the core's ajournal window is LLVMF_STK = 32768 bytes) can meet it; the tie
     instantiates `lo := sp - FN_STACK`.
   AsanRTInv.RT is NOT a premise of any lemma here: it enters one level up, through F12.v's Section S
   (APIf / FF, F12.v:735, :738), unchanged, and the tie lemmas take those as the binders of F12's own types.

   SIX-MODULE SPELLING (porter a Theorem Labs lane, 04:24Z / 04:33Z): this file's Require closure reaches both copies of
   YK11, YK1b and YM05, so it never Imports them and names YK11's content only through
   `Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11` (the unit copy, the one F12.v
   imports). *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
(* F12.v's own Require block, in its order; YK11 / YM05 Required, not Imported (six-module rule, header) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply RcDeclLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  asan_memcpy_c bcmp_wrap_c memcmp_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
(* this file's additions: the source segment, the callee's footprint contract and its proof, the evtF normalize *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF asan_memcpyF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* as in F2F.v: munch / wmono / outside / bytes_at are lib/Lib's, the ones the callee contract speaks about *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
(* MState.unsigned_lit_wrap, MState.unsigned_lit and Frame.outside are written by full path to the lib/Lib copies,
   `OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.<module>.<name>`: this is an F-side (footprint) file, and its
   engine family is lib/Lib (its statements, ExecF and StepF bind it).  The source Seg/F12.v binds the A.Tk.UL copies;
   that is the one allowed difference, the Seg engine split (a Theorem Labs lane 08:56Z; Locate-table DEFECT rule).  Written short,
   they bound the A/Bz/Lib twins here (glue base 29ddfc3ea99 / a1debf82953, int base 739628fd500), which is neither
   side. *)

(* The run keeps the memory of its ten stores explicit (the write chain), as F12.v does with Step's hook
   (F12.v:52): StepF's automatic cell bookkeeping is switched off. *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= idtac.

(* The spill and metadata addresses reach solve_accs as bv_unsigned (Z_to_bv 64 A) + k / bv_unsigned (Z_to_bv 64
   (Sfr fr)) + k, which its syntactic matching does not relate to the rng premises; close such a goal from any rng
   hypothesis after normalizing bv_unsigned (Z_to_bv 64 _) (F2F.v's f2_accF, unchanged). *)
Ltac f12F_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= f12F_accF.

Section RunF.
Context {fx : K11.FPState}.

(* ---- f12_run's inline run (F12.v:1073-1222), 0x820fc -> 0x82138, under a footprint RNG ---- *)
Lemma f12_run_F : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr sp lo v25 : Z) (st junk : list byte),
  (* the registers the run reads: sp, s1 = A, s3 = S(fr), s9 = v25 (stored at [A+152]) *)
  K11.getr regs 2 = Z_to_bv 64 sp -> rg regs 9 A -> rg regs 19 (Sfr fr) -> rg regs 25 v25 ->
  (* placement: the frame, the spill area, the stack *)
  IMG_HI <= fr -> fr mod 8 = 0 -> fr + FRAME_BYTES <= A -> A + 416 <= APPMEM_END ->
  sp <= A -> 0 <= sp < 2 ^ 64 -> sp <= APPMEM_END ->
  (* the callee window below sp: exactly asan_memcpy_contract_F's stack premises *)
  HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= sp ->
  (fr + FRAME_BYTES <= sp - 2224 \/ sp <= fr) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) ->
  (* the memory the run reads and writes *)
  wr_at rsegs mem (A + 152) 8 ->
  q64 mem (A + 184) (fr + 336) -> q64 mem (A + 192) (fragb fr) ->
  bytes_at rsegs mem (fragb fr) st -> length st = 72%nat -> addressable mem (fragb fr) 72 ->
  rw_cells rsegs mem (fr + 336) [CB 72 junk] -> length junk = 72%nat ->
  stk rsegs mem lo sp ->
  ro_agree rsegs mem -> asan_cells mem -> shadow_rw mem ->
  (* the run's own accesses: the spill store, the nine metadata-byte stores, the two spill loads *)
  ExecF.rng RNG (A + 152) 8 -> ExecF.rng RNG (Sfr fr + 42) 9 ->
  ExecF.rng RNG (A + 184) 8 -> ExecF.rng RNG (A + 192) 8 ->
  (* the callee's regions (asan_memcpy_contract_F's footprint premises), unchanged *)
  rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExecF.rng RNG (fr + 336) 72 -> ExecF.rng RNG (fragb fr) 72 ->
  sh_word_rng RNG (fr + 336) 72 -> sh_word_rng RNG (fragb fr) 72 ->
  sh_word_rng RNG (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = MS R K11.fp_regs pc' K11.fp_csr None mem' (K11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x82138 /\
        K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
        K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
        K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
        K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
        K11.getr R 25 = Z_to_bv 64 (fragb fr) /\ K11.getr R 26 = K11.getr regs 26 /\
        munch (f12_W A fr sp) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
        stk rsegs mem' lo sp /\ q64 mem' (A + 152) v25 /\
        rw_cells rsegs mem' (fr + 336) [CB 72 st] /\ bytes_at rsegs mem' (fragb fr) st /\
        addressable mem' (fr + 336) 72 /\ asan_cells mem' /\ shadow_rw mem'))
    (MS (Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x820fc) K11.fp_csr None mem (K11.seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros RNG MCPY regs mem A fr sp lo v25 st junk Hr2 H9 Hr19 Hs9 HGT Hfr8 Hfa HA416 Hspa Hsp0 HspA Hlo HloK Hfrw2 Hfrapp Hw152 Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hwstk Hro HAC HSW
    R152 Rsh42 R184 R192 Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  (* the constants and derived placement facts F12.v:937-1058 states before its run (the ones the run uses) *)
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HFN : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HGTv : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKm : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HIH : IMG_HI = 6283264) by reflexivity.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSPu : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (HCk : 0 < LOWMEM_END /\ LOWMEM_END < LOWSHADOW_END /\ LOWSHADOW_END < HIGHSHADOW_BEG /\
               HIGHSHADOW_BEG < HIGHMEM_BEG /\ HIGHMEM_BEG < APPMEM_END /\ APPMEM_END <= 2 ^ 64 /\
               AC.GT + 1048576 < HIGHMEM_BEG /\ RT_HI < AC.GT /\ 0 < AC.GT /\
               RT_LO < RT_HI /\ RT_HI < LOWMEM_END /\ 0 < RT_LO /\
               0 < REAL_BCMP /\ REAL_BCMP + 8 < LOWMEM_END /\
               0 < REAL_MEMCMP /\ REAL_MEMCMP + 8 < LOWMEM_END /\
               0 < GOT_CF /\ GOT_CF + 8 < LOWMEM_END /\ 0 < CF /\ CF + 256 < LOWMEM_END /\
               REAL_BCMP + 8 < AC.GT /\ REAL_MEMCMP + 8 < AC.GT /\ GOT_CF + 8 < AC.GT /\ CF + 256 < AC.GT)
    by (unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END, AC.GT, RT_HI, RT_LO,
          REAL_BCMP, REAL_MEMCMP, GOT_CF, CF; lia).
  destruct HCk as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7 & HC8 & HC9 & HC10 & HC11 & HC12 &
                   HC13 & HC14 & HC15 & HC16 & HC17 & HC18 & HC19 & HC20 &
                   HC21 & HC22 & HC23 & HC24).
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (f12_in_shadow_fr fr a Hfrapp Hfr8 Ha)).
  assert (HSHlo : LOWMEM_END <= Sfr fr)
    by (destruct (f12_sh_lt (Sfr fr) (HshIS (Sfr fr) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (HSHhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (destruct (f12_sh_lt (Sfr fr + FRAME_SHADOW - 1) (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia))) as (Hi1 & Hi2); lia).
  (* the frame lies wholly above or wholly below its metadata range (it is app memory, low or high) *)
  assert (Harm : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr).
  { pose proof (Hfrapp fr ltac:(lia)) as Ha. pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Hb.
    clear - Ha Hb HFBval HFSval. unfold Sfr, shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
    destruct Ha as [Hlow|Hhigh]; [left|right]; destruct Hb as [Hb|Hb]; Z.div_mod_to_equations; lia. }
  assert (Hshstk : stk rsegs mem (Sfr fr) (Sfr fr + FRAME_SHADOW))
    by (apply (f12_shadow_stk mem (Sfr fr) (Sfr fr + FRAME_SHADOW) HSW HshIS); lia).
  assert (Hwrsh : wr_at rsegs mem (Sfr fr) FRAME_SHADOW)
    by (apply (f12_wr_of_stk mem (Sfr fr) FRAME_SHADOW (Sfr fr) (Sfr fr + FRAME_SHADOW) Hshstk); lia).
  assert (B152 : store_ok rsegs mem (wa (A + 152)) 8%nat = true).
  { pose proof (wr_at_store_ok rsegs mem (A + 152) 8 0 8%nat Hw152 ltac:(lia) ltac:(cbn; lia)) as HB0.
    rewrite Z.add_0_r in HB0. exact HB0. }
  assert (B42 : store_ok rsegs mem (wa (Sfr fr + 42)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 42 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B43 : store_ok rsegs mem (wa (Sfr fr + 43)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 43 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B44 : store_ok rsegs mem (wa (Sfr fr + 44)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 44 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B45 : store_ok rsegs mem (wa (Sfr fr + 45)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 45 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B46 : store_ok rsegs mem (wa (Sfr fr + 46)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 46 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B47 : store_ok rsegs mem (wa (Sfr fr + 47)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 47 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B48 : store_ok rsegs mem (wa (Sfr fr + 48)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 48 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B49 : store_ok rsegs mem (wa (Sfr fr + 49)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 49 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B50 : store_ok rsegs mem (wa (Sfr fr + 50)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 50 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  (* the bounds the footprint hint f12F_accF needs for the s3-based stores *)
  assert (HSf0 : 0 <= Sfr fr) by lia.
  assert (HSf1 : Sfr fr + 51 <= 2 ^ 64) by lia.
  rewrite f12_mkR_of_expand.
  f12_subst_slot H9. rewrite Hr2. f12_subst_slot Hr19.
  try f12_lib_ms.
  f12_sok B152. step.
  f12_sok B46. step.
  f12_sok B47. step.
  f12_sok B48. step.
  f12_sok B49. step.
  f12_sok B42. step.
  f12_sok B43. step.
  f12_sok B44. step.
  f12_sok B45. step.
  f12_sok B50. step.
  step.
  f12_rd Hq184 (A + 184) (fr + 336). step.
  f12_rd Hq192 (A + 192) (fr + 2768). step.
  step. step.
  (* ---- the ten stores are done: the memory facts over the write chain ---- *)
  match goal with
  | |- context [MS _ _ _ _ _ ?m0 (K11.seg_rom _)] => remember m0 as mm eqn:Emm
  end.
  assert (MUst : munch [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm).
  { rewrite Emm.
    repeat (apply munch_write; [ | lia | f12_len | cbn [inside]; rewrite ?length_le8, ?length_le1; cbn [Z.of_nat];
                                 first [left; lia | right; left; lia] ]).
    apply munch_refl. }
  assert (WMst : wmono rsegs mem mm) by (rewrite Emm; repeat apply wmono_write; apply wmono_refl).
  assert (STst : stk rsegs mm lo sp)
    by (rewrite Emm; repeat (apply stk_write; [ | lia | f12_len ]); exact Hwstk).
  assert (SWst : shadow_rw mm)
    by (rewrite Emm; repeat (apply f12_shadow_rw_write; [ | lia | f12_len ]); exact HSW).
  assert (ROmm : ro_agree rsegs mm).
  { apply (sl_ro_keep [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm Hro MUst). intros x Hx.
    cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside outside].
    split; [lia|]. split; [lia | exact I]. }
  assert (ACst : asan_cells mm)
    by (apply (fl_asan_cells _ mem mm HAC MUst); intros x Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (BAsrc : bytes_at rsegs mm (fragb fr) st)
    by (rewrite Emm; repeat (apply bytes_at_write_other; [ | lia | f12_len | f12_djl ]); exact HFGb).
  assert (RWdst : rw_cells rsegs mm (fr + 336) [CB 72 junk])
    by (rewrite Emm; repeat (apply rw_cells_frame; [ | lia | f12_len | f12_djl ]); exact Hjrw).
  assert (Q152m : bytes_at rsegs mm (A + 152) (le8 (K11.getr regs 25))).
  { rewrite Emm.
    repeat first [ apply bytes_at_write_same; rewrite ?length_le8; cbn [Z.of_nat]; lia
                 | apply bytes_at_write_other; [ | lia | f12_len | f12_djl ] ]. }
  assert (ADsrc : addressable mm (fragb fr) 72).
  { apply (f12_addr_munch mem mm _ (fragb fr) 72 HfgA MUst). intros i Hi.
    assert (Hsh : in_shadow (shadow_addr (fragb fr + i)))
      by (apply shadow_of_app; apply Hfrapp; unfold fragb; lia).
    assert (Hne : ~ (Sfr fr + 42 <= shadow_addr (fragb fr + i) < Sfr fr + 51))
      by (apply (f12_sh_out_fr fr (fragb fr + i) 42 51 Hfr8 Hfr0 ltac:(unfold fragb; lia));
          unfold fragb; lia).
    destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
    cbn [outside]; repeat split; try exact I;
    first [lia | match goal with |- ?G => idtac "ADFAIL:" G end; fail]. }
  assert (ADdst : addressable mm (fr + 336) 72).
  { apply (f12_addr_of_zero9 _ fr Hfr8 Hfrapp Hfr0). intros k Hk. rewrite Emm.
    destruct (Z.eq_dec k 0) as [->|?]; [replace (Sfr fr + 42 + 0) with (Sfr fr + 42) by lia; f12_zb|].
    destruct (Z.eq_dec k 1) as [->|?]; [replace (Sfr fr + 42 + 1) with (Sfr fr + 43) by lia; f12_zb|].
    destruct (Z.eq_dec k 2) as [->|?]; [replace (Sfr fr + 42 + 2) with (Sfr fr + 44) by lia; f12_zb|].
    destruct (Z.eq_dec k 3) as [->|?]; [replace (Sfr fr + 42 + 3) with (Sfr fr + 45) by lia; f12_zb|].
    destruct (Z.eq_dec k 4) as [->|?]; [replace (Sfr fr + 42 + 4) with (Sfr fr + 46) by lia; f12_zb|].
    destruct (Z.eq_dec k 5) as [->|?]; [replace (Sfr fr + 42 + 5) with (Sfr fr + 47) by lia; f12_zb|].
    destruct (Z.eq_dec k 6) as [->|?]; [replace (Sfr fr + 42 + 6) with (Sfr fr + 48) by lia; f12_zb|].
    destruct (Z.eq_dec k 7) as [->|?]; [replace (Sfr fr + 42 + 7) with (Sfr fr + 49) by lia; f12_zb|].
    replace k with 8 by lia. replace (Sfr fr + 42 + 8) with (Sfr fr + 50) by lia. f12_zb. }
  (* ---- the call of checked_memcpy, on the normalized memory ---- *)
  try unfold fragb in *.
  assert (E336 : bv_unsigned (Z_to_bv 64 (fr + 336)) = fr + 336) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E2768 : bv_unsigned (Z_to_bv 64 (fr + 2768)) = fr + 2768) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  pose proof MCPY as HM. unfold asan_memcpy_contract_F, ASAN_MEMCPY_K in HM. cbv zeta in HM.
  pose proof (mem_rel_normalize rsegs mm ROmm) as REL.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact ROmm |].
    eapply HM with (RNG := RNG) (src := st) (junk := junk) (lo := lo).
    all: rewrite ?E336, ?E2768, ?E72, ?HSPu.
    all: try change (Z.to_nat 72) with 72%nat.
    - exact (proj1 (bytes_at_rel rsegs mm _ _ _ REL) BAsrc).
    - exact HFGl.
    - apply (rel_rw_norm mm _ _ _ REL); [|exact RWdst].
      intros i Hi. apply ro_addr_false_hi. cbn [cells_size csize Nat.add] in Hi. lia.
    - right; right. lia.
    - lia.
    - exact (rel_addr_norm mm _ _ _ REL ADsrc).
    - exact (rel_addr_norm mm _ _ _ REL ADdst).
    - right. apply Hfrapp. lia.
    - right. apply Hfrapp. lia.
    - right. split; apply Hfrapp; lia.
    - right. lia.
    - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
    - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
    - apply (rel_stk_norm mm _ _ _ REL); [intros x Hx; apply ro_addr_false_hi; lia | exact STst].
    - lia.
    - lia.
    - exact HspA.
    - exact (rel_ac_norm mm _ REL ACst).
    - exact (rel_sw_norm mm _ REL SWst).
    - exact (mem_inv_normalize rsegs mm).
      (* the callee's footprint premises (asan_memcpy_contract_F), this lemma's own *)
      - exact Rby.
      - exact Rimg.
      - exact Rstk.
      - exact RngD.
      - exact RngS.
      - exact RngDs.
      - exact RngSs.
      - exact RngKs. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SR0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
    EFc, ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  pose proof (munch_rel rsegs _ mm (normalize rsegs mm) m' m0' REL HR' Hro' MU0) as MUc.
  pose proof (wmono_rel rsegs mm (normalize rsegs mm) m' m0' REL HR' Hro' WM0) as WMc.
  pose proof (ro_agree_same rsegs mm m' ROmm Hro') as ROc.
  pose proof (rel_stk_back m' m0' _ _ HR' ST0) as STc.
  pose proof (rel_rw_back m' m0' _ _ HR' RW0) as RWc.
  pose proof (proj2 (bytes_at_rel rsegs m' m0' _ _ HR') BA0) as BAc.
  pose proof (rel_ac_back m' m0' HR' AC0) as ACc.
  pose proof (rel_sw_back m' m0' HR' SR0) as SRc.
  unfold ASAN_MEMCPY_K in MUc.
  rewrite ?E336 in MUc. rewrite ?E72 in MUc. rewrite ?HSPu in MUc.
  rewrite ?HSPu in STc.
  rewrite ?E336 in RWc. rewrite ?E72 in RWc.
  rewrite ?E2768 in BAc.
  replace (ret_pc (Z_to_bv 64 0x82138)) with (Z_to_bv 64 0x82138)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 3 eexists. split; [reflexivity|].
  split; [reflexivity|].
  do 14 (split; [reflexivity|]).
  split.
  { unfold f12_W. eapply munch_trans.
    - eapply munch_weaken; [|exact MUst]. intros z Hz. cbn [outside] in *.
      repeat split; try exact I; lia.
    - eapply munch_weaken; [|exact MUc]. intros z Hz. cbn [outside] in *.
      repeat split; try exact I; lia. }
  split; [eapply wmono_trans; [exact WMst | exact WMc]|].
  split; [exact ROc|].
  split; [exact STc|].
  split.
  { unfold q64. unfold rg in Hs9. rewrite <- Hs9.
    eapply fl_bytes; [exact Q152m | exact MUc |]. rewrite length_le8. intros x Hx. cbn [outside].
    repeat split; try exact I; lia. }
  split; [change (Z.to_nat 72) with 72%nat in RWc; exact RWc|].
  split; [exact BAc|].
  split.
  { eapply (f12_addr_munch _ _ _ (fr + 336) 72 ADdst MUc). intros i Hi.
    assert (Hsh : in_shadow (shadow_addr (fr + 336 + i))) by (apply shadow_of_app; apply Hfrapp; lia).
    destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
    cbn [outside]. repeat split; try exact I.
    all: first [ lia
               | intros HCx; apply (fun H1 => app_not_shadow _ H1 Hsh); apply Hfrapp; lia
               | match goal with |- ?G => idtac "ADDFAIL:" G end; fail ]. }
  split; [exact ACc | exact SRc].
Qed.

(* f12_run's inline run in its old form (the lib/Lib Exec.evt premise sl_run_lib takes), from f12_run_F at
   ExecF.RNG_all: the footprint contract by a Theorem Labs lane's proved, closed asan_memcpy_holds_F (asan_memcpyF.v:242),
   rng_bytes RNG_all outright, every rng / sh_word_rng premise by rng_all / sh_word_rng_all from the run's own
   placement premises. *)
Lemma f12_run_of_F :
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr sp lo v25 : Z) (st junk : list byte),
  (* the registers the run reads: sp, s1 = A, s3 = S(fr), s9 = v25 (stored at [A+152]) *)
  K11.getr regs 2 = Z_to_bv 64 sp -> rg regs 9 A -> rg regs 19 (Sfr fr) -> rg regs 25 v25 ->
  (* placement: the frame, the spill area, the stack *)
  IMG_HI <= fr -> fr mod 8 = 0 -> fr + FRAME_BYTES <= A -> A + 416 <= APPMEM_END ->
  sp <= A -> 0 <= sp < 2 ^ 64 -> sp <= APPMEM_END ->
  (* the callee window below sp: exactly asan_memcpy_contract_F's stack premises *)
  HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= sp ->
  (fr + FRAME_BYTES <= sp - 2224 \/ sp <= fr) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) ->
  (* the memory the run reads and writes *)
  wr_at rsegs mem (A + 152) 8 ->
  q64 mem (A + 184) (fr + 336) -> q64 mem (A + 192) (fragb fr) ->
  bytes_at rsegs mem (fragb fr) st -> length st = 72%nat -> addressable mem (fragb fr) 72 ->
  rw_cells rsegs mem (fr + 336) [CB 72 junk] -> length junk = 72%nat ->
  stk rsegs mem lo sp ->
  ro_agree rsegs mem -> asan_cells mem -> shadow_rw mem ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R K11.fp_regs pc' K11.fp_csr None mem' (K11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x82138 /\
        K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
        K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
        K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
        K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
        K11.getr R 25 = Z_to_bv 64 (fragb fr) /\ K11.getr R 26 = K11.getr regs 26 /\
        munch (f12_W A fr sp) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
        stk rsegs mem' lo sp /\ q64 mem' (A + 152) v25 /\
        rw_cells rsegs mem' (fr + 336) [CB 72 st] /\ bytes_at rsegs mem' (fragb fr) st /\
        addressable mem' (fr + 336) 72 /\ asan_cells mem' /\ shadow_rw mem'))
    (MS (Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x820fc) K11.fp_csr None mem (K11.seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros regs mem A fr sp lo v25 st junk Hr2 H9 Hr19 Hs9 HGT Hfr8 Hfa HA416 Hspa Hsp0 HspA Hlo HloK Hfrw2 Hfrapp Hw152 Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hwstk Hro HAC HSW.
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HIH : IMG_HI = 6283264) by reflexivity.
  assert (HKm : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (f12_in_shadow_fr fr a Hfrapp Hfr8 Ha)).
  assert (HSHlo : LOWMEM_END <= Sfr fr)
    by (destruct (f12_sh_lt (Sfr fr) (HshIS (Sfr fr) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (HSHhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (destruct (f12_sh_lt (Sfr fr + FRAME_SHADOW - 1) (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)))
          as (Hi1 & Hi2); lia).
  pose proof two64 as H64.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f12_run_F ExecF.RNG_all asan_memcpy_holds_F regs mem A fr sp lo v25 st junk
           Hr2 H9 Hr19 Hs9 HGT Hfr8 Hfa HA416 Hspa Hsp0 HspA Hlo HloK Hfrw2 Hfrapp Hw152 Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hwstk Hro HAC HSW).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold fragb; lia.
  - apply sh_word_rng_all; lia.
  - apply sh_word_rng_all; unfold fragb; lia.
  - apply sh_word_rng_all; lia.
Qed.

(* ---- f12_entry2's inline run (F12.v:1661-1671), 0x820f8 -> 0x820fc: `bltz a0` with a0 = v >= 0, not taken.
   Register-only: no rng premise. ---- *)
Lemma f12_entry2_F : forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (v : Z),
  rg regs 10 v -> 0 <= v < 2 ^ 63 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = MS R K11.fp_regs pc' K11.fp_csr None mem' (K11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
        K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
        K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
        K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
        K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
        K11.getr R 25 = K11.getr regs 25 /\ K11.getr R 26 = K11.getr regs 26))
    (MS (Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x820f8) K11.fp_csr None mem (K11.seg_rom rsegs)).
Proof.
  intros RNG regs mem v Ha0 Hv.
  rewrite f12_mkR_of_expand. f12_subst_slot Ha0.
  step.                                              (* 820f8 bltz a0,82bf4 *)
  match goal with
  | |- context [if ?cnd then _ else _] =>
      replace cnd with false
        by (symmetry; unfold bv_lts; rewrite (f12_signed v Hv);
            change (bv_signed (Z_to_bv 64 0)) with 0; apply Z.ltb_ge; lia)
  end.
  cbv iota.
  apply ExecF.evtF_done. do 3 eexists. split; [reflexivity|].
  repeat split; reflexivity.
Qed.

(* f12_entry2's inline run in its old form, from f12_entry2_F at ExecF.RNG_all. *)
Lemma f12_entry2_of_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (v : Z),
  rg regs 10 v -> 0 <= v < 2 ^ 63 ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R K11.fp_regs pc' K11.fp_csr None mem' (K11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
        K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
        K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
        K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
        K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
        K11.getr R 25 = K11.getr regs 25 /\ K11.getr R 26 = K11.getr regs 26))
    (MS (Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x820f8) K11.fp_csr None mem (K11.seg_rom rsegs)).
Proof.
  intros regs mem v Ha0 Hv.
  exact (ExecF.evtF_evt rsegs ExecF.RNG_all _ _ (f12_entry2_F ExecF.RNG_all regs mem v Ha0 Hv)).
Qed.

End RunF.

(* ---- The compiled tie (header): F12's own cut lemmas, re-proved by F12.v's own scripts with each inline run
   discharged from this file's old forms, and the segment lemma derived from them. ---- *)

(* F12.f12_run (F12.v:933-1627), its script verbatim except: the Section's binders are introduced by name, the five
   Section lemmas of F12.v are cited closed (F12.f12_ff / f12_law_blocks / f12_law_store / f12_law_fs_place /
   f12_fr_run with their Section arguments), and the inline run (F12.v:1073-1222) is f12_run_of_F. *)
Lemma f12_run_src : ltac:(let T := type of (@F12.f12_run) in exact T).
Proof.
  intros until j. revert j.
  pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hexit g c HInv.
  pose proof (F12.f12_ff B APIf ra empty FF) as (SEGS & _).
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HC & HP).
  subst c. rewrite SEGS.
  destruct HP as (HbK & HbRC & HID & HF17 & HW240 & HPF).
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Hfrapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HC as (Hs7 & Hr18 & (A & H9 & HA64 & HSPILL & Hq232) & HbPH & HbFR & HbFS & HbKN & HFGj & HFSj).
  pose proof HSPILL as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
  pose proof HbFR as (HfgA & HidA & HFGb & HFGl).
  pose proof HbK as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu176 & Hargs).
  pose proof HbRC as (HADpa & HADpp & HADpn).
  pose proof HHB as (Hphinz & HADphi).
  pose proof HFLSI as ((HPRO & _ & Hfrstk & _ & _) & _ & _ & _ & (HinH & _ & _) & _).
  pose proof HPRO as (_ & S120 & S136 & _ & _ & S176 & _ & _ & _ & _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HFN : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HGTv : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HFSv : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKm : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64).
  { rewrite <- Haspz. unfold AC.aspZ.
    pose proof (bv_unsigned_in_range 64 (K11.getr regs 2)) as HR. unfold bv_modulus in HR. cbn in HR. lia. }
  assert (HA0b : 0 <= A0 < 2 ^ 64) by lia.
  pose proof (f12_A_eq regs A A0 H9 HA64 Hr9 HA0b) as EA0. subst A0.
  rewrite Haspz in Hwlo, Hwstk.
  assert (Hfrw2 : fr + FRAME_BYTES <= sp - 2224 \/ sp <= fr).
  { destruct (Hapart 2224 ltac:(lia)) as [Hd|Hd]; rewrite Haspz in Hd; [left|right]; lia. }
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HSPu : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (HspA : sp <= APPMEM_END) by lia.
  assert (HCk : 0 < LOWMEM_END /\ LOWMEM_END < LOWSHADOW_END /\ LOWSHADOW_END < HIGHSHADOW_BEG /\
               HIGHSHADOW_BEG < HIGHMEM_BEG /\ HIGHMEM_BEG < APPMEM_END /\ APPMEM_END <= 2 ^ 64 /\
               AC.GT + 1048576 < HIGHMEM_BEG /\ RT_HI < AC.GT /\ 0 < AC.GT /\
               RT_LO < RT_HI /\ RT_HI < LOWMEM_END /\ 0 < RT_LO /\
               0 < REAL_BCMP /\ REAL_BCMP + 8 < LOWMEM_END /\
               0 < REAL_MEMCMP /\ REAL_MEMCMP + 8 < LOWMEM_END /\
               0 < GOT_CF /\ GOT_CF + 8 < LOWMEM_END /\ 0 < CF /\ CF + 256 < LOWMEM_END /\
               REAL_BCMP + 8 < AC.GT /\ REAL_MEMCMP + 8 < AC.GT /\ GOT_CF + 8 < AC.GT /\ CF + 256 < AC.GT)
    by (unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END, AC.GT, RT_HI, RT_LO,
          REAL_BCMP, REAL_MEMCMP, GOT_CF, CF; lia).
  destruct HCk as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7 & HC8 & HC9 & HC10 & HC11 & HC12 &
                   HC13 & HC14 & HC15 & HC16 & HC17 & HC18 & HC19 & HC20 &
                   HC21 & HC22 & HC23 & HC24).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfrub : fr + FRAME_BYTES <= APPMEM_END) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (f12_in_shadow_fr fr a Hfrapp Hfr8 Ha)).
  assert (HSHlo : LOWMEM_END <= Sfr fr)
    by (destruct (f12_sh_lt (Sfr fr) (HshIS (Sfr fr) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (HSHhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (destruct (f12_sh_lt (Sfr fr + FRAME_SHADOW - 1) (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia))) as (Hi1 & Hi2); lia).
  (* the frame lies wholly above or wholly below its metadata range (it is app memory, low or high) *)
  assert (Harm : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr).
  { pose proof (Hfrapp fr ltac:(lia)) as Ha. pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Hb.
    clear - Ha Hb HFBval HFSval. unfold Sfr, shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
    destruct Ha as [Hlow|Hhigh]; [left|right]; destruct Hb as [Hb|Hb]; Z.div_mod_to_equations; lia. }
  pose proof (AsanRTInv.RT_cells sp mem md HRT) as HAC.
  pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW.
  pose proof HRT as (_ & _ & _ & HCF & _ & HREAL & _).
  assert (Hshstk : stk rsegs mem (Sfr fr) (Sfr fr + FRAME_SHADOW))
    by (apply (f12_shadow_stk mem (Sfr fr) (Sfr fr + FRAME_SHADOW) HSW HshIS); lia).
  (* the spill band [A + 64, A + 288) inside the S-anchored window *)
  assert (Hstksp : stk rsegs mem (A + 64) (A + 288)).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 64) (g_S g) Hwin ltac:(lia)) as (_ & HS1).
    destruct (stk_split rsegs mem (A + 64) (A + 288) (g_S g) HS1 ltac:(lia)) as (HS2 & _). exact HS2. }
  assert (Hwrsp : wr_at rsegs mem (A + 64) 224)
    by (apply (f12_wr_of_stk mem (A + 64) 224 (A + 64) (A + 288) Hstksp); lia).
  assert (Hwrsh : wr_at rsegs mem (Sfr fr) FRAME_SHADOW)
    by (apply (f12_wr_of_stk mem (Sfr fr) FRAME_SHADOW (Sfr fr) (Sfr fr + FRAME_SHADOW) Hshstk); lia).
  assert (Hwrfr : wr_at rsegs mem fr FRAME_BYTES)
    by (apply (f12_wr_of_stk mem fr FRAME_BYTES fr (fr + FRAME_BYTES) Hfrstk); lia).
  (* every live block (the record block, the input block) is app memory below stklo and apart from the frame *)
  assert (Hblk : forall q k x, In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + k ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros q k x Hin Hx.
    destruct (F12.f12_law_blocks APIf _ mem md q k HAH Hin) as (Hqs & Hqapp & Hqnfs).
    pose proof (Hqapp x Hx) as Hxa. pose proof (Hqnfs x Hx) as Hnfs.
    split; [exact Hxa|]. split; [lia|]. intros Hfx.
    destruct Hloc as [(_ & _ & Hreal)|(_ & _ & HinFS & _)].
    - destruct (Hreal x Hfx) as (Hlo & _). lia.
    - exact (Hnfs (HinFS x Hfx)). }
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct Hsp280 as (A280 & H9280 & HA280 & Hq280).
  pose proof (f12_A_eq regs A A280 H9 HA64 H9280 HA280) as E280. subst A280.
  set (st := t_FG (g_in g) j) in *.
  destruct (f12_stk_rwb mem (fr + 336) 72 fr (fr + FRAME_BYTES) Hfrstk ltac:(lia) ltac:(cbn [Z.of_nat]; lia))
    as (junk & Hjl & Hjrw).
  assert (B152 : store_ok rsegs mem (wa (A + 152)) 8%nat = true).
  { replace (A + 152) with (A + 64 + 88) by lia.
    apply (wr_at_store_ok rsegs mem (A + 64) 224 88 8%nat Hwrsp ltac:(lia) ltac:(cbn; lia)). }
  assert (B42 : store_ok rsegs mem (wa (Sfr fr + 42)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 42 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B43 : store_ok rsegs mem (wa (Sfr fr + 43)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 43 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B44 : store_ok rsegs mem (wa (Sfr fr + 44)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 44 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B45 : store_ok rsegs mem (wa (Sfr fr + 45)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 45 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B46 : store_ok rsegs mem (wa (Sfr fr + 46)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 46 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B47 : store_ok rsegs mem (wa (Sfr fr + 47)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 47 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B48 : store_ok rsegs mem (wa (Sfr fr + 48)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 48 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B49 : store_ok rsegs mem (wa (Sfr fr + 49)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 49 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B50 : store_ok rsegs mem (wa (Sfr fr + 50)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 50 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  apply (sl_run_lib regs (Z_to_bv 64 0x820fc) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x82138 /\
       K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
       K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
       K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
       K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
       K11.getr R 25 = Z_to_bv 64 (fragb fr) /\ K11.getr R 26 = K11.getr regs 26 /\
       munch (f12_W A fr sp) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - FN_STACK) sp /\ q64 mem' (A + 152) (b2z (t_tfill (g_in g) j)) /\
       rw_cells rsegs mem' (fr + 336) [CB 72 st] /\ bytes_at rsegs mem' (fragb fr) st /\
       addressable mem' (fr + 336) 72 /\ asan_cells mem' /\ shadow_rw mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the inline run 0x820fc -> 0x82138 (F12.v:1073-1222), discharged from this file's old form f12_run_of_F
       at ExecF.RNG_all; lo := sp - FN_STACK (Hwstk), v25 := b2z (t_tfill (g_in g) j) (Hs9),
       st := t_FG (g_in g) j (the set above) *)
    exact (f12_run_of_F regs mem A fr sp (sp - FN_STACK) _ st junk Hr2 H9 Hr19 Hs9 HGT Hfr8 Hfa ltac:(lia)
             Hspa Hsp0 HspA ltac:(unfold FN_STACK; lia) ltac:(unfold FN_STACK; lia) Hfrw2 Hfrapp
             ltac:(apply (f12_wrsub mem (A + 64) 224 88 8 (A + 152) Hwrsp); lia)
             Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hwstk Hro HAC HSW).
  - (* ---- the exit cut at 0x82138 ---- *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
      E26 & MUt & WMt & ROt & STt & Q152 & RWd & BAs & ADd & ACt & SWt) Hreg Hmat.
    subst pc'.
    assert (Fr2 : K11.getr regs' 2 = K11.getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : K11.getr regs' 3 = K11.getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : K11.getr regs' 4 = K11.getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : K11.getr regs' 8 = K11.getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : K11.getr regs' 9 = K11.getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : K11.getr regs' 18 = K11.getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : K11.getr regs' 19 = K11.getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : K11.getr regs' 20 = K11.getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : K11.getr regs' 21 = K11.getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : K11.getr regs' 22 = K11.getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : K11.getr regs' 23 = K11.getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : K11.getr regs' 24 = K11.getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : K11.getr regs' 25 = Z_to_bv 64 (fragb fr)) by (rewrite Hreg; exact E25).
    assert (Fr26 : K11.getr regs' 26 = K11.getr regs 26) by (rewrite Hreg; exact E26).
    assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite Fr9; exact H9).
    assert (Trg : forall r v, K11.getr regs' r = K11.getr regs r -> rg regs r v -> rg regs' r v)
      by (intros r v E Hr; unfold rg in *; rewrite E; exact Hr).
    assert (TBL : bytes_at rsegs mem' (fr + 336) st)
      by (pose proof RWd as ((_ & Hb) & _); cbn [cells_bytes cbytes] in Hb; rewrite app_nil_r in Hb; exact Hb).
    pose proof Q152 as Q152b. unfold q64 in Q152b.
    (* ---- the write set f12_W, against every carried fact ---- *)
    assert (HWout : forall x, (x < A + 152 \/ A + 160 <= x) -> (x < Sfr fr + 42 \/ Sfr fr + 51 <= x) ->
              (x < fr + 336 \/ fr + 408 <= x) -> (x < sp - 2224 \/ sp <= x) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x).
    { intros x H1 H2 H3 H4. unfold f12_W. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (DISJ : forall q, (A + 152 <= q < A + 160) \/ (Sfr fr + 42 <= q < Sfr fr + 51) \/
               (fr + 336 <= q < fr + 408) \/ (sp - 2224 <= q < sp) \/ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) q).
    { intros q. unfold f12_W. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside]. lia. }
    assert (HshW : forall x, app_mem x -> x < Sfr fr + 42 \/ Sfr fr + 51 <= x).
    { intros x Hx. destruct (Z_lt_le_dec x (Sfr fr + 42)) as [h|h]; [left; exact h|].
      destruct (Z_lt_le_dec x (Sfr fr + 51)) as [h2|h2]; [|right; exact h2].
      exfalso. exact (app_not_shadow x Hx (HshIS x ltac:(lia))). }
    assert (HfrS : forall s, in_shadow s -> s < fr + 336 \/ fr + 408 <= s).
    { intros s Hs. destruct (Z_lt_le_dec s (fr + 336)) as [h|h]; [left; exact h|].
      destruct (Z_lt_le_dec s (fr + 408)) as [h2|h2]; [|right; exact h2].
      exfalso. exact (app_not_shadow s (Hfrapp s ltac:(lia)) Hs). }
    assert (HWsh : forall a, app_mem a -> 0 <= a -> ~ (fr + 336 <= a < fr + 408) ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) (shadow_addr a)).
    { intros a Ha Ha0 Hna.
      pose proof (shadow_of_app a Ha) as Hs. destruct (f12_sh_lt _ Hs) as (Hs1 & Hs2).
      apply HWout; [lia | | exact (HfrS _ Hs) | lia].
      pose proof (f12_sh_out_fr fr a 42 51 Hfr8 Hfr0 Ha0 ltac:(lia)) as Hn. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> (x < fr + 336 \/ fr + 408 <= x) ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x).
    { intros x Hx Hc. apply HWout; [lia | exact (HshW x (Hfrapp x Hx)) | exact Hc |].
      destruct Hfrw2 as [Hd|Hd]; lia. }
    assert (HWA9 : forall x, A + 16 <= x < A + 416 -> (x < A + 152 \/ A + 160 <= x) ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x).
    { intros x Hx Hc. apply HWout; [exact Hc | lia | lia | lia]. }
    assert (HWlo : forall x, 0 <= x < AC.GT -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x).
    { intros x Hx. apply HWout; lia. }
    assert (HWsv : forall x, g_S g - 104 <= x < g_S g -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x).
    { intros x Hx. apply HWout; lia. }
    assert (HWblk : forall q k x, In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + k ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) (shadow_addr x)).
    { intros q k x Hin Hx. destruct (Hblk q k x Hin Hx) as (Hxa & Hxs & Hxf).
      assert (Hx0 : 0 <= x) by (unfold app_mem in Hxa; lia).
      split.
      - apply HWout; [lia | exact (HshW x Hxa) | lia | lia].
      - apply HWsh; [exact Hxa | exact Hx0 | lia]. }
    assert (HWin : 0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) x /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) (shadow_addr x)).
    { intros Hn x Hx. apply (HWblk (g_p g) (g_n g) x); [apply in_or_app; right; exact (HinH Hn) | exact Hx]. }
    (* ---- AH, image ownership, stklo, stkhi across the run ---- *)
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WMt (Z_to_bv 64 a) Hw)).
    assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md /\
      (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md a
             <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md a) /\
      AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
      AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5f & HfsbS & HinFS & Hrec)].
      - (* real-stack arm: every written byte is at or above stklo, or the metadata of a frame byte *)
        assert (HstoreR : forall a, 0 <= a < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
          mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns. apply MUt. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia.
          destruct (DISJ a) as [D|[D|[D|[D|D]]]].
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; right; right.
            exists (fr + 8 * (a - Sfr fr)). split.
            + rewrite (f12_sh_fr fr (8 * (a - Sfr fr)) Hfr8 ltac:(lia)).
              replace (8 * (a - Sfr fr) / 8) with (a - Sfr fr)
                by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity). lia.
            + right; left. destruct (Hreal (fr + 8 * (a - Sfr fr)) ltac:(lia)) as (Hlo & Hhi). lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left.
            destruct (Hreal a ltac:(lia)) as (Hlo & Hhi). lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exact D. }
        exact (F12.f12_law_store APIf (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreR HwmL).
      - (* side arm: the frame is FakeStack slot jj of class 6 (FSREC); the metadata lies below FS + 36864 *)
        destruct Hrec as (FS & jj & HFSw & HFSr & Hjj & Hfre & _ & _).
        destruct (F12.f12_law_fs_place APIf (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FS HAH HFSw HFSr)
          as (HFSgt & HFSst & HFSapp).
        assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
        rewrite HM6 in Hjj.
        assert (Hfrv : fr = FS + 6328320 + jj * 4096)
          by (rewrite Hfre; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq (b & Hb).
          destruct (DISJ q) as [D|[D|[D|[D|D]]]].
          - exact (f12_bytes_mrd mem' (A + 152) _ q Q152b ltac:(rewrite length_le8; lia)).
          - destruct (SWt q (HshIS q ltac:(lia))) as (_ & bb & Hbb). exists bb. exact Hbb.
          - exact (f12_bytes_mrd mem' (fr + 336) _ q TBL ltac:(rewrite HFGl; lia)).
          - destruct STt as (_ & _ & Hsk). destruct (Hsk q ltac:(lia)) as (_ & bb & Hbb). exists bb. exact Hbb.
          - exists b. rewrite (KindBGlue.mbyte_munch rsegs _ mem mem' q MUt Hq D). exact Hb. }
        assert (Hmeta : forall q, fs_meta FS q -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside (f12_W A fr sp) q).
        { intros q Hq.
          assert (HqFS : FS <= q < FS + 36864).
          { pose proof (fs_meta_below FS q Hq) as Hlt. split; [|exact Hlt].
            destruct Hq as [Hc0|[Hc0|[(c & Hc & Hr)|(c & jj' & Hc & Hjj' & Heq)]]].
            - lia.
            - lia.
            - unfold AC.a_fs_hint in Hr. lia.
            - subst q. exact (proj1 (a_fs_flag_range FS c jj' Hc Hjj')). }
          assert (Happq : app_mem q) by (apply HFSapp; lia).
          apply HWout; [lia | exact (HshW q Happq) | lia | lia]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
          ~ (FS <= q < FS + AC.FS_SIZE) ->
          ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
          mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnf Hnsh. apply MUt. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit by lia.
          destruct (DISJ q) as [D|[D|[D|[D|D]]]].
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia|].
            rewrite (f12_sh_fr fr (8 * (q - Sfr fr)) Hfr8 ltac:(lia)).
            replace (8 * (q - Sfr fr) / 8) with (q - Sfr fr)
              by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity). lia.
          - exfalso. apply Hnf. lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exact D. }
        destruct (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    (f12_W A fr sp) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md FS LAWS HAH HFSw
                    ltac:(lia) ltac:(lia) MUt HwmL Hpres Hmeta Hagree)
          as (HA1 & HA2 & HA3 & HA4).
        split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3 | exact HA4]. }
    destruct HAHS as (HAH' & Hown & HSTKlo & HSTKhi).
    (* ---- the frame's 392 metadata bytes, the S-anchored window and FSREC after the run ---- *)
    assert (HshStk : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW))
      by (apply (f12_shadow_stk mem' (Sfr fr) (Sfr fr + FRAME_SHADOW) SWt HshIS); lia).
    assert (Hshnew : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { destruct (f12_bytes_of_stk mem' (Sfr fr) (Z.to_nat FRAME_SHADOW) (Sfr fr) (Sfr fr + FRAME_SHADOW) HshStk ltac:(lia)
                  ltac:(cbn [Z.of_nat]; lia)) as (sh & Hl & Hb).
      exists sh. split; [exact Hb | exact Hl]. }
    assert (Hwin' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (f12_stk_after (f12_W A fr sp) mem mem' _ _ Hwin MUt WMt). intros x Hx.
      destruct (DISJ x) as [D|[D|[D|[D|D]]]].
      - right. exact (f12_bytes_mrd mem' (A + 152) _ x Q152b ltac:(rewrite length_le8; lia)).
      - left. apply HWout; lia.
      - right. exact (f12_bytes_mrd mem' (fr + 336) _ x TBL ltac:(rewrite HFGl; lia)).
      - right. destruct STt as (_ & _ & Hsk). destruct (Hsk x ltac:(lia)) as (_ & bb & Hbb).
        exists bb. exact Hbb.
      - left. exact D. }
    assert (HrecK : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. eapply fsrec_munch_lo with (W := f12_W A fr sp); [exact Hrec | exact HAH | exact MUt | |].
      - intros x Hx. apply HWlo. lia.
      - intros x Hxa Hxf Hxs. apply HWout; [lia | exact (HshW x Hxa) | lia | lia]. }
    (* ---- FRA and ENT at the exit ---- *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr _ regs regs' mem' md md');
        [| exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat].
      apply (F12.f12_fr_run B APIf ra empty FF g fr _ regs mem mem' md (f12_W A fr sp) HFRA MUt WMt ROt).
      - unfold f12_W, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        unfold LOWMEM_END in HSHlo. unfold AC.GT in HGT.
        cbn [disjoint_from]. repeat split; try exact I;
        first [right; lia | left; lia | match goal with |- ?G => idtac "RTDJ:" G end; fail].
      - intros a Ha. destruct (SWt a Ha) as (_ & b & Hb). exists b. exact Hb.
      - exact HAH'.
      - exact HSTKlo.
      - intros x Hx. apply HWfr; lia.
      - exact HWlo.
      - intros A' HA' HA'r x Hx. rewrite (f12_A_eq regs A A' H9 HA64 HA' HA'r) in Hx. apply HWA9; lia.
      - exact HWsv.
      - exact Hshnew.
      - exact Hwin'.
      - exact HrecK.
      - intros a Ha. pose proof (f12_ag_lt a Ha) as Hab.
        apply (addr1_munch (f12_W A fr sp) mem mem' a MUt); [|exact (HAG a Ha)].
        apply HWsh; [exact (addr1_app mem a (HAG a Ha)) | lia | lia].
      - intros a Ha1 Ha2. pose proof (HWA a Ha1 Ha2) as HadA.
        apply (addr1_munch (f12_W A fr sp) mem mem' a MUt); [|exact HadA].
        apply HWsh; [exact (addr1_app mem a HadA) | lia | lia]. }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [| exact Hmat].
      eapply ent_store with (W := f12_W A fr sp); [exact HENT | exact HFRA | exact MUt | | exact HSTKlo
                                                  | exact HSTKhi |].
      - intros x Hx. destruct (DISJ x) as [D|[D|[D|[D|D]]]].
        + right; left. lia.
        + right; right; right. lia.
        + right; right; left. lia.
        + right; left. lia.
        + left. exact D.
      - intros a _ Ho. exact (proj2 (Hown a) Ho). }
    (* ---- the carried facts at the exit ---- *)
    assert (Tq : forall off v, 24 <= off <= 400 -> (off + 8 <= 152 \/ 160 <= off) ->
              q64 mem (A + off) v -> q64 mem' (A + off) v).
    { intros off v Hoff Hoff2 Hqv. apply (f12_q64_mv (f12_W A fr sp) mem mem' (A + off) v Hqv MUt).
      intros x Hx. apply HWA9; lia. }
    assert (Tsp : forall off v, 24 <= off <= 400 -> (off + 8 <= 152 \/ 160 <= off) ->
              spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hoff2 Hs. exists A. split; [exact H9'|].
      apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A off v H9 HA64 ltac:(lia) ltac:(lia) Hs)]. }
    assert (Tad : forall p n, addressable mem p n -> (forall i, 0 <= i < n -> ~ (fr + 336 <= p + i < fr + 408)) ->
              addressable mem' p n).
    { intros p n Had Hn. apply (f12_addr_munch mem mem' _ p n Had MUt). intros i Hi.
      pose proof Had as (Hp0 & _ & _ & Hall). destruct (Hall i Hi) as (Hai & _).
      apply HWsh; [exact Hai | lia | exact (Hn i Hi)]. }
    assert (Tfr : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
              (a + Z.of_nat (length bs) <= fr + 336 \/ fr + 408 <= a) -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2 H3. eapply fl_bytes; [exact Hb | exact MUt |]. intros x Hx. apply HWfr; lia. }
    assert (Tphi : forall a bs, bytes_at rsegs mem a bs -> phi <= a ->
              a + Z.of_nat (length bs) <= phi + AC.a_size (flen g j) -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2. eapply fl_bytes; [exact Hb | exact MUt |]. intros x Hx.
      exact (proj1 (HWblk phi (AC.a_size (flen g j)) x Hinphi ltac:(lia))). }
    assert (TFS : FSj g fr j regs' mem').
    { destruct HFSj as (S104 & S112 & Sbody & Sad & HFI).
      split; [apply Tsp; [lia | lia | exact S104]|].
      split; [apply Tsp; [lia | lia | exact S112]|].
      pose proof (f12_fs_body_len (g_in g) j) as Hbl.
      split; [apply Tfr; [exact Sbody | lia | lia | lia]|].
      split; [apply Tad; [exact Sad | intros i Hi; lia] | exact HFI]. }
    assert (TID : IDb1 g fr j mem').
    { destruct HID as (HIDe & HIDok). split; [|exact HIDok].
      unfold IDBe in *. apply Tfr; [exact HIDe | lia | rewrite f12_ID1_len; lia | rewrite f12_ID1_len; lia]. }
    assert (TFG : FGj g fr j mem').
    { destruct HFGj as (HFGe & Hfok). split; [|exact Hfok].
      assert (LFG : length (t_FG (g_in g) j) = 72%nat) by exact HFGl.
      unfold FGBe in *. apply Tfr; [exact HFGe | lia | rewrite LFG; lia | rewrite LFG; lia]. }
    (* ---- the exit cut Inv_A82138_at ---- *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { split; [exact Hphinz|]. apply Tad; [exact HADphi|].
      intros i Hi Hc. destruct (Hblk phi _ (phi + i) Hinphi ltac:(lia)) as (_ & _ & Hnf). apply Hnf. lia. }
    split.
    { apply (f12_FLSI_mv g j fr regs regs' mem mem' (f12_W A fr sp) A H9 HA64 ltac:(lia) Fr9 MUt).
      - intros x Hx Hc. apply HWA9; lia.
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. unfold fragb. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - exact HWin.
      - exact (fra_stk B APIf ra g fr _ regs' mem' md' HFRA').
      - exact HFLSI. }
    split.
    { apply (f12_LK_mv g j fr regs regs' mem mem' (f12_W A fr sp) Fr21 MUt); [|exact HLK].
      intros x Hx. apply HWfr; lia. }
    exists A, (b2z (t_sum_ok (g_in g) j)).
    split; [exact H9'|].
    split; [unfold rg; exact Fr25|].
    split; [exact HA64|].
    split; [unfold b2z; destruct (t_sum_ok (g_in g) j); lia|].
    split; [reflexivity|].
    split.
    { apply f12_q64_rw3.
      - apply Tq; [lia | lia | exact Hq256].
      - replace (A + 256 + 8) with (A + 264) by lia. apply Tq; [lia | lia | exact Hq264].
      - replace (A + 256 + 16) with (A + 272) by lia. apply Tq; [lia | lia | exact Hq272].
      - eapply wr_at_transport; [apply (f12_wrsub mem (A + 64) 224 192 24 (A + 256) Hwrsp); lia | exact WMt]. }
    split.
    { apply (f12_rw_of_bytes mem' (fragb fr) st 72); [ | exact HFGl | ].
      - apply Tfr; [exact HFGb | unfold fragb; lia | rewrite HFGl; unfold fragb; lia
                   | rewrite HFGl; unfold fragb; lia].
      - eapply wr_at_transport; [|exact WMt].
        apply (f12_wrsub mem fr FRAME_BYTES 2768 (Z.of_nat 72) (fragb fr) Hwrfr);
          [lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | unfold fragb; lia]. }
    split; [apply Tad; [exact HfgA | intros i Hi; unfold fragb; lia]|].
    split; [apply Tad; [exact HADpa | intros i Hi; lia]|].
    split; [apply Tad; [exact HADpp | intros i Hi; lia]|].
    split; [apply Tad; [exact HADpn | intros i Hi; lia]|].
    split; [exact ACt|]. split; [exact SWt|].
    split.
    { eapply fl_bytes; [apply f12_real_bcmp; exact HREAL | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_real_memcmp; exact HREAL | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_got_cf; exact HCF | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_cf_254; exact HCF | exact MUt |].
      intros x Hx. apply HWlo. cbn [length] in Hx. lia. }
    split.
    { eapply fl_bytes; [apply f12_cf_255; exact HCF | exact MUt |].
      intros x Hx. apply HWlo. cbn [length] in Hx. lia. }
    split; [apply Tq; [lia | lia | exact Hq184]|].
    split; [apply Tq; [lia | lia | exact Hq192]|].
    split; [apply Tq; [lia | lia | exact Hq280]|].
    split; [exact TBL|].
    split; [exact ADd|].
    split; [apply Tq; [lia | lia | exact Hq80]|].
    split; [apply Tq; [lia | lia | exact Hq88]|].
    split; [apply Tq; [lia | lia | exact Hq96]|].
    split; [apply Tq; [lia | lia | exact Hq272]|].
    split; [apply Tq; [lia | lia | exact Hq264]|].
    split.
    { (* F16CARRY *)
      split; [exact (proj2 HFGj)|].
      split; [exact TFS|].
      split; [exists (ID1 g j); split; [exact (proj1 TID) | apply f12_ID1_len]|].
      split; [apply Tad; [exact HidA | intros i Hi; lia]|].
      split; [apply Tq; [lia | lia | exact Hq144]|].
      (* F17CARRY *)
      split; [exact (Trg _ _ Fr23 Hs7)|].
      split; [exact (Trg _ _ Fr22 Hs6)|].
      split; [exact (Trg _ _ Fr24 Hs8)|].
      split; [exact (Trg _ _ Fr18 Hr18)|].
      split; [exact (Trg _ _ Fr20 Hs4)|].
      split; [apply Tq; [lia | lia | exact Hq232]|].
      split.
      { destruct HF17 as (A17 & H917 & HA17 & Hq200).
        rewrite (f12_A_eq regs A A17 H9 HA64 H917 HA17) in Hq200. apply Tq; [lia | lia | exact Hq200]. }
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 136 _ H9 HA64 ltac:(lia) ltac:(lia) S136)]|].
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 120 _ H9 HA64 ltac:(lia) ltac:(lia) S120)]|].
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 176 _ H9 HA64 ltac:(lia) ltac:(lia) S176)]|].
      split; [exists A; split; [exact H9' | exact Q152]|].
      split.
      { destruct HW240 as (A24 & H924 & HA24 & w240 & Hq240 & Hw0r & Hwt & Hwf).
        rewrite (f12_A_eq regs A A24 H9 HA64 H924 HA24) in Hq240.
        exists w240. split; [apply Tq; [lia | lia | exact Hq240]|].
        split; [exact Hw0r|]. split; [exact Hwt | exact Hwf]. }
      destruct HPF as (Ab & H9b & HAb & HL & H8).
      rewrite (f12_A_eq regs A Ab H9 HA64 H9b HAb) in H8.
      split.
      { intros H50.
        destruct (HL H50) as ((rb & Hrb & Hrbl) & Hphi).
        destruct HbPH as (HPHg & _ & _).
        assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
        assert (HGl : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
        assert (TG : bytes_at rsegs mem' phi (t_g (g_in g) j))
          by (apply Tphi; [exact (HPHg H50) | lia | rewrite HGl, Hsz; lia]).
        split.
        { exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
          apply Tphi; [apply f12_bytes_first; exact Hrb | lia | rewrite length_firstn, Hsz; lia]. }
        split; [exact TG|].
        split.
        { apply Tphi; [exact Hphi | lia |]. pose proof (f12_phi_len (g_in g) j) as Hpl.
          rewrite Hsz. unfold flen in *. lia. }
        (* rec_inv0: b5_PH / HB / the block law, b5_F17, b5_SPILL's [A+248], b5_K's [A+280] *)
        pose proof HADphi as (Hp0 & _ & Hpe & _).
        split; [lia|].
        split; [unfold AC.a_size in Hpe; lia|].
        split; [exact H50|].
        split; [pose proof (RcParse.ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia|].
        split; [intros a Ha; exact (proj1 (Hblk phi _ a Hinphi ltac:(rewrite Hsz; lia)))|].
        split.
        { destruct HF17 as (A17 & H917 & HA17 & Hq200).
          rewrite (f12_A_eq regs A A17 H9 HA64 H917 HA17) in Hq200. apply Tq; [lia | lia | exact Hq200]. }
        split; [unfold t_blk; apply f12_bytes_bsl; [exact TG | lia | lia | rewrite HGl; lia]|].
        split; [apply f12_bytes_bsl; [exact TG | lia | lia | rewrite HGl; lia]|].
        split; [apply Tq; [lia | lia | exact Hq248] | apply Tq; [lia | lia | exact Hq280]]. }
      intros H8819.
      assert (Hbig : 50 <= flen g j).
      { unfold t_8819 in H8819. apply andb_prop in H8819 as (H1 & _). apply andb_prop in H1 as (H1 & _).
        unfold t_big in H1. apply Z.leb_le in H1. exact H1. }
      assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
      destruct (H8 H8819) as (HPG & (ls & rs & Hq56 & Hls & Hlsl & Hrs & Hrsl & Hmc & Had186) &
                              (ls2 & rs2 & Hq48 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hmc2 & Had180)).
      split.
      { apply (f12_parse_mv g j fr phi mem mem' (f12_W A fr sp) MUt); [ | | exact HPG].
        - intros x Hx. exact (HWblk phi _ x Hinphi ltac:(rewrite Hsz; lia)).
        - intros x Hx. apply HWfr; lia. }
      split.
      { exists (firstn 6 ls), (firstn 6 rs).
        split; [apply Tq; [lia | lia | exact Hq56]|].
        split; [apply Tfr; [apply f12_bytes_first; exact Hls | lia | rewrite length_firstn; lia
                           | rewrite length_firstn; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [apply Tphi; [apply f12_bytes_first; exact Hrs | lia | rewrite length_firstn, Hsz; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [rewrite f12_mcmp_firstn; exact Hmc|].
        apply Tad; [exact Had186 | intros i Hi; lia]. }
      exists (firstn 6 ls2), (firstn 6 rs2).
      split; [apply Tq; [lia | lia | exact Hq48]|].
      split; [apply Tfr; [apply f12_bytes_first; exact Hls2 | lia | rewrite length_firstn; lia
                         | rewrite length_firstn; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [apply Tphi; [apply f12_bytes_first; exact Hrs2 | lia | rewrite length_firstn, Hsz; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f12_mcmp_firstn; exact Hmc2|].
      apply Tad; [exact Had180 | intros i Hi; lia]. }
    (* IFS1 *)
    split; [exact TID|]. split; [exact TFG | exact TFS].
Qed.

(* F12.f12_entry2 (F12.v:1645-1692), its script verbatim except the same three changes. *)
Lemma f12_entry2_src : ltac:(let T := type of (@F12.f12_entry2) in exact T).
Proof.
  intros until j. revert j.
  pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j H g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HC &
    HK & HRC & _ & (v & Ha0 & Hv) & HID & H17 & H240 & H17b).
  pose proof (F12.f12_ff B APIf ra empty FF) as (SEGS & _). subst c. rewrite SEGS.
  pose proof HFRA as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  apply (sl_run_lib regs (Z_to_bv 64 0x820f8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
       K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
       K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
       K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
       K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
       K11.getr R 25 = K11.getr regs 25 /\ K11.getr R 26 = K11.getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the inline run 0x820f8 -> 0x820fc (F12.v:1661-1671), discharged from this file's old form
       f12_entry2_of_F at ExecF.RNG_all *)
    exact (f12_entry2_of_F regs mem v Ha0 Hv).
  - intros R pc' mem' regs' md' (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 &
      E25 & E26) Hreg Hmat.
    subst pc' mem'. rewrite <- SEGS. apply H.
    assert (F2 : K11.getr regs' 2 = K11.getr regs 2) by (rewrite Hreg; exact E2).
    assert (F9 : K11.getr regs' 9 = K11.getr regs 9) by (rewrite Hreg; exact E9).
    destruct (f12_body_regs g j phi fr regs regs' mem F2 F9
                ltac:(rewrite Hreg; exact E18) ltac:(rewrite Hreg; exact E20) ltac:(rewrite Hreg; exact E21)
                ltac:(rewrite Hreg; exact E22) ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E24)
                ltac:(rewrite Hreg; exact E25) HFLSI HLK HC
                (conj HK (conj HRC (conj HID (conj H17 (conj H240 H17b))))))
      as (HF' & HL' & HC' & HP').
    exists phi, regs', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
        [ exact F2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4 | rewrite Hreg; exact E8 | exact F9
        | rewrite Hreg; exact E19 | rewrite Hreg; exact E26 | exact Hmat ]. }
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HF'|]. split; [exact HL'|].
    split; [exact HC' | exact HP'].
Qed.

(* F12.seg_F12 (F12.v:1695-1700) from the two ties and the no-step lemma F12.f12_entry1, as its own proof does. *)
Lemma seg_F12_src : ltac:(let T := type of (@F12.seg_F12) in exact T).
Proof.
  intros until j. intros Hexit.
  assert (Hrun := Hexit). eapply f12_run_src in Hrun; [| eassumption ..].
  split; [eapply F12.f12_entry1 | eapply f12_entry2_src]; first [exact Hrun | eassumption].
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane; F12F's route (C) rows written by a Theorem Labs lane, per the wave lead 11:29Z, with
   a Theorem Labs lane 11:24Z): the twin of f12_run_F in the wave's form.  Everything above this line is unchanged; the old
   lemmas and the three ties keep their own proofs (f12_run_F takes the callee contract, a Theorem Labs lane 09:58Z).
   - The premise `shadow_rw mem` becomes `shadow_rw_on (f12_run_shadow_R fr) mem`.  R is the shadow the run needs
     PRESENT (a Theorem Labs lane 10:34Z: the bytes it reads and the bytes it stores into): the nine metadata bytes the run STORES,
     [Sfr fr + 42, Sfr fr + 51) (`sb zero` at 0x82100 .. 0x82120; the run reads no shadow byte itself), and the
     memcpy call's region through the callee's own predicate, asan_memcpy_c_on.asan_memcpy_shadow_R at the call's
     arguments (D = fr + 336, S = fragb fr, N = 72).  Both lie in the frame's 392 shadow bytes [Sfr fr, Sfr fr + 392)
     (FRAME_SHADOW, the region the plain F12 run reads).
   - The callee premise asan_memcpy_contract_F becomes a Theorem Labs lane's asan_memcpy_contract_F_on
     (lib/A/Prog/asan_memcpy_cF_on.v 95a5333de98 (the blob this tree had at release c5e779efe8c), from a working branch 83ab88c3325; proof
     asan_memcpyF_on.asan_memcpy_holds_F_on).
   - The post's `shadow_rw mem'` becomes `forall P, shadow_rw_on P mem -> shadow_rw_on P mem'`: across the ten stores by
     F12.f12_shadow_rw_write_on, across the normalize by ShadowRwOnT.shadow_rw_on_normalize, across the call by the
     callee's post, and back by ShadowRwOnT.shadow_rw_on_of_rel.
   The script is f12_run_F's, with those three changes and the store permission of the nine metadata bytes read from
   R's first part (F12.f12_shadow_stk_on) instead of from the whole frame shadow. ---- *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c_on asan_memcpy_cF_on.
Module SRW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SRT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module MCO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Module MCF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.

Definition f12_run_shadow_R (fr : Z) (a : Z) : Prop :=
  (Sfr fr + 42 <= a < Sfr fr + 51) \/
  MCO.asan_memcpy_shadow_R (Z_to_bv 64 (fr + 336)) (Z_to_bv 64 (fragb fr)) (Z_to_bv 64 72) a.

Section RunFOn.
Context {fx : K11.FPState}.

Lemma f12_run_F_on : forall (RNG : ExecF.footprint),
  MCF.asan_memcpy_contract_F_on ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr sp lo v25 : Z) (st junk : list byte),
  K11.getr regs 2 = Z_to_bv 64 sp -> rg regs 9 A -> rg regs 19 (Sfr fr) -> rg regs 25 v25 ->
  IMG_HI <= fr -> fr mod 8 = 0 -> fr + FRAME_BYTES <= A -> A + 416 <= APPMEM_END ->
  sp <= A -> 0 <= sp < 2 ^ 64 -> sp <= APPMEM_END ->
  HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= sp ->
  (fr + FRAME_BYTES <= sp - 2224 \/ sp <= fr) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) ->
  wr_at rsegs mem (A + 152) 8 ->
  q64 mem (A + 184) (fr + 336) -> q64 mem (A + 192) (fragb fr) ->
  bytes_at rsegs mem (fragb fr) st -> length st = 72%nat -> addressable mem (fragb fr) 72 ->
  rw_cells rsegs mem (fr + 336) [CB 72 junk] -> length junk = 72%nat ->
  stk rsegs mem lo sp ->
  ro_agree rsegs mem -> asan_cells mem -> SRW.shadow_rw_on (f12_run_shadow_R fr) mem ->
  ExecF.rng RNG (A + 152) 8 -> ExecF.rng RNG (Sfr fr + 42) 9 ->
  ExecF.rng RNG (A + 184) 8 -> ExecF.rng RNG (A + 192) 8 ->
  rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExecF.rng RNG (fr + 336) 72 -> ExecF.rng RNG (fragb fr) 72 ->
  sh_word_rng RNG (fr + 336) 72 -> sh_word_rng RNG (fragb fr) 72 ->
  sh_word_rng RNG (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = MS R K11.fp_regs pc' K11.fp_csr None mem' (K11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x82138 /\
        K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
        K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 18 = K11.getr regs 18 /\
        K11.getr R 19 = K11.getr regs 19 /\ K11.getr R 20 = K11.getr regs 20 /\ K11.getr R 21 = K11.getr regs 21 /\
        K11.getr R 22 = K11.getr regs 22 /\ K11.getr R 23 = K11.getr regs 23 /\ K11.getr R 24 = K11.getr regs 24 /\
        K11.getr R 25 = Z_to_bv 64 (fragb fr) /\ K11.getr R 26 = K11.getr regs 26 /\
        munch (f12_W A fr sp) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
        stk rsegs mem' lo sp /\ q64 mem' (A + 152) v25 /\
        rw_cells rsegs mem' (fr + 336) [CB 72 st] /\ bytes_at rsegs mem' (fragb fr) st /\
        addressable mem' (fr + 336) 72 /\ asan_cells mem' /\
        (forall P : Z -> Prop, SRW.shadow_rw_on P mem -> SRW.shadow_rw_on P mem')))
    (MS (Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x820fc) K11.fp_csr None mem (K11.seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros RNG MCPY regs mem A fr sp lo v25 st junk Hr2 H9 Hr19 Hs9 HGT Hfr8 Hfa HA416 Hspa Hsp0 HspA Hlo HloK Hfrw2 Hfrapp Hw152 Hq184 Hq192 HFGb HFGl HfgA Hjrw Hjl Hwstk Hro HAC HSW
    R152 Rsh42 R184 R192 Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HFN : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HGTv : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKm : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HIH : IMG_HI = 6283264) by reflexivity.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSPu : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (HCk : 0 < LOWMEM_END /\ LOWMEM_END < LOWSHADOW_END /\ LOWSHADOW_END < HIGHSHADOW_BEG /\
               HIGHSHADOW_BEG < HIGHMEM_BEG /\ HIGHMEM_BEG < APPMEM_END /\ APPMEM_END <= 2 ^ 64 /\
               AC.GT + 1048576 < HIGHMEM_BEG /\ RT_HI < AC.GT /\ 0 < AC.GT /\
               RT_LO < RT_HI /\ RT_HI < LOWMEM_END /\ 0 < RT_LO /\
               0 < REAL_BCMP /\ REAL_BCMP + 8 < LOWMEM_END /\
               0 < REAL_MEMCMP /\ REAL_MEMCMP + 8 < LOWMEM_END /\
               0 < GOT_CF /\ GOT_CF + 8 < LOWMEM_END /\ 0 < CF /\ CF + 256 < LOWMEM_END /\
               REAL_BCMP + 8 < AC.GT /\ REAL_MEMCMP + 8 < AC.GT /\ GOT_CF + 8 < AC.GT /\ CF + 256 < AC.GT)
    by (unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END, AC.GT, RT_HI, RT_LO,
          REAL_BCMP, REAL_MEMCMP, GOT_CF, CF; lia).
  destruct HCk as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7 & HC8 & HC9 & HC10 & HC11 & HC12 &
                   HC13 & HC14 & HC15 & HC16 & HC17 & HC18 & HC19 & HC20 &
                   HC21 & HC22 & HC23 & HC24).
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (f12_in_shadow_fr fr a Hfrapp Hfr8 Ha)).
  assert (HSHlo : LOWMEM_END <= Sfr fr)
    by (destruct (f12_sh_lt (Sfr fr) (HshIS (Sfr fr) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (HSHhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (destruct (f12_sh_lt (Sfr fr + FRAME_SHADOW - 1) (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (Harm : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr).
  { pose proof (Hfrapp fr ltac:(lia)) as Ha. pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Hb.
    clear - Ha Hb HFBval HFSval. unfold Sfr, shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
    destruct Ha as [Hlow|Hhigh]; [left|right]; destruct Hb as [Hb|Hb]; Z.div_mod_to_equations; lia. }
  (* route (C): the store permission of the nine metadata bytes, from R's first part *)
  assert (Hshstk : stk rsegs mem (Sfr fr + 42) (Sfr fr + 51)).
  { apply (f12_shadow_stk_on mem (Sfr fr + 42) (Sfr fr + 51)); [| intros a Ha; apply HshIS; lia | lia | lia].
    apply (SRW.shadow_rw_on_mono (f12_run_shadow_R fr) _ mem); [| exact HSW]. intros a Ha.
    unfold f12_run_shadow_R. left. unfold f12_shadow_stk_shadow_R in Ha. exact Ha. }
  assert (Hwrsh : wr_at rsegs mem (Sfr fr + 42) 9)
    by (apply (f12_wr_of_stk mem (Sfr fr + 42) 9 (Sfr fr + 42) (Sfr fr + 51) Hshstk); lia).
  assert (B152 : store_ok rsegs mem (wa (A + 152)) 8%nat = true).
  { pose proof (wr_at_store_ok rsegs mem (A + 152) 8 0 8%nat Hw152 ltac:(lia) ltac:(cbn; lia)) as HB0.
    rewrite Z.add_0_r in HB0. exact HB0. }
  assert (Bk : forall k, 42 <= k < 51 -> store_ok rsegs mem (wa (Sfr fr + k)) 1%nat = true).
  { intros k Hk.
    pose proof (wr_at_store_ok rsegs mem (Sfr fr + 42) 9 (k - 42) 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia)) as HB0.
    replace (Sfr fr + 42 + (k - 42)) with (Sfr fr + k) in HB0 by lia. exact HB0. }
  pose proof (Bk 42 ltac:(lia)) as B42. pose proof (Bk 43 ltac:(lia)) as B43. pose proof (Bk 44 ltac:(lia)) as B44.
  pose proof (Bk 45 ltac:(lia)) as B45. pose proof (Bk 46 ltac:(lia)) as B46. pose proof (Bk 47 ltac:(lia)) as B47.
  pose proof (Bk 48 ltac:(lia)) as B48. pose proof (Bk 49 ltac:(lia)) as B49. pose proof (Bk 50 ltac:(lia)) as B50.
  clear Bk.
  assert (HSf0 : 0 <= Sfr fr) by lia.
  assert (HSf1 : Sfr fr + 51 <= 2 ^ 64) by lia.
  rewrite f12_mkR_of_expand.
  f12_subst_slot H9. rewrite Hr2. f12_subst_slot Hr19.
  try f12_lib_ms.
  f12_sok B152. step.
  f12_sok B46. step.
  f12_sok B47. step.
  f12_sok B48. step.
  f12_sok B49. step.
  f12_sok B42. step.
  f12_sok B43. step.
  f12_sok B44. step.
  f12_sok B45. step.
  f12_sok B50. step.
  step.
  f12_rd Hq184 (A + 184) (fr + 336). step.
  f12_rd Hq192 (A + 192) (fr + 2768). step.
  step. step.
  match goal with
  | |- context [MS _ _ _ _ _ ?m0 (K11.seg_rom _)] => remember m0 as mm eqn:Emm
  end.
  assert (MUst : munch [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm).
  { rewrite Emm.
    repeat (apply munch_write; [ | lia | f12_len | cbn [inside]; rewrite ?length_le8, ?length_le1; cbn [Z.of_nat];
                                 first [left; lia | right; left; lia] ]).
    apply munch_refl. }
  assert (WMst : wmono rsegs mem mm) by (rewrite Emm; repeat apply wmono_write; apply wmono_refl).
  assert (STst : stk rsegs mm lo sp)
    by (rewrite Emm; repeat (apply stk_write; [ | lia | f12_len ]); exact Hwstk).
  (* route (C): every region present before the ten stores is present after them *)
  assert (SWP : forall P : Z -> Prop, SRW.shadow_rw_on P mem -> SRW.shadow_rw_on P mm)
    by (intros P HP; rewrite Emm; repeat (apply f12_shadow_rw_write_on; [ lia | f12_len | ]); exact HP).
  assert (ROmm : ro_agree rsegs mm).
  { apply (sl_ro_keep [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm Hro MUst). intros x Hx.
    cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.outside outside].
    split; [lia|]. split; [lia | exact I]. }
  assert (ACst : asan_cells mm)
    by (apply (fl_asan_cells _ mem mm HAC MUst); intros x Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (BAsrc : bytes_at rsegs mm (fragb fr) st)
    by (rewrite Emm; repeat (apply bytes_at_write_other; [ | lia | f12_len | f12_djl ]); exact HFGb).
  assert (RWdst : rw_cells rsegs mm (fr + 336) [CB 72 junk])
    by (rewrite Emm; repeat (apply rw_cells_frame; [ | lia | f12_len | f12_djl ]); exact Hjrw).
  assert (Q152m : bytes_at rsegs mm (A + 152) (le8 (K11.getr regs 25))).
  { rewrite Emm.
    repeat first [ apply bytes_at_write_same; rewrite ?length_le8; cbn [Z.of_nat]; lia
                 | apply bytes_at_write_other; [ | lia | f12_len | f12_djl ] ]. }
  assert (ADsrc : addressable mm (fragb fr) 72).
  { apply (f12_addr_munch mem mm _ (fragb fr) 72 HfgA MUst). intros i Hi.
    assert (Hsh : in_shadow (shadow_addr (fragb fr + i)))
      by (apply shadow_of_app; apply Hfrapp; unfold fragb; lia).
    assert (Hne : ~ (Sfr fr + 42 <= shadow_addr (fragb fr + i) < Sfr fr + 51))
      by (apply (f12_sh_out_fr fr (fragb fr + i) 42 51 Hfr8 Hfr0 ltac:(unfold fragb; lia));
          unfold fragb; lia).
    destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
    cbn [outside]; repeat split; try exact I;
    first [lia | match goal with |- ?G => idtac "ADFAIL:" G end; fail]. }
  assert (ADdst : addressable mm (fr + 336) 72).
  { apply (f12_addr_of_zero9 _ fr Hfr8 Hfrapp Hfr0). intros k Hk. rewrite Emm.
    destruct (Z.eq_dec k 0) as [->|?]; [replace (Sfr fr + 42 + 0) with (Sfr fr + 42) by lia; f12_zb|].
    destruct (Z.eq_dec k 1) as [->|?]; [replace (Sfr fr + 42 + 1) with (Sfr fr + 43) by lia; f12_zb|].
    destruct (Z.eq_dec k 2) as [->|?]; [replace (Sfr fr + 42 + 2) with (Sfr fr + 44) by lia; f12_zb|].
    destruct (Z.eq_dec k 3) as [->|?]; [replace (Sfr fr + 42 + 3) with (Sfr fr + 45) by lia; f12_zb|].
    destruct (Z.eq_dec k 4) as [->|?]; [replace (Sfr fr + 42 + 4) with (Sfr fr + 46) by lia; f12_zb|].
    destruct (Z.eq_dec k 5) as [->|?]; [replace (Sfr fr + 42 + 5) with (Sfr fr + 47) by lia; f12_zb|].
    destruct (Z.eq_dec k 6) as [->|?]; [replace (Sfr fr + 42 + 6) with (Sfr fr + 48) by lia; f12_zb|].
    destruct (Z.eq_dec k 7) as [->|?]; [replace (Sfr fr + 42 + 7) with (Sfr fr + 49) by lia; f12_zb|].
    replace k with 8 by lia. replace (Sfr fr + 42 + 8) with (Sfr fr + 50) by lia. f12_zb. }
  try unfold fragb in *.
  assert (E336 : bv_unsigned (Z_to_bv 64 (fr + 336)) = fr + 336) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E2768 : bv_unsigned (Z_to_bv 64 (fr + 2768)) = fr + 2768) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.unsigned_lit; lia).
  pose proof MCPY as HM. unfold MCF.asan_memcpy_contract_F_on, ASAN_MEMCPY_K in HM. cbv zeta in HM.
  pose proof (mem_rel_normalize rsegs mm ROmm) as REL.
  eapply ExecF.evtF_cut.
  { eapply MNF.evtF_normalize_ro; [exact ROmm |].
    eapply HM with (RNG := RNG) (src := st) (junk := junk) (lo := lo).
    all: rewrite ?E336, ?E2768, ?E72, ?HSPu.
    all: try change (Z.to_nat 72) with 72%nat.
    - exact (proj1 (bytes_at_rel rsegs mm _ _ _ REL) BAsrc).
    - exact HFGl.
    - apply (rel_rw_norm mm _ _ _ REL); [|exact RWdst].
      intros i Hi. apply ro_addr_false_hi. cbn [cells_size csize Nat.add] in Hi. lia.
    - right; right. lia.
    - lia.
    - exact (rel_addr_norm mm _ _ _ REL ADsrc).
    - exact (rel_addr_norm mm _ _ _ REL ADdst).
    - right. apply Hfrapp. lia.
    - right. apply Hfrapp. lia.
    - right. split; apply Hfrapp; lia.
    - right. lia.
    - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
    - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
    - apply (rel_stk_norm mm _ _ _ REL); [intros x Hx; apply ro_addr_false_hi; lia | exact STst].
    - lia.
    - lia.
    - exact HspA.
    - exact (rel_ac_norm mm _ REL ACst).
    - (* route (C): the callee's region, R's second part, carried across the stores and the normalize *)
      apply (SRT.shadow_rw_on_normalize _ mm ROmm). apply SWP.
      apply (SRW.shadow_rw_on_mono (f12_run_shadow_R fr) _ mem); [| exact HSW]. intros a Ha.
      unfold f12_run_shadow_R. right. exact Ha.
    - exact (mem_inv_normalize rsegs mm).
      - exact Rby.
      - exact Rimg.
      - exact Rstk.
      - exact RngD.
      - exact RngS.
      - exact RngDs.
      - exact RngSs.
      - exact RngKs. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SR0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
    EFc, ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  pose proof (munch_rel rsegs _ mm (normalize rsegs mm) m' m0' REL HR' Hro' MU0) as MUc.
  pose proof (wmono_rel rsegs mm (normalize rsegs mm) m' m0' REL HR' Hro' WM0) as WMc.
  pose proof (ro_agree_same rsegs mm m' ROmm Hro') as ROc.
  pose proof (rel_stk_back m' m0' _ _ HR' ST0) as STc.
  pose proof (rel_rw_back m' m0' _ _ HR' RW0) as RWc.
  pose proof (proj2 (bytes_at_rel rsegs m' m0' _ _ HR') BA0) as BAc.
  pose proof (rel_ac_back m' m0' HR' AC0) as ACc.
  (* route (C): any region present at entry is present at the exit *)
  assert (SRc : forall P : Z -> Prop, SRW.shadow_rw_on P mem -> SRW.shadow_rw_on P m').
  { intros P HP. apply (SRT.shadow_rw_on_of_rel P m' m0' HR'). apply SR0.
    apply (SRT.shadow_rw_on_normalize P mm ROmm). exact (SWP P HP). }
  unfold ASAN_MEMCPY_K in MUc.
  rewrite ?E336 in MUc. rewrite ?E72 in MUc. rewrite ?HSPu in MUc.
  rewrite ?HSPu in STc.
  rewrite ?E336 in RWc. rewrite ?E72 in RWc.
  rewrite ?E2768 in BAc.
  replace (ret_pc (Z_to_bv 64 0x82138)) with (Z_to_bv 64 0x82138)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  do 3 eexists. split; [reflexivity|].
  split; [reflexivity|].
  do 14 (split; [reflexivity|]).
  split.
  { unfold f12_W. eapply munch_trans.
    - eapply munch_weaken; [|exact MUst]. intros z Hz. cbn [outside] in *.
      repeat split; try exact I; lia.
    - eapply munch_weaken; [|exact MUc]. intros z Hz. cbn [outside] in *.
      repeat split; try exact I; lia. }
  split; [eapply wmono_trans; [exact WMst | exact WMc]|].
  split; [exact ROc|].
  split; [exact STc|].
  split.
  { unfold q64. unfold rg in Hs9. rewrite <- Hs9.
    eapply fl_bytes; [exact Q152m | exact MUc |]. rewrite length_le8. intros x Hx. cbn [outside].
    repeat split; try exact I; lia. }
  split; [change (Z.to_nat 72) with 72%nat in RWc; exact RWc|].
  split; [exact BAc|].
  split.
  { eapply (f12_addr_munch _ _ _ (fr + 336) 72 ADdst MUc). intros i Hi.
    assert (Hsh : in_shadow (shadow_addr (fr + 336 + i))) by (apply shadow_of_app; apply Hfrapp; lia).
    destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
    cbn [outside]. repeat split; try exact I.
    all: first [ lia
               | intros HCx; apply (fun H1 => app_not_shadow _ H1 Hsh); apply Hfrapp; lia
               | match goal with |- ?G => idtac "ADDFAIL:" G end; fail ]. }
  split; [exact ACc | exact SRc].
Qed.

End RunFOn.
