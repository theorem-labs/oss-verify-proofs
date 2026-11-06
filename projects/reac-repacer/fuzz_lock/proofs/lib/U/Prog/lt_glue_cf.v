(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_cg.v, with its module paths and module names changed; 60 of its 130 lines of code are new or changed and 615 lines of the source are left out. *)
(* The crash-free twin of lt_glue.v: g_run_cf and g_check_cf, the lemmas g_run and g_check with SRcf B in place
   of SR (ms_segs B), over libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v
   (25e3d17bdb50) llvm_run_norm_cf. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr lt_glue.
Import ListNotations.
Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.

Lemma evt_SRcf_canon_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof. rewrite <- SEGS. exact (evt_SRcf_canon B). Qed.

Lemma llvm_run_norm_cf : forall (fx' : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MState.MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' -> ro_same rsegs mem m' ->
     SRcf B (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros fx' regs pc mem md Q P Hh Hl Hro HE Hform HK.
  apply (evt_SRcf_canon_r _ (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P);
    [| exact Hh | exact Hl |].
  - change (RegisterBridge.canonical_register_state (YK11.mkst regs pc mem (YK11.seg_rom rsegs)))
      with (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize; [exact lf_wx | exact Hro | exact HE].
  - intros ms' (can & (s0 & HQ & Hrel & Hsame) & Heq).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MState.MS] in *. subst.
    destruct (lf_eqv_mkst R F pc' fc cm (seg_rom rsegs) ms' Heq) as [Ems Hx]. rewrite Ems.
    exact (HK R F pc' fc m0' HQ _ cm Hx E8 Hsame).
Qed.

Lemma g_run_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
        (S - stk <= x < S) \/ exists y k, lf_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     lf_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     SRcf B (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (llvm_run_norm_cf fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | exact Hc | exact HS | exact MU' | exact WM' | exact Hro' | exact HW].
Qed.

(* the call of a harness function whose contract keeps every block and leaves no footprint of its own *)
Lemma g_check_cf : forall stk S L0 A0 mem0 md0 regs mem md L A (K : Z) (bres : sbound) (pc : Z) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md ->
  YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 -> S - stk <= spZ regs - K -> spZ regs <= S -> 0 <= K ->
  SRcf B (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md)
    (fun c' => exists (fx2 : YK11.FPState) L' A' regs' mem' md',
       c' = mkCfg (@YK11.mkst fx2 regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md' /\
       frm_zero (@fp_csr fx2) /\
       call_post_k B (aa_MR API) K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
       blocks L' A' = blocks L A /\
       blocks_kept B L A mem mem' (fun _ => False) /\
       guard_kept B mem mem' /\
       ro_agree (ms_segs B) mem' /\
       res_ok_slots A' bres /\
       st_init_done A' = true) ->
  (forall (fx2 : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx2) ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' ->
     regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SRcf B (mkCfg (@YK11.mkst fx2 regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 regs mem md L A K bres pc P FR Hc HS H1 H2 HK0 HC KONT.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B); [exact HC|].
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost | lia | lia | | | | | |
      exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (KONT fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2).
  - apply (g_above B API ERRNO_LOW stk S L A regs mem md K (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS HK0).
    intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

End G.
