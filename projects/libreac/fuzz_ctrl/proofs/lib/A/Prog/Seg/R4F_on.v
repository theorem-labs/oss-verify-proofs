(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 554 of its 653 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P4.v; 138 of its 266 lines of code are new or changed and 525 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P4F_on.v, with its module names, addresses and numbers changed; 87 of its 127 lines of code are new or changed and 226 lines of the source are left out. *)
(* lib/A/Prog/Seg/R4F_on.v -- route (C) twin of Seg/R4F.v's r4_evt_F (Seg/R4F.v is not in this delivery) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane).  Written by
   a Theorem Labs lane for the glue of seg_R4 (lib/A/ACtlG/R4.v), with a Theorem Labs lane's standing consent and
   a Theorem Labs lane's go (12:55Z / 13:0xZ).  Seg/R4F.v (not in this delivery) is not edited by this file; its last version (the BASE blob below) differs from a working branch's blob 3325917d8e2 only in the module qualification of MState in r4_evt_F's proof; this file
   is a NEW file beside it.  rule 24: no function proved (kind: segment run lemma, footprint form).

   BASE: the text of r4_evt_F in a Theorem Labs lane's fold a working branch 4bae33fdf54 (Seg/R4F.v (not in this delivery) blob
   061393e6fc5: every MState.unsigned_lit in the full path of its copy, A.Tk.UL.MState), with ONE change each way, as
   the callee's own twin (asan_memset_cF_on.v) makes it:
     - the universal premise `shadow_rw m` becomes `shadow_rw_on (r4_evt_shadow_R D) m`;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`;
   and the callee contract asan_memset_contract_F becomes asan_memset_contract_F_on (a Theorem Labs lane, asan_memset_cF_on.v
   6137e3c5f10; proof asan_memsetF_on.v 34752af7b24 asan_memset_holds_F_on; both by path from
   a working branch 83ab88c3325).  Every other binder, premise and post conjunct is r4_evt_F's.

   THE REGION.  The segment's own accesses (li a2,72 ; ld a0,48(s1) ; li a1,0 ; jal) touch no shadow byte.  The callee
   reads (and never stores) the shadow words of its destination, asan_memset_shadow_R a0 a2 = sh_word_on D 72 at this
   call site (a0 = D, a2 = 72).  So r4_evt_shadow_R D := sh_word_on D 72, the contiguous span of aligned shadow words
   of [D, D + 72).  The callee window [spv - ASAN_MEMSET_K, spv) is NOT in it: the callee's _on contract does not
   ask for its shadow.

   THE PROOF is r4_evt_F's, with the two shadow lines replaced: the premise goes to the normalized memory by
   ShadowRwOnT.shadow_rw_on_rel (in place of R4.r4_sw_norm), the callee's premise is that fact at
   asan_memset_shadow_R (Z_to_bv 64 D) (Z_to_bv 64 72), and the post's transport comes back from the normalized run's
   memory by shadow_rw_on_rel / shadow_rw_on_of_rel (in place of R4.r4_sw_back). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c asan_memset_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R4.
(* route (C): the region form and its transports, the callee's _on contract; Required, never Imported. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_cF_on.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module MSO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c_on.
Module MSFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_cF_on.

(* The shadow the run reads: the callee's asan_memset_shadow_R at a0 = D, a2 = 72. *)
Definition r4_evt_shadow_R (D a : Z) : Prop := SWO.sh_word_on D 72 a.

(* ---- r4_evt_F (R4F.v:39) in route (C) form. ---- *)
Lemma r4_evt_F_on : MSFO.asan_memset_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 48) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - 2208 \/ spv <= D) ->
    6283264 <= D -> 6283264 <= lo ->
    stk rsegs m lo spv -> lo + 2208 <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (r4_evt_shadow_R D) m -> ro_agree rsegs m ->
    (* the segment's own access: the spill load [A + 48, A + 56) *)
    ExecF.rng RNG (A + 48) 8 ->
    (* the callee's regions (asan_memset_contract_F_on's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG D 72 ->
    sh_word_rng RNG D 72 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81588) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 21 = s5 /\
         munch [(D, D + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m') /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81578) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk -> -> HA HD Hspv HLD RW HAD HE HA7 HRT HSEP HDGT HLGT ST HLO HHM HAE HAC HSW HRO
    G48 Gby Gimg Gstk Gd Gshd Gshs.
  unfold MSFO.asan_memset_contract_F_on, ASAN_MEMSET_K in MSET. cbv zeta in MSET.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (RWn : rw_cells rsegs (normalize rsegs m) D [CB 72 junk]).
  { apply (R4.r4_rw_norm m _ D _ REL); [|exact RW].
    intros i Hi. cbn [cells_size csize] in Hi. apply R4.r4_notro.
    pose proof (rw_cells_bound rsegs m D _ RW) as Hb.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hb. lia. }
  assert (STn : stk rsegs (normalize rsegs m) lo spv).
  { apply (R4.r4_stk_norm m _ lo spv REL); [|exact ST]. intros x Hx. apply R4.r4_notro. lia. }
  pose proof (R4.r4_ac_norm m _ REL HAC) as ACn.
  pose proof (SROT.shadow_rw_on_rel _ m _ REL HSW) as SWn.
  pose proof (R4.r4_addr_rel m _ D 72 REL HAD) as HADn.
  step. step. step. step.
  eapply ExecF.evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    eapply MSET with (RNG := RNG) (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWn.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HADn.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HE.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. exact HA7.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HRT.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSEP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact STn.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact ACn.
    - (* the callee's region is this run's: asan_memset_shadow_R (Z_to_bv 64 D) (Z_to_bv 64 72) = sh_word_on D 72 *)
      unfold MSO.asan_memset_shadow_R.
      rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact SWn.
    - apply mem_inv_normalize.
    - exact Gby.
    - exact Gimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (s0' & PO & MR & RS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MUc & WMc & MIc & STc & RWc & HAC' & HSW').
  subst s0'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  unfold ASAN_MEMSET_K in MUc, STc.
  rewrite ED in MUc. rewrite E72 in MUc. rewrite Esp in MUc. rewrite Esp in STc.
  rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in RWc by lia.
  change (Z.to_nat 72) with 72%nat in RWc. change (0 mod 256) with 0 in RWc.
  replace (ret_pc (Z_to_bv 64 0x81588)) with (Z_to_bv 64 0x81588) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' mem' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  apply ExecF.evtF_done. exists R', mem'.
  split; [unfold MS; subst; reflexivity|].
  subst R'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) mem' m0' REL Hmem RS MUc)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mem' m0' REL Hmem RS WMc)|].
  split; [exact (ro_agree_same rsegs m mem' HRO RS)|].
  split; [exact (R4.r4_stk_back mem' m0' lo spv Hmem STc)|].
  split; [exact (R4.r4_ac_back mem' m0' Hmem HAC')|].
  split; [| exact (R4.r4_rw_back mem' m0' D _ Hmem RWc)].
  (* any region held before the run is held after it: to the normalized memory, across the callee, and back *)
  intros P HP.
  exact (SROT.shadow_rw_on_of_rel P mem' m0' Hmem (HSW' P (SROT.shadow_rw_on_rel P m _ REL HP))).
Qed.
