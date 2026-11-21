(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StdModel OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeLaws OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ModelAmb OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8ReadBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8ReadStage.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU8 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesU8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP8 Require Import U8HeapPre U8HBase U8HConv U8TrTail U8RdLib U8RdInv U8RdRules U8RdGrow U8RdChunk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LOOP.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).
Hypothesis Hfile : fs_lookup fs0 path = Some content.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
(* [comment removed for export] *)
Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop).
Hypothesis RM : rule_malloc_grow AI AIm.
Hypothesis RF : rule_free_grow AI AIm.
Hypothesis AIm_perm : forall j X X' s mo, Permutation.Permutation X X' -> AIm j X s mo -> AIm j X' s mo.
Hypothesis AI_vm : forall j X s mo mo', AI j X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_materialized mo' = m_vm_materialized mo -> AI j X s mo'.

Abbreviation GRD := (G_rd path stdin0 fs0 tid).
Abbreviation GPOST := (G_post stdin0 fs0 tid).
Abbreviation RDI := (rd_inv sp0 tid content).
Let L : Z := Z.of_nat (length content).

(* [comment removed for export] *)
Variables (TOOM TREF K : ShapeAlg.TSet).
Hypothesis TOOM_nil : TOOM [].
Hypothesis TREF_nil : TREF [].
Hypothesis K_nil : K [].

(* [comment removed for export] *)
Definition oom_cont : Prop :=
  forall (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
         (x8 x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    RDI (GRD cap) pb buf cap cap M s mo -> 65536 <= cap < 2 ^ 26 -> cap <= L ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 buf)
                                   y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap))
                                   (Z_to_bv 64 0x241f9) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x14b6c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) TOOM.

(* [comment removed for export] *)
Definition ref_cont : Prop :=
  forall (pb : bptr) (buf : Z) (M : word -> option byte) (s : PState) (mo : Model)
         (x8 x18 x24 x25 x26 x27 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    RDI (GRD (2 ^ 26)) pb buf (2 ^ 26) (2 ^ 26) M s mo -> 2 ^ 26 <= L ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 buf)
                                   (Z_to_bv 64 1) y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 (2 ^ 26)) (Z_to_bv 64 3) (Z_to_bv 64 (2 ^ 26))
                                   (Z_to_bv 64 0x241f9) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x14b4c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) TREF.

(* [comment removed for export] *)
Definition end_cont : Prop :=
  forall (j : nat) (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
         (x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    RDI GPOST pb buf cap L M s mo -> AI j [pb] s mo -> 65536 <= cap <= 2 ^ 26 -> L < cap ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                   y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                   (Z_to_bv 64 0x241f9) (Z_to_bv 64 0) x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x14a00) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) K.

Hypothesis HOOM : oom_cont.
Hypothesis HREF : ref_cont.
Hypothesis HEND : end_cont.

(* [comment removed for export] *)
Fixpoint SH (j : nat) (cap : Z) : ShapeAlg.TSet :=
  if L <? cap then K else
  match j with
  | O => TREF
  | S j' => SH j' (2 * cap)   (* tier-2b port: the grow is always served, no out-of-memory branch *)
  end.

Lemma SH_nil : forall j cap, SH j cap [].
Proof.
  induction j as [|j IH]; intros cap; cbn [SH]; destruct (L <? cap); try assumption.
  apply IH.
Qed.

(* [comment removed for export] *)
Lemma mat_G_rd : forall off s mo, GRD off s mo -> m_vm_materialized mo = [].
Proof. intros off s mo HG. unfold G_rd in HG. rewrite HG. reflexivity. Qed.

(* [comment removed for export] *)
Lemma loop_end_case : forall (j : nat) (pb : bptr) (buf cap len : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  RDI (GRD len) pb buf cap len M s mo -> 0 <= len < cap -> 65536 <= cap <= 2 ^ 26 -> L < cap ->
  AI j [pb] s mo ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 0x241f9) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x149d0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) K.
Proof.
  intros until x31. intros RI HLEN HCAP EL HAI.
  eapply (chunk_rz sp0 SP0 ATOPE path stdin0 fs0 tid content Hfile Htid); [exact RI | exact HLEN | lia | |].
  - intros HL. exfalso. fold L in HL. lia.
  - intros _ M' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI' EV.
    eapply (HEND j); [exact RI' | | exact HCAP | exact EL].
    eapply AI_vm; [exact HAI | exact EV |].
    pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI) as [_ [_ HG]].
    pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI') as [_ [_ HG']].
    rewrite (mat_G_rd _ _ _ HG). unfold G_post in HG'. rewrite HG'. reflexivity.
Qed.

Lemma read_loop_rz : forall (j : nat) (pb : bptr) (buf cap len : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  RDI (GRD len) pb buf cap len M s mo -> 0 <= len < cap -> cap * 2 ^ Z.of_nat j = 2 ^ 26 -> 65536 <= cap ->
  AI j [pb] s mo ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 0x241f9) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x149d0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (SH j cap).
Proof.
  induction j as [|j IH]; intros until x31; intros RI HLEN HCAPJ HCAP HAI.
  - (* [comment removed for export] *)
    assert (CE : cap = 2 ^ 26) by (cbn in HCAPJ; lia). subst cap.
    cbn [SH]. destruct (L <? 2 ^ 26) eqn:EL.
    + apply Z.ltb_lt in EL. eapply (loop_end_case 0%nat); [exact RI | exact HLEN | lia | exact EL | exact HAI].
    + apply Z.ltb_ge in EL.
      eapply (chunk_rz sp0 SP0 ATOPE path stdin0 fs0 tid content Hfile Htid); [exact RI | exact HLEN | lia | |].
      * intros _ M' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI' EV.
        (* [comment removed for export] *)
        pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI') as [(Ld & _ & HKL & _) _].
        pose proof (kl_halt _ _ _ HKL) as Hh.
        pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL)) as Hl.
        apply rz_evt; [exact Hh | exact Hl |].
        step. step.
        rewrite unsigned_lit by lia. change (2 ^ 26 ≫ 26) with 1. if_true. apply evt_done.
        eapply HREF; [exact RI' | exact EL].
      * intros HL. exfalso. fold L in HL. lia.
  - (* [comment removed for export] *)
    assert (P : 1 <= 2 ^ Z.of_nat j) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia).
    assert (CJ : 2 * cap * 2 ^ Z.of_nat j = 2 ^ 26) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r in HCAPJ by lia; lia).
    assert (CLT : cap < 2 ^ 26) by nia.
    cbn [SH]. destruct (L <? cap) eqn:EL.
    + apply Z.ltb_lt in EL. eapply (loop_end_case (S j)); [exact RI | exact HLEN | lia | exact EL | exact HAI].
    + apply Z.ltb_ge in EL.
      eapply (chunk_rz sp0 SP0 ATOPE path stdin0 fs0 tid content Hfile Htid); [exact RI | exact HLEN | lia | |].
      * intros _ M' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI' EV.
        assert (HAI' : AI (S j) [pb] s mo').
        { eapply AI_vm; [exact HAI | exact EV |].
          pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI) as [_ [_ HG]].
          pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI') as [_ [_ HG']].
          rewrite (mat_G_rd _ _ _ HG), (mat_G_rd _ _ _ HG'). reflexivity. }
        eapply (grow_step_rz sp0 SP0 ATOPE path stdin0 fs0 tid content AI AIm RM RF AIm_perm j TOOM (SH j (2 * cap)));
          [exact RI' | lia | exact HAI' | exact TOOM_nil | apply SH_nil | |].
        -- intros M2 s2 mo2 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RI2.
           eapply HOOM; [exact RI2 | lia | exact EL].
        -- intros pb' nb M2 s2 mo2 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RI2 HAI2.
           eapply IH; [exact RI2 | lia | exact CJ | lia | exact HAI2].
      * intros HL. exfalso. fold L in HL. lia.
Qed.

(* [comment removed for export] *)
Lemma SH_norm : forall j cap, cap * 2 ^ Z.of_nat j = 2 ^ 26 -> 0 < cap ->
  ShapeAlg.t_eq (ShapeAlg.t_alt2 TOOM (SH j cap)) (ShapeAlg.t_alt2 TOOM (if L <? 2 ^ 26 then K else TREF)).
Proof.
  induction j as [|j IH]; intros cap HC HP.
  - assert (CE : cap = 2 ^ 26) by (cbn in HC; lia). subst cap. cbn [SH]. destruct (L <? 2 ^ 26); apply ShapeAlg.t_eq_refl.
  - assert (P : 1 <= 2 ^ Z.of_nat j) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia).
    assert (CJ : 2 * cap * 2 ^ Z.of_nat j = 2 ^ 26) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r in HC by lia; lia).
    assert (CLT : cap < 2 ^ 26) by nia.
    cbn [SH]. destruct (L <? cap) eqn:EL.
    + apply Z.ltb_lt in EL. replace (L <? 2 ^ 26) with true by (symmetry; apply Z.ltb_lt; lia). apply ShapeAlg.t_eq_refl.
    + apply IH; [exact CJ | lia].
Qed.

(* Tier-2b port: the loop's tree without the out-of-memory alternative. *)
Lemma SH_norm' : forall j cap, cap * 2 ^ Z.of_nat j = 2 ^ 26 -> 0 < cap ->
  ShapeAlg.t_eq (SH j cap) (if L <? 2 ^ 26 then K else TREF).
Proof.
  induction j as [|j IH]; intros cap HC HP.
  - assert (CE : cap = 2 ^ 26) by (cbn in HC; lia). subst cap. cbn [SH]. destruct (L <? 2 ^ 26); apply ShapeAlg.t_eq_refl.
  - assert (P : 1 <= 2 ^ Z.of_nat j) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); lia).
    assert (CJ : 2 * cap * 2 ^ Z.of_nat j = 2 ^ 26) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r in HC by lia; lia).
    assert (CLT : cap < 2 ^ 26) by nia.
    cbn [SH]. destruct (L <? cap) eqn:EL.
    + apply Z.ltb_lt in EL. replace (L <? 2 ^ 26) with true by (symmetry; apply Z.ltb_lt; lia). apply ShapeAlg.t_eq_refl.
    + apply IH; [exact CJ | lia].
Qed.
End LOOP.
