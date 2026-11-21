(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the two lazy mmap triples take a NULL hint, from which the decline test place_declined_b is computed (the mmap inversion wstep_mmap_invA derives it from the step's answer instead); etriple_mmap_lazyA written as plain text, asking the request's non-refusability and its premise of every admissible address, so the grant is at Linux's address; the frame obligation's new cases closed by RomBase's tactics). *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "ss_next"; "SLit"; "reg_sv"; "rm"; "sobj"; "ss_objs"; "SVar"; "obj_range"; "ranges_disjoint"; "ss_pc"; "valuation"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "shadow_addr"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "find_segment"; "machine_state"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "pair"; "None"; "Some"; "fst"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_add_lazy"; "with_vmmaps"; "event"; "ENOMEM"; "errno_ret"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "mmap_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_rw_vm"; "mmap_place_ok"; "mmap_n"; "mmap_rw_model"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* [mmap_grant_refusable] lives in Fw/Refusable.v and `Require Import SysSpec` does not
   re-export it; without it the build fails at SegD_mmap.v:100 (measured), "The
   reference mmap_grant_refusable was not found in the current environment".  Twin of
   the MmapSymA.v fix; the class is REFERENCE-NOT-FOUND ->
   LOOK IN THE UNIT'S OWN MODULES FIRST.  Existing Fw sentence extended, not a new one,
   and this file is not among the seven correct-by-absence files (clause (b) of their
   list). *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep RomBase Refusable.
(* The same class again, twin of the MmapSymA fix: without this line the build
   fails (measured) at SegD_mmap.v:149 "The variable linux_place_is was
   not found in the current environment".  The Refusable line above brings in
   mmap_grant_refusable, and the same restatement also uses [linux_place_is], which
   lives in Checks.Placement and is not re-exported by SysSpec.  Same cure as
   Malloc/HeapEx.v.  Clause (b) re-checked: this file is not among the seven
   correct-by-absence files. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA CompleteA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section M.
Variable segs : list Segment.

Lemma mmap_rw_model_lazy : ltac2:(tb__ "0|1|
S14Q40A1M0S33G0G0S1S24S41R4A1S25A3S1S33S49R5R4R3R2A4S35R2S48R3A1S36S46S34R4A1R3R2A3R4A2A3A3F_;Fa;Flen;Fm;Fflags;").
Proof. intros flags m len a H. unfold mmap_rw_model, with_mmap_backing. rewrite H. reflexivity. Qed.

(* LPS 727298f3: a premise [reg_sv (ax_S A) 10 = SLit 0] (the hint a0 is NULL) is inserted right
   after the [reg_sv (ax_S A) 17 = SLit 222] premise, and nothing else changed (decoded with this
   file's [tbs__] table, the premise added, re-encoded).  The proof computes the decline test
   [place_declined_b ... = false] of the [wstep_mmap_*A] / [mmap_only_okA] lemmas from it. *)
Theorem triple1_mmap_lazyA : ltac2:(tb__ "0|0|
S43OF_;S2fS2fS14Q40A1S2fF_;S19S11S26S14Q40A1A1S1eS31Vsegs;R8R7A3S4fVsegs;R9R8A3S30Vsegs;S7S15R6A1A1R9A3S1S27S3aA1S4cVsegs;S10S15R7A1A1A2S2aS3aS3bA2A3S1S5S9S15R8A1Z11A2S8ZdeA1A3S1S5S9S15R9A1ZaA2S8Z0A1A3S1S5S9S15RaA1ZbA2S8R7A1A3S1S1eS22R8Z1000A2Z0A3S0S1fZ0R9A2S1fR9S23Z2Z3eA2A2A2S26S37A1S1dS33S4dVsegs;RfReR10S28S26S37A1S4aR3S4bR2R1A2A4A5R14R10RfR4R2A4S0S1S24S42S1bR4U2A2S1bR4U3A2S1bR4U5A2A3S25A3S0S1S24S41S1bR4U3A2A1S25A3S0R14R11R10R5R3A4S14Q40A1S47S1bR5U0A2S1bR5U3A2R4S1bR5U1A2R1A5S0SbS40SbR1ScS15R15A1A1A3SfSeR15R2A2S28S1eS1eS12Q40R4A2S20S12Q40R4A2R13A2A4A2F_;Fo;S0S1eS0S21S12Q40R3A2R1A2S1fR1S20S12Q40R3A2R12A2A2A2S1S27S32A1S1cVsegs;R2Z1A3S29S32A1A3F_;Fz;S0S2cS5S5A2S1eS40S2cS5S5A2R2S16R16A1A3S0S21S12Q40S6R16S2bS5S5R3A3A2A2R2A2S1fR2S20S12Q40S6R16S2bS5S5R3A3A2A2S12Q40S6R16S2dS5S5R3A3A2A2A2A2A2S3S0S21S12Q40R6A2S12Q40S1aS12Q40S6R17S17R18A1A2A2R3A2A2A2S1fS12Q40S1aS12Q40S6R17S17R18A1A2A2R3A2A2S20S12Q40R6A2R15A2A2A2A1F_;F_;Fy;Fr;R15R2S3eS3dR13S3cSaR13A1R2S13Q40R11A2A3A2S7S15R14A1A1R2A3R12R7S35R2S13Q40R11A2S36S46S34R5A1S1bR6U1A2R2A3R5A2A3A5A2A2A2F_;Fa;A2A2A2F_;F_;Fmd;Fms;Ftr;S45Vsegs;R12S2eVsegs;R11ReRdRcA5S43S4S2eVsegs;R11S4eRfS8S12Q40S39S38A1A2A1A2ReRdR1A6S2S14Q40A1S14Q40A1S2eVsegs;R11R1A1S18R10S3fS15R10A1SdS7S15R10A1A1A1ScS15R10A1A1S50S7S15R10A1A1A1A4A2S3eS3dRfS3cSaRfA1R1S13Q40RdA2A3A2S7S15R10A1A1R1A3ReR2A6La;A2A2Lw;A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Ftp;Frho;FA;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo A rho tp nlit Hokf Hokp Hst Hi H17 H10 H11 Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit segs rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hdecl : place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
                    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false).
  { destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite G0, H10.
    exact (place_declined_b_null _ _ _). }
  assert (Hn1 : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Hnl : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). apply (mmap_only_okA segs ms md _ Hh H222 Hlen Hmodb Hdecl).
  - intros w' Hw. destruct (wstep_mmap_invA segs ms md _ Hh H222 Hlen Hmodb tr w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hseg & Hxs & HJo).
      pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).     rewrite HnZ in Pceil. rewrite Hn1 in Pfree.
      split.
      * rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1.
        eapply (smatchA_after_grant_lazy segs rho _ tp A tr ms md tr (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) a (Z_to_bv 64 nlit) a
                  (SVar (ss_next (ax_S A))) (Pos.succ (ss_next (ax_S A))) Hsp);
          rewrite ?Hnl; try reflexivity.
        -- unfold mmap_rw_vm. rewrite Hn1. reflexivity.
        -- exact Pal.
        -- change page_size with 4096. exact Hmod.
        -- lia.
        -- pose proof (alloc_top_lt (m_vmmaps md)). unfold two_pow_64 in *. lia.
        -- exact (region_free_app_r _ _ _ _ Pfree).
        -- exact Hseg.
        -- exact Hdisj.
        -- exact Hxs.
        -- apply agree_below_set_rw. lia.
        -- apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
        -- cbn. rewrite Pos.ltb_lt. apply Pos.lt_succ_diag_r.
        -- cbn [eval]. apply rho_set_rw_at.
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1. exact HJo.
Qed.

(* RESTATED.  The old statement fails (measured) at
   SegD_mmap.v:80.  This file builds only once Fw3A/MmapA.v compiles, so the error
   shows only then.  THIRD member of one family (with Fw3A/MmapA.v and
   MallocA/MmapSymA.v):
   [wstep_mmap_intro_okA] takes [linux_place_is] as its last premise and the old
   existential over [mmap_place_ok] cannot name Linux's address.  Restated exactly as
   Fw3A/MmapA.v's etriple_mmap_rw_objA and MallocA/MmapSymA.v's etriple_mmap_rw_symA:
     old:  ... /\ exists a, mmap_place_ok ... a /\ DISJ a /\ SEG a /\ XS a /\ Jo a ...
     new:  ... /\ mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md
                   (mmap_nZ (ms_gpr ms 1)) = false
                /\ forall a, mmap_place_ok ... a -> DISJ a /\ SEG a /\ XS a /\ Jo a ...
   This is the LAZY variant, so [mmap_noreserve_b (ms_gpr ms 3) = true] is unchanged
   and the mapping stays unbacked; the refusability conjunct is about PLACEMENT, not
   backing, so the two are independent and no bound moves.
   Hypothesis-side only: the postcondition is untouched and the universal is stronger
   than the existential for any caller that already quantifies over its address.
   Decoded from this file's own [tbs__] table and written out; NOTHING RE-ENCODED.
   NO IMAGE-DERIVED NUMERAL INTRODUCED -- 222, 17, 11, 1, 4096, 2^62 only, all carried
   over unchanged from the decoded text, none address-shaped. *)
Theorem etriple_mmap_lazyA :
  forall (J : jpredA) (Jo : word -> jpredA) (A : axst) (rho : valuation)
         (tp : list word) (nlit : Z),
    stableA segs (ss_next (ax_S A)) J ->
    instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
    reg_sv (ax_S A) 17 = SLit 222 ->
    reg_sv (ax_S A) 10 = SLit 0 ->
    reg_sv (ax_S A) 11 = SLit nlit ->
    nlit mod 4096 = 0 ->
    0 < nlit < 2 ^ 62 ->
    (forall tr ms md,
        smatch_pendingA segs rho tp A (tr, mkCfg ms md) ->
        J rho tp tr md ->
        mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_noreserve_b (ms_gpr ms 3) = true
        /\ mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md
             (mmap_nZ (ms_gpr ms 1)) = false
        /\ (forall a,
              mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs (ax_S A)) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + nlit))
              /\ (forall z, bv_unsigned a <= z < bv_unsigned a + nlit ->
                    find_segment segs z 1 = None)
              /\ (forall (r : sv * sv) (y : Z),
                    In r (ax_X A) ->
                    bv_unsigned (eval rho (fst r)) <= y
                      < bv_unsigned (eval rho (fst r)) + bv_unsigned (eval rho (snd r)) ->
                    ~ (bv_unsigned a
                         <= bv_unsigned (shadow_addr (bv_unsigned (eval rho (ax_base A))) y)
                         < bv_unsigned a + nlit))
              /\ Jo a (rho_set_rw (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 nlit)))
                         (ss_next (ax_S A)) a) tp tr
                   (vm_add_lazy a (Z_to_bv 64 nlit)
                      (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)))) ->
    etriple segs (SPA segs J A rho tp)
      (fun w => exists a,
         SPA segs (Jo a)
           (ax_setS A (S_after (ax_S A) (SVar (ss_next (ax_S A)))
                         (ss_objs (ax_S A)) (Pos.succ (ss_next (ax_S A)))))
           (rho_set_rw (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 nlit)))
              (ss_next (ax_S A)) a) tp w).
Proof using .
  intros J Jo A rho tp nlit Hst Hi H17 H10 H11 Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_lit segs rho tp A tr ms md nlit Hsp H11 Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hrf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hdecl : place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
                    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false).
  { destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite G0, H10.
    exact (place_declined_b_null _ _ _). }
  assert (Hn1 : mmap_n (ms_gpr ms 1) = Z_to_bv 64 nlit) by (unfold mmap_n; rewrite HnZ; reflexivity).
  assert (Hnl : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (apply u64_lit; lia).
  destruct (ltac:(first
    [ exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hlen Hrf)
    | exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) ])
    : exists a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a
                /\ linux_place_is (m_vmmaps md) (kb_thp (m_kernel md)) (ms_gpr ms 0)
                     (mmap_nZ (ms_gpr ms 1)) a = true) as (a & Hpl & Hlp).
  change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
  destruct (HOK a Hpl) as (Hdisj & Hseg & Hxs & HJo).
  eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb Hdecl tr a Hp Hpl Hlp)|].
  exists a. pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).     rewrite HnZ in Pceil. rewrite Hn1 in Pfree.
  split.
  - rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1.
    eapply (smatchA_after_grant_lazy segs rho _ tp A tr ms md tr (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) a (Z_to_bv 64 nlit) a
              (SVar (ss_next (ax_S A))) (Pos.succ (ss_next (ax_S A))) Hsp);
      rewrite ?Hnl; try reflexivity.
    + unfold mmap_rw_vm. rewrite Hn1. reflexivity.
    + exact Pal.
    + change page_size with 4096. exact Hmod.
    + lia.
    + pose proof (alloc_top_lt (m_vmmaps md)). unfold two_pow_64 in *. lia.
    + exact (region_free_app_r _ _ _ _ Pfree).
    + exact Hseg.
    + exact Hdisj.
    + exact Hxs.
    + apply agree_below_set_rw. lia.
    + apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
    + cbn. rewrite Pos.ltb_lt. apply Pos.lt_succ_diag_r.
    + cbn [eval]. apply rho_set_rw_at.
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite (mmap_rw_model_lazy _ md _ a Hnr), Hn1. exact HJo.
Qed.

End M.
