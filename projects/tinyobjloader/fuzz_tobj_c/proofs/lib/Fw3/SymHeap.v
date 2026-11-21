(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the five mmap triples written as plain text with the decline premise place_declined_b, etriple_mmap_rw_okJ asking the request's non-refusability and its premise of every admissible address, the step inversions wstep_mmap_inv and wstep_mmap_none_inv called without it; the munmap triples with munmap's exact cut, maps_subtract equals map_remove; the mprotect triples with the premise that the range misses the vDSO pair; the frame obligation's new cases closed by RomBase's tactics). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "ms_mem"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "reg_sv"; "sobj"; "eval"; "ss_next"; "SLit"; "sstate"; "valuation"; "ss_objs"; "sv"; "rm"; "ss_pc"; "obj_range"; "ranges_disjoint"; "ro_addr"; "SVar"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@Corelib.Init.Datatypes"; "bool"; "pair"; "true"; "list"; "option"; "false"; "Some"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_n"; "mmap_place_ok"; "mmap_rw_vm"; "munmap_model"; "mmap_fixed_dead_model"; "mmap_fixed_ok_model"; "mmap_none_vm"; "mmap_place_ok_none"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "page_size"; "map_contains"; "vm_maps"; "with_vmmaps"; "vm_brk"; "TASK_SIZE"; "alloc_top"; "map_has"; "region_free"; "two_pow_64"; "vm_noaccess"; "VmMaps"; "vm_reserved"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "rho_set_rw"; "ok_pframeJ"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple1"; "etriple"; "model_idle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "with_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.Heap"; "S_ret_lit"; "S_ret_fresh"; "enomem_ret"; "rho_after_zero"; "rho_after_unmap"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "zero_range"; "after_sys_mem"; "after_sys"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_grant_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noaccess_b"; "brk_grow_ok"; "brk_model_next"; "mmap_fixed_noaccess_b"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* [linux_place_is] lives in Checks.Placement.  Fw/SysSpec.v:12 and
   Fw/Refusable.v:16 each Require Import it, but `Require Import SysSpec` does
   not re-export those names, so this file needs its own Import; without it the
   restatement below fails with "The reference linux_place_is was not found"
   (measured, SymHeap.v:182). *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable RomBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymSoundR
  SymFrame SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Heap.
Variable segs : list Segment.

Lemma smatch_pending_reunmap : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39S9Q40M1A1M2G2S4aVsegs;R7R6S20G0S37R5S38R4R3A2A4A4S33S32S8G1R3A2S8G1R2A2A2S36Z2Z40A2A2SdS5aSdR1S13R9A1A3S18S17RbR2A2S20S26S26S8G1R6A2M3S32G3S8G1R5A2A2A4A2F_;Fo;S4aVsegs;S52RaS5bS15RaA1R5R4A3A2R9S20G0S37R8S38S53R7S5bS7R7A1R5R4A3A2R6A2A4A4F_;F_;F_;Fn;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md a n Hsp Hnw Hdisj.
  pose proof Hsp as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & (Hall & Hpd & Hfr) & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof (swf_objs S Hwf) as Hobjwf.
  assert (Hur : forall mem x, unmap_range mem a n x = if in_range a n x then None else mem x)
    by (intros; apply unmap_range_at).
  unfold smatch_pending. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|].
  split; [cbn; rewrite eval_set_rm; exact Hpend|].
  split; [exact Hhalt|]. split; [exact Hrom|].
  split.
  { intros x Hro. cbn [with_mem ms_mem]. rewrite Hur. destruct (in_range a n x); [reflexivity|].
    apply Hroc. exact Hro. }
  split; [intros r Hr; rewrite eval_set_rm; apply Hregs; exact Hr|].
  split; [intros r; rewrite eval_set_rm; apply Hfregs|].
  split; [unfold fcsr_match in *; destruct (ss_fcsr S); [exact Hfcsr | rewrite eval_set_rm; exact Hfcsr]|].
  split; [unfold resv_match in *; cbn [with_mem ms_resv]; destruct (ss_resv S); destruct (ms_resv ms);
          rewrite ?eval_set_rm; exact Hresv|].
  split; [|apply Forall_forall; intros p Hp; apply holds_set_rm; exact (proj1 (Forall_forall _ _) Hfacts p Hp)].
  split; [|split].
  - apply Forall_forall. intros o Hin.
    pose proof (proj1 (Forall_forall _ _) Hall o Hin) as Ho.
    pose proof (proj1 (forallb_forall _ _) Hobjwf o Hin) as Howf.
    eapply (obj_holds_set_rm_ext segs rho _ ms); [intros ?; reflexivity | | exact Ho].
    intros off Hoff. cbn [with_mem ms_mem]. rewrite Hur.
    pose proof (Hdisj o Hin) as D. pose proof (proj1 Ho) as HB.
    unfold obj_range, ranges_disjoint in D. cbn [fst snd] in D.
    destruct (in_range a n _) eqn:Hir; [|reflexivity].
    apply in_range_spec in Hir. rewrite u64_of_sum in Hir by lia. lia.
  - apply pairwise_disjoint_set_rm. exact Hpd.
  - intros x Hout. apply outside_all_set_rm in Hout. cbn [with_mem ms_mem set_rm rm]. rewrite !Hur.
    destruct (in_range a n x); [reflexivity|]. apply Hfr. exact Hout.
Qed.

Lemma after_sys_mem_with_mem : ltac2:(tb__ "0|1|
S6S9Q40A1M0G0S23S9Q8A1A1F_;S0S6S5dR3R2R1A3S5eS53R3R1A2R2A2A3Fmem;Fr;Fms;").
Proof using . intros. reflexivity. Qed.

Lemma smatch_after_mem_ret : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39G0S39S9Q40A1M1G1S23S9Q8A1A1F_;M2G2S4aVsegs;S52RaR1A2R9S20G0S37R8S38S53R7R2A2R6A2A4A4S51R5A1S1bVsegs;S4bS52RcR3A2SfRbA1M3R5A3S4dRbS1aG3A1S13RbA1S66G3A1A4S20G0S37R7S38S5dR9R5R4A3R6A2A4A4F_;F_;Fm;Fmem;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r mem m Hsp Hh'.
  rewrite after_sys_mem_with_mem. exact (smatch_after_ret segs _ S tr _ md tr' md' r Hsp Hh').
Qed.

Lemma smatch_after_mem_lit : ltac2:(tb__ "0|4|
S12S11S22S3aA1M0S6S39G0S39S9Q40M1A1M2G2S23S9Q8A1A1F_;M3G3S4aVsegs;S52RaR1A2R9S20G0S37R8S38S53R7R2A2R6A2A4A4S51R5A1S1bVsegs;S52RcR3A2S4dRbS10S8G1R5A2A1S13RbA1SfRbA1A4S20G0S37R7S38S5dR9R5R4A3R6A2A4A4F_;F_;Fm;Fmem;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r mem m Hsp Hh'.
  rewrite after_sys_mem_with_mem. exact (smatch_after_ret_lit segs _ S tr _ md tr' md' r Hsp Hh').
Qed.

Lemma pending_args : ltac2:(tb__ "0|2|
S12S11S22S3aA1M0S6S39S4aVsegs;R5R4S20G0S37R3S38R2R1A2A4A4S1S0S9Q40A1M1S5R3U0A2SeR6ScR5ZaA2A2A3S1S0G1S5R3U1A2SeR6ScR5ZbA2A2A3S1S0G1S5R3U2A2SeR6ScR5ZcA2A2A3S1S0G1S5R3U3A2SeR6ScR5ZdA2A2A3S1S0G1S5R3U4A2SeR6ScR5ZeA2A2A3S0G1S5R3U5A2SeR6ScR5ZfA2A2A3A2A2A2A2A2F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsp.
  repeat split;
  [ exact (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 3 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 4 Hsp ltac:(lia))
  | exact (smatch_pending_gpr segs _ _ _ _ _ 5 Hsp ltac:(lia)) ].
Qed.

Lemma mmap_nw : ltac2:(tb__ "0|3|
S47S9Q40M0A1M1G1S33S32S8G0R2A2S29R1A1A2S42R3A1A2S1S0S26S8G0S2aR2A1A2M2S29R2A1A3S33S32S8G0R3A2G2A2S36Z2Z40A2A2A2F_;Flen;Fa;Fh;").
Proof using .
  intros h a len H. pose proof (urange a) as Ha.
  assert (Hn : 0 <= mmap_nZ len).
  { unfold mmap_nZ, page_round_up_Z, page_size. pose proof (urange len). apply Z.mul_nonneg_nonneg; [|lia]. apply Z.div_pos; lia. }
  assert (Hc : alloc_top h < 2 ^ 64) by (pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
  assert (E : bv_unsigned (mmap_n len) = mmap_nZ len).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. lia. }
  rewrite E. lia.
Qed.

Definition rho_after_zero (rho : valuation) (nx : positive) (r a n : word) : valuation := ltac2:(tb__ "0|0|
S4bS52Vrho;S5cS15Vrho;A1Va;Vn;A3A2Vnx;Vr;A3").

Definition rho_after_unmap (rho : valuation) (nx : positive) (r a n : word) : valuation := ltac2:(tb__ "0|0|
S4bS52Vrho;S5bS15Vrho;A1Va;Vn;A3A2Vnx;Vr;A3").

Definition S_ret_fresh (S : sstate) : sstate := ltac2:(tb__ "0|1|
S4dVS;S1aSfVS;A1M0A1S13VS;A1S66G0A1A4").
Definition S_ret_lit (S : sstate) (z : Z) : sstate := ltac2:(tb__ "0|0|
S4dVS;S10Vz;A1S13VS;A1SfVS;A1A4").

Definition enomem_ret : Z := bv_unsigned (errno_ret ENOMEM).

(* LPS 727298f3: the J-premise's FIRST conjunct is the decline premise [place_declined_b ... =
   false] of [mmap_only_ok] (Fw/SysStep.v; [wstep_mmap_inv] derives it from the step's answer);
   the statement was decoded from this file's [tbs__] table and written out, nothing else
   changed.  The same for the four mmap triples below. *)
Theorem triple1_mmap_rwJ :
  forall (ok : world -> Prop) (J Jf : jpred) (Jo : word -> jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 222 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_noreserve_b (ms_gpr ms 3) = false
        /\ Jf rho tr md
        /\ (forall a,
              mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x, bv_unsigned a <= bv_unsigned x
                              < bv_unsigned a + mmap_nZ (ms_gpr ms 1) ->
                    ro_addr segs x = false)
              /\ Jo a (rho_after_zero rho (ss_next S) a a (mmap_n (ms_gpr ms 1))) tr
                   (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md))) ->
    triple1 segs ok (SPJ segs J S rho)
      (fun w => SPJ segs Jf (S_ret_lit S enomem_ret) rho w
             \/ exists a, SPJ segs (Jo a) (S_ret_fresh S)
                  (rho_after_zero rho (ss_next S) a a (mmap_n (eval rho (reg_sv S 11)))) w).
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_inv Hp Hh H222 Hlen Hmod Hnr Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

(* RESTATED.  The old statement fails here (measured), with the
   build's error:
     SymHeap.v, line 155, characters 61-72: Error: No applicable tactic.
   The encoded statement was decoded from its own [tbs__] table and written out
   explicitly; nothing was re-encoded.  OLD BESIDE NEW, in the J-premise:
     old:  ... /\ exists a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md
                              (ms_gpr ms 1) a
                            /\ DISJ a /\ RO a /\ Jo a ...
     new:  ... /\ mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md
                    (mmap_nZ (ms_gpr ms 1)) = false
                 /\ forall a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md
                                (ms_gpr ms 1) a
                             -> DISJ a /\ RO a /\ Jo a ...
   WHY: at LPS 75d69e00 [wstep_mmap_intro_ok] (Fw/SysStep.v:1257-1267) takes the
   checker's own placement test, [linux_place_is], as its eighth premise, because
   an mmap returns LINUX's address and not merely an admissible one
   (Checks/Placement.v:1012-1017 pins it, :776 makes it unique).  [mmap_place_ok]
   is the four admissibility facts plus [mmap_noreserve_backed_ok] (decoded from
   Fw/SysSpec.v:1638) and is strictly weaker: it admits every free, aligned,
   in-range address, so an existential over it cannot name Linux's.  This is the
   same class as POLICY-PINNED-TO-MODEL.
   WHY THIS SHAPE AND NOT "ADD linux_place_is TO THE EXISTENTIAL": the callers
   get their witness from [vm_room_grant] (Malloc/VmRoom.v:135), whose decoded
   conclusion offers [forall hint flags, mmap_noreserve_b flags = false ->
   mmap_place_ok hint flags md len a] -- an address that is free for ANY hint,
   i.e. exactly not Linux's pick -- so they could never discharge a
   [linux_place_is] premise about their own [a].  What they CAN discharge is
   non-refusability, from [vm_place_available_of_gap] (Fw/Refusable.v:230-245),
   whose four side conditions [vm_room_grant] does supply, including the
   [task_unmapped_base] floor that [mmap_place_ok] alone lacks.  This theorem
   then takes Linux's address itself from [mmap_rw_not_refusable_place]
   (SysSpec.v:1909-1911) and instantiates the caller's universal at it.
   The universal half is NOT a new demand: Malloc/TRRulesK.v:293 already receives
   [Hall] in exactly that form from [HP] and instantiates it at :302, so this
   restatement lets it pass [Hall] straight through instead of repackaging it.
   The sibling [etriple_mmap_rw_anyJ] below is already written this way (:186,
   :191-193); this makes the two theorems one shape.
   THE GUARANTEE IS NOT WEAKENED: both changes are to a HYPOTHESIS, the
   postcondition is untouched, and the universal half is STRONGER than the
   existential half it replaces for every caller that already has it.
   Consumers, all five sites -- Malloc/TRRulesK.v:290, P/Mal_mdirect__G4.v:550
   and :693, U/Mal_mdirect__G4.v:549 and :692 -- apply this theorem and prove the
   J-premise in tactic text, so each gains two visible goals: loud and findable,
   per REPLAY-HYPOTHESIS-NOT-FIELD (amended).  Neither new obligation reaches a
   published file: [mmap_grant_refusable], [mmap_place_ok] and [linux_place_is]
   occur 0 times in Statements.v and 0 times in each of the three
   proofs/*/Proof.v at an earlier revision, with `Qed` n=1 in each Proof.v as the
   firing control. *)
Theorem etriple_mmap_rw_okJ :
  forall (J : jpred) (Jo : word -> jpred) (S : sstate) (rho : valuation),
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 222 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_noreserve_b (ms_gpr ms 3) = false
        /\ mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md
             (mmap_nZ (ms_gpr ms 1)) = false
        /\ (forall a,
              mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x, bv_unsigned a <= bv_unsigned x
                              < bv_unsigned a + mmap_nZ (ms_gpr ms 1) ->
                    ro_addr segs x = false)
              /\ Jo a (rho_after_zero rho (ss_next S) a a (mmap_n (ms_gpr ms 1))) tr
                   (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md))) ->
    etriple segs (SPJ segs J S rho)
      (fun w => exists a,
         SPJ segs (Jo a) (S_ret_fresh S)
           (rho_after_zero rho (ss_next S) a a (mmap_n (eval rho (reg_sv S 11)))) w).
Proof using .
  intros J Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hmod & Hnr & Hrf & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  (* [mmap_rw_not_refusable_place] closes Section MmapRW with `Proof using Hlen`,
     so whether [Hlen] is an explicit argument depends on how the section
     abstracted it; the two forms are tried in order and the goal's type is
     written out, which also does the job of [anyJ]'s [change] at :192. *)
  assert (HLX : exists a,
            mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a
            /\ linux_place_is (m_vmmaps md) (kb_thp (m_kernel md)) (ms_gpr ms 0)
                 (mmap_nZ (ms_gpr ms 1)) a = true)
    by (first
         [ exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hlen Hrf)
         | exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) ]).
  destruct HLX as (a & Hpl & Hlp).
  destruct (HJo a Hpl) as (Hdisj & Hnro & HJoa).
  pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
  eexists. split; [eapply (@wstep_mmap_intro_ok segs tr ms); eassumption|].
  exists a. split.
  - unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
    eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
    apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJoa.
Qed.

Theorem etriple_mmap_rw_failJ :
  forall (J Jf : jpred) (S : sstate) (rho : valuation),
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 222 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md (mmap_nZ (ms_gpr ms 1)) = true
        /\ Jf rho tr md) ->
    etriple segs (SPJ segs J S rho) (SPJ segs Jf (S_ret_lit S enomem_ret) rho).
Proof using .
  intros J Jf S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hmod & Hrf & HJf).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  eexists. split; [eapply (@wstep_mmap_intro_fail segs tr ms); eassumption|].
  split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem etriple_mmap_rw_anyJ :
  forall (J Jf : jpred) (Jo : word -> jpred) (S : sstate) (rho : valuation),
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 222 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_noreserve_b (ms_gpr ms 3) = false
        /\ (mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md (mmap_nZ (ms_gpr ms 1)) = true ->
            Jf rho tr md)
        /\ (forall a,
              mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x, bv_unsigned a <= bv_unsigned x
                              < bv_unsigned a + mmap_nZ (ms_gpr ms 1) ->
                    ro_addr segs x = false)
              /\ Jo a (rho_after_zero rho (ss_next S) a a (mmap_n (ms_gpr ms 1))) tr
                   (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md))) ->
    etriple segs (SPJ segs J S rho)
      (fun w => SPJ segs Jf (S_ret_lit S enomem_ret) rho w
             \/ exists a, SPJ segs (Jo a) (S_ret_fresh S)
                  (rho_after_zero rho (ss_next S) a a (mmap_n (eval rho (reg_sv S 11)))) w).
Proof using .
  intros J Jf Jo S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hmod & Hnr & HJf & HJo).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) (ms_gpr ms 0) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [eapply (@wstep_mmap_intro_fail segs tr ms); eassumption|].
    left. split; [|exact (HJf eq_refl)]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
  - (* arity-robust, as in [etriple_mmap_rw_okJ] above: Section MmapRW closes
       [mmap_rw_not_refusable_place] with `Proof using Hlen`, so [Hlen] may or
       may not be an explicit argument.  Writing the type out also does the job
       of the [change] this branch used to need. *)
    assert (HLX : exists a,
              mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a
              /\ linux_place_is (m_vmmaps md) (kb_thp (m_kernel md)) (ms_gpr ms 0)
                   (mmap_nZ (ms_gpr ms 1)) a = true)
      by (first
           [ exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hlen Hrf)
           | exact (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) ]).
    destruct HLX as (a & Hpl & Hlp).
    destruct (HJo a Hpl) as (Hdisj & Hnro & HJoa).
    pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
    eexists. split; [eapply (@wstep_mmap_intro_ok segs tr ms); eassumption|].
    right. exists a. split.
    + unfold S_ret_fresh, rho_after_zero. rewrite <- G1.
      eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
      apply smatch_pending_rezero; [exact Hsp | lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJoa.
Qed.

Theorem triple1_mmap_noneJ :
  forall (ok : world -> Prop) (J Jf : jpred) (Jo : word -> jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 222 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        place_declined_b (m_kernel md) (m_vmmaps md) (ms_gpr ms 0)
          (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ mmap_noaccess_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
        /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = false
        /\ mmap_noreserve_b (ms_gpr ms 3) = false
        /\ Jf rho tr md
        /\ (forall a,
              mmap_place_ok_none (ms_gpr ms 0) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + mmap_nZ (ms_gpr ms 1)))
              /\ Jo a (rho_after_unmap rho (ss_next S) a a (mmap_n (ms_gpr ms 1))) tr
                   (with_vmmaps (mmap_none_vm (m_vmmaps md) (ms_gpr ms 1) a) md))) ->
    triple1 segs ok (SPJ segs J S rho)
      (fun w => SPJ segs Jf (S_ret_lit S enomem_ret) rho w
             \/ exists a, SPJ segs (Jo a) (S_ret_fresh S)
                  (rho_after_unmap rho (ss_next S) a a (mmap_n (eval rho (reg_sv S 11)))) w).
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hdecl & Hlen & Hna & Hmod & Hnr & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_none_only_ok segs); eassumption.
  - intros w' Hw. destruct (wstep_mmap_none_inv Hp Hh H222 Hlen Hna Hmod Hnr Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. exists a. destruct (HOK a Hpl) as (Hdisj & HJo).
      pose proof Hpl as (_ & _ & Hceil & _). destruct (mmap_nw _ a (ms_gpr ms 1) Hceil) as [En Hnw].
      split.
      * unfold S_ret_fresh, rho_after_unmap. rewrite <- G1.
        eapply smatch_after_mem_ret; [|split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)]].
        apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G1. exact HJo.
Qed.

(* RESTATED.  The old statement fails (measured) at
   SymHeap.v:344 characters
   163-174: "Error: No applicable tactic." -- the [eassumption] closing
   [eapply (@munmap_exact_only_ok segs ms md)].
   At LPS 75d69e00 that lemma (Fw/SysStep.v:1491-1496) takes THREE premises:
   [model_idle m], [map_has (vm_maps h) addr n = true] and
   [maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr +
   bv_unsigned n) = map_remove (vm_maps h) addr].  The J-premise supplies the
   first two and not the third, so [eassumption] has nothing to offer for it.
   The same premise is taken by [wstep_munmap_exact_intro] (:1486) and by
   [wstep_munmap_exact_inv], which :345 calls.
   The encoded statement was decoded from this file's own [tbs__] table and
   written out explicitly; the ONLY difference from the decoded text is the
   added conjunct, placed immediately after the [map_has] one so the existing
   intro pattern reads in order.  Nothing was re-encoded.  OLD BESIDE NEW:
     old:  ... /\ map_has ... = true /\ DISJ /\ J' ...
     new:  ... /\ map_has ... = true
                /\ maps_subtract (vm_maps (m_vmmaps md)) ... = map_remove ...
                /\ DISJ /\ J' ...
   WHY A CONJUNCT OF THE J-PREMISE AND NOT A HYPOTHESIS OF THE THEOREM
   (PREMISE-AS-CONJUNCT): the fact is about the model the CALLER presents at
   the call, so it belongs beside the four facts the caller already proves
   there, where every producer must discharge it loudly.  It is derivable
   rather than new: the model's own [maps_subtract_exact]
   (Common/MmapSim.v:214-222) gives exactly this equation from [0 < n], the
   positivity of every size in the list, the uniqueness of the entry at [addr]
   and pairwise disjointness -- facts a munmap caller holds about its own
   ledger.  So no obligation escapes toward a published file.
   ARITY NOTE, per RECORDED CONSUMERS: FIELD = RE-ENCODE: this unit carries
   TermBlob in 1,513 files, so it is the one unit of this group bound by that
   rule -- but the rule is about a RECORD's arity, and this is a conjunction in
   a theorem's own hypothesis, written out as explicit text rather than
   re-encoded.  No record gains or loses a field here.
   The theorem is WEAKENED in its hypothesis and its conclusion is untouched. *)
Theorem triple1_munmapJ :
  forall (ok : world -> Prop) (J J' : jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 215 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        bv_unsigned (ms_gpr ms 0) mod page_size = 0
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE
        /\ map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
        /\ maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned (ms_gpr ms 0))
             (bv_unsigned (ms_gpr ms 0) + bv_unsigned (mmap_n (ms_gpr ms 1)))
           = map_remove (vm_maps (m_vmmaps md)) (ms_gpr ms 0)
        /\ (forall o, In o (ss_objs S) ->
              ranges_disjoint (obj_range rho o)
                (bv_unsigned (ms_gpr ms 0),
                 bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
        /\ J' (set_rm rho (unmap_range (rm rho) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) tr
             (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) ->
    triple1 segs ok (SPJ segs J S rho)
      (SPJ segs J' (S_ret_lit S 0)
         (set_rm rho (unmap_range (rm rho) (eval rho (reg_sv S 10))
                        (mmap_n (eval rho (reg_sv S 11)))))).
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  (* Hrm is the maps_subtract/map_remove conjunct the restated J-premise adds;
     both [eassumption]s below now have it. *)
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hlen & Hwrap & Hhas & Hrm & Hdisj & HJ').
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold TASK_SIZE in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@munmap_exact_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_munmap_exact_inv segs ms md) in Hw; try eassumption. rewrite Hw.
    split.
    + unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
      eapply smatch_after_mem_lit; [| apply munmap_model_idle; exact Hh].
      apply smatch_pending_reunmap; [exact Hsp | unfold TASK_SIZE in Hwrap; lia | rewrite En; exact Hdisj].
    + cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJ'.
Qed.

(* RESTATED.  The old statement fails (measured) at
   SymHeap.v:428 characters
   66-77: "Error: No applicable tactic." -- the [eassumption] closing
   [eapply (@wstep_munmap_exact_intro segs ms md)].
   Identical class to [triple1_munmapJ] above, in its etriple sibling:
   [wstep_munmap_exact_intro] (Fw/SysStep.v:1479-1488) takes the same third
   premise [maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr +
   bv_unsigned n) = map_remove (vm_maps h) addr] that [munmap_exact_only_ok]
   does, and the J-premise supplied only [map_has].  Decoded from this file's
   own [tbs__] table and written out with the one conjunct added immediately
   after [map_has], so the existing intro pattern reads in order.  Nothing was
   re-encoded; no record gains or loses a field.  Derivable rather than new,
   by the model's [maps_subtract_exact] (Common/MmapSim.v:214-222).
   The munmap pair needs the SAME repair twice: with only triple1_munmapJ
   repaired, the first error is at this theorem (measured), which is the
   sibling-shape prediction holding. *)
Theorem etriple_munmapJ :
  forall (J J' : jpred) (S : sstate) (rho : valuation),
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 215 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        bv_unsigned (ms_gpr ms 0) mod page_size = 0
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE
        /\ map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
        /\ maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned (ms_gpr ms 0))
             (bv_unsigned (ms_gpr ms 0) + bv_unsigned (mmap_n (ms_gpr ms 1)))
           = map_remove (vm_maps (m_vmmaps md)) (ms_gpr ms 0)
        /\ (forall o, In o (ss_objs S) ->
              ranges_disjoint (obj_range rho o)
                (bv_unsigned (ms_gpr ms 0),
                 bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
        /\ J' (set_rm rho (unmap_range (rm rho) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) tr
             (munmap_model md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)))) ->
    etriple segs (SPJ segs J S rho)
      (SPJ segs J' (S_ret_lit S 0)
         (set_rm rho (unmap_range (rm rho) (eval rho (reg_sv S 10))
                        (mmap_n (eval rho (reg_sv S 11)))))).
Proof using .
  intros J J' S rho Hi H17 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hlen & Hwrap & Hhas & Hrm & Hdisj & HJ').
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold TASK_SIZE in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  eexists. split; [eapply (@wstep_munmap_exact_intro segs ms md); eassumption|].
  split.
  - unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
    eapply smatch_after_mem_lit; [| apply munmap_model_idle; exact Hh].
    apply smatch_pending_reunmap; [exact Hsp | unfold TASK_SIZE in Hwrap; lia | rewrite En; exact Hdisj].
  - cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJ'.
Qed.

Theorem triple1_brk_queryJ : ltac2:(tb__ "0|3|
S4eOF_;S1dS9Q40A1M0S1dF_;S11S12S1eVsegs;R5R4A3S4cVsegs;R6R5A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10Zd6A1A3S0S14ScR6ZaA2S10Z0A1A3S22S3aA1M1S6S39S4aVsegs;R9RaS20G1S37R3S38R2R1A2A4A4RdRaR4R2A3RdS40S3bR3A1A1M2S4bRbSfRcA1G2A3R5R3A4F_;F_;Fmd;Fms;Ftr;S4fVsegs;RbS1cVsegs;RaR8R7A4S4eS3G0G0S1cVsegs;RbR1A1S56RaA1S4bR9SfRaA1R1A3R2A5Lb;A2Lw;A4F_;F_;F_;F_;F_;F_;Frho;FS;FJ';FJ;Fok;").
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 H10 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _). rewrite H10 in G0. cbn [eval] in G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@brk_query_only_ok segs); eassumption.
  - intros w' Hw. eapply (@wstep_brk_query_inv segs) in Hw; try eassumption. rewrite Hw.
    exists (vm_brk (m_vmmaps md)). split.
    + unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
    + cbn [w_tr w_cfg fst snd cfg_model]. exact (HJ tr ms md Hsp Hk).
Qed.

Theorem etriple_brk_queryJ : ltac2:(tb__ "0|3|
S1dS9Q40A1M0S1dF_;S11S12S0S23S27A1S54Vsegs;S16R2A1A2S25S27S28A2A3S0S14ScR3Z11A2S10Zd6A1A3S0S14ScR4ZaA2S10Z0A1A3S22S3aA1M1S6S39S4aVsegs;R7R8S20G1S37R3S38R2R1A2A4A4RbR8R4R2A3RbS40S3bR3A1A1M2S4bR9SfRaA1G2A3R5R3A4F_;F_;Fmd;Fms;Ftr;S50Vsegs;S1cVsegs;R8R6R5A4S4eS3G0G0S1cVsegs;R9R1A1S56R8A1S4bR7SfR8A1R1A3R2A5Lb;A2Lw;A3F_;F_;F_;F_;Frho;FS;FJ';FJ;").
Proof using .
  intros J J' S rho Hi H17 H10 HJ.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _). rewrite H10 in G0. cbn [eval] in G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  eexists. split; [eapply (@wstep_brk_query_intro segs tr ms); eassumption|].
  exists (vm_brk (m_vmmaps md)). split.
  - unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
  - cbn [w_tr w_cfg fst snd cfg_model]. exact (HJ tr ms md Hsp Hk).
Qed.

Theorem triple1_brk_growJ : ltac2:(tb__ "0|d|
S4eOF_;S1dS1dS1dS11S12S9Q40M0A1M1S1eVsegs;R7R6A3S4cVsegs;R8R7A3S0S23S27A1S54Vsegs;S16R5A1A2S25S27S28A2A3S0S14ScR6Z11A2S10Zd6A1A3S22S3aA1M2S6S39S4aVsegs;R9RaS20G2S37R3S38R2R1A2A4A4ReRaR4R2A3S1S0G1S40S3bR3A1M3A1RaA3S1S33S8G0S49G3A1A2S8G0RaA2M4A2S1S0S26S35G4S3cA2Z0M5A3S1S0S26S35S8G0S5R4U0M6A2M7A2M8S3cA2G5A3S1S1S34G5G4A2S34G4G8A2A2S1ReS4bRbSfRcA1RaA3R5R3A3S0S1fS63R3G7G7A3S21A3S1SdS5aSdR1S13ReA1A3S18S17ReR2A2S20S26S26S8G0RdA2S8G0S5R7G6A2A2A4A2F_;Fo;S1G1S1S33S8G0RcA2S8G0R1A2M9A2S34G9S8G0S5R6G6A2A2A2A2S0S1fS19Vsegs;R2A2S24A3F_;Fx;ReS52RcS5cS15RcA1RbSbG0S5R5G6A2MaRbA3A3A2R6S3fS64S3bR4A1GaGaA3R4A2A3A2A2F_;A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RcS1cVsegs;RbR8R7A4S4eS4S1cVsegs;RbS56R9A1S4bR8SfR9A1MbR7A3R1A5S1cVsegs;RaS4dR9ScR9ZaA2McS13R9A1GbA4S52R8S5cS15R8A1R7SbG0SeR8GcA2R7A3A3A2R1A5A2Lw;A4F_;F_;F_;F_;F_;Fb0;Frho;FS;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo S rho b0 Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hb0 & Hsb & Halo & Halr & Hlt & HJf & HOK). subst b0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@brk_grow_only_ok segs); try eassumption; lia.
  - intros w' Hw. eapply (@wstep_brk_grow_inv segs) in Hw; try eassumption; [|lia]. destruct Hw as [(Hg & ->) | ->].
    + right. destruct (HOK Hg) as (Hdisj & Hnro & HJo).
      rewrite (brk_eff_grow_aligned (m_vmmaps md) (ms_gpr ms 0) Halo Halr Hlt).
      change (eff_mem ms (mkEffect (ms_gpr ms 0) [] [(vm_brk (m_vmmaps md), (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv)]))
        with (zero_range (ms_mem ms) (vm_brk (m_vmmaps md)) (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv).
      pose proof (urange (ms_gpr ms 0)) as Hr0.
      assert (En : bv_unsigned (ms_gpr ms 0 - vm_brk (m_vmmaps md))%bv = bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md))).
      { rewrite bv_sub_unsigned. apply bv_wrap_small. rewrite two64. lia. }
      split.
      * rewrite <- G0. rewrite after_sys_mem_with_mem.
        eapply smatch_after_ret_expr; [| split; [apply (model_idle_halted Hh)|apply (model_idle_lazy Hh)] | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
        apply smatch_pending_rezero; [exact Hsp | rewrite En; lia | rewrite En | rewrite En].
        -- intros o Ho. replace (bv_unsigned (vm_brk (m_vmmaps md)) + (bv_unsigned (ms_gpr ms 0) - bv_unsigned (vm_brk (m_vmmaps md)))) with (bv_unsigned (ms_gpr ms 0)) by lia. exact (Hdisj o Ho).
        -- intros x Hx. apply Hnro. lia.
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0. exact HJo.
    + left. split.
      * unfold S_ret_fresh. eapply smatch_after_ret; [exact Hsp | exact Hh].
      * cbn [w_tr w_cfg fst snd cfg_model]. exact HJf.
Qed.

(* RESTATED.  The old statement fails (measured) at
   SymHeap.v:558 characters
   166-177: "Error: No applicable tactic." -- the [eassumption] closing
   [eapply (@mprotect_expose_only_ok segs ms md)].
   DIAGNOSED FROM THE SOURCE, NOT FROM THE LOG, so no truncation can reach it:
   [mprotect_expose_only_ok] closes Section MprotectW with
   [Proof using Halign Hlen Hno Hprot Hvd Hwrap] (Fw/SysStep.v:1578), and that
   Section declares SIX hypotheses (:1533-:1541).  The J-premise supplies
   [Hprot], [Halign], [Hlen] and [Hwrap], and [Hno] is [H226] in context, so the
   one with nothing to offer it is
     Hvd : region_free (vdso_reserved (m_kernel m) (vdso_top h)) addr n = true
   (:1541, whose own comment records why it exists: mprotect over the
   vDSO/vvar pair is unmodeled, SysSpec's Section Mprotect).  Counting the
   Section's hypotheses off its declaration at a named sha is exact; nothing
   here was counted inside printed output.
   The encoded statement was decoded from this file's own [tbs__] table and
   written out explicitly; the ONLY difference from the decoded text is the
   added conjunct, placed immediately after the [two_pow_64] one so the
   existing intro pattern reads in order.  Nothing re-encoded; no record gains
   or loses a field, so RECORDED CONSUMERS: FIELD = RE-ENCODE does not bite.
   OLD BESIDE NEW, in the J-premise:
     old:  ... /\ addr + nZ < two_pow_64 /\ map_contains (vm_noaccess ...) ...
     new:  ... /\ addr + nZ < two_pow_64
                /\ region_free (vdso_reserved (m_kernel md)
                     (vdso_top (m_vmmaps md))) (ms_gpr ms 0)
                     (mmap_n (ms_gpr ms 1)) = true
                /\ map_contains (vm_noaccess ...) ...
   THE GUARANTEE IS NOT WEAKENED: the added conjunct is a HYPOTHESIS and the
   postcondition is untouched.  This is the third member of one family in this
   file -- [triple1_munmapJ] and [etriple_munmapJ] each needed
   [maps_subtract ... = map_remove ...], and the mprotect pair needs [Hvd] --
   so the sibling-shape prediction has now held three times running: each round
   moved this file's first error to the next theorem of the same shape. *)
Theorem triple1_mprotect_exposeJ :
  forall (ok : world -> Prop) (J Jf Jo : jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 226 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        bv_unsigned (ms_gpr ms 2) = 3
        /\ bv_unsigned (ms_gpr ms 0) mod page_size = 0
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64
        /\ region_free (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md)))
             (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
        /\ map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ Jf rho tr md
        /\ (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned (ms_gpr ms 0),
                    bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x, bv_unsigned (ms_gpr ms 0) <= bv_unsigned x
                              < bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) ->
                    ro_addr segs x = false)
              /\ Jo (set_rm rho (zero_range (rm rho) (ms_gpr ms 0)
                                   (mmap_n (ms_gpr ms 1)))) tr
                   (mprotect_model_next md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))))) ->
    triple1 segs ok (SPJ segs J S rho)
      (fun w => SPJ segs Jf (S_ret_lit S enomem_ret) rho w
                \/ SPJ segs Jo (S_ret_lit S 0)
                     (set_rm rho (zero_range (rm rho) (eval rho (reg_sv S 10))
                                    (mmap_n (eval rho (reg_sv S 11))))) w).
Proof using .
  intros ok J Jf Jo S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & _).
  (* Hvd is the vdso_reserved conjunct the restated J-premise adds; it is
     Section MprotectW's sixth hypothesis (Fw/SysStep.v:1541) and the one the
     [eassumption] at the end of this proof had nothing to offer. *)
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hvd & Hna & Hmp & HJf & HOK).
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (En : bv_unsigned (mmap_n (ms_gpr ms 1)) = mmap_nZ (ms_gpr ms 1)).
  { unfold mmap_n. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64.
    unfold mmap_nZ, page_round_up_Z, page_size in *. pose proof (urange (ms_gpr ms 1)). pose proof (urange (ms_gpr ms 0)).
    unfold two_pow_64 in Hwrap. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]. }
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mprotect_expose_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_mprotect_expose_inv segs ms md) in Hw; try eassumption. destruct Hw as [-> | (Hb & ->)].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right. destruct (HOK Hb) as (Hdisj & Hnro & HJo). split.
      * unfold S_ret_lit. rewrite <- G0, <- G1. change 0 with (bv_unsigned (Z_to_bv 64 0)).
        eapply smatch_after_mem_lit; [| apply mprotect_model_next_idle; exact Hh].
        apply smatch_pending_rezero; [exact Hsp | unfold two_pow_64 in Hwrap; lia | rewrite En; exact Hdisj | rewrite En; exact Hnro].
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
Qed.

(* RESTATED.  The old statement fails (measured) at
   SymHeap.v:649 characters
   164-175: "Error: No applicable tactic." -- the [eassumption] closing
   [eapply (@mprotect_noop_only_ok segs ms md)].
   The NOOP sibling of [triple1_mprotect_exposeJ], with the same missing
   hypothesis: Section MprotectW (Fw/SysStep.v:1527-1541) declares six, and
   [Hvd : region_free (vdso_reserved (m_kernel m) (vdso_top h)) addr n = true]
   (:1541) is the one this J-premise does not supply.  Read from the Section's
   own text at a named sha -- not from a sibling call, not from an environment
   dump, and not from the twin's argument list.
   Decoded from this file's own [tbs__] table and written out; the ONLY
   difference from the decoded text is the added conjunct, placed after the
   [two_pow_64] one so the existing intro pattern reads in order.  Nothing
   re-encoded, no record touched.  The conjunct is a HYPOTHESIS and the
   postcondition is untouched.
   Sixth member of one family in this file -- munmap x2, mprotect-expose,
   mprotect-noop -- and with each one repaired the first error moves to the
   next theorem of the same shape (measured), which is a positional application naming its
   next defect rather than its arity. *)
Theorem triple1_mprotect_noopJ :
  forall (ok : world -> Prop) (J J' : jpred) (S : sstate) (rho : valuation),
    ok_frameJ segs ok J ->
    ok_pframeJ segs ok J ->
    instr_at segs (ss_pc S) = Some Ecall ->
    reg_sv S 17 = SLit 226 ->
    (forall tr ms md,
        smatch_pending segs rho S (tr, mkCfg ms md) ->
        J rho tr md ->
        bv_unsigned (ms_gpr ms 2) = 3
        /\ bv_unsigned (ms_gpr ms 0) mod page_size = 0
        /\ ms_gpr ms 1 <> Z_to_bv 64 0
        /\ bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64
        /\ region_free (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md)))
             (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true
        /\ map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = false
        /\ map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ region_free (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0)
             (mmap_n (ms_gpr ms 1)) = true
        /\ J' rho tr md) ->
    triple1 segs ok (SPJ segs J S rho) (SPJ segs J' (S_ret_lit S 0) rho).
Proof using .
  intros ok J J' S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  (* Hvd is the vdso_reserved conjunct the restated J-premise adds; it is
     Section MprotectW's sixth hypothesis and the one both [eassumption]s
     below had nothing to offer. *)
  destruct (HJ tr ms md Hsp Hk) as (Hprot & Hal & Hlen & Hwrap & Hvd & Hna & Hmp & Hrf & HJ').
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mprotect_noop_only_ok segs ms md); eassumption.
  - intros w' Hw. eapply (@wstep_mprotect_noop_inv segs ms md) in Hw; try eassumption. rewrite Hw.
    split; [|exact HJ']. unfold S_ret_lit. change 0 with (bv_unsigned (Z_to_bv 64 0)).
    eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
Qed.

Theorem triple1_mmap_fixedJ : ltac2:(tb__ "0|12|
S4eOF_;S1dS1dS1dS1dS11S12S1eVsegs;R7R6A3S4cVsegs;R8R7A3S0S23S27A1S54Vsegs;S16R4A1A2S25S27S28A2A3S0S14ScR5Z11A2S10ZdeA1A3S22S3aA1M0S6S39S4aVsegs;R8R9S20G0S37R3S38R2R1A2A4A4ReR9R4R2A3S1S2S0S9Q40M1A1S5R4U1M2A2M3SaG1Z0M4A2A3A1S1S0S1fS65S5R4U2A2M5S5R4U3A2M6S5R4U5A2M7A3S21A3S1S0S1fS62G5G6G7A3S24A3S1S0S1fS5fG5G6G7A3S24A3S1S33S32S8G1S5R4U0M8A2M9A2MaS29G3A1A2S42S3bR3A1MbA1A2S1S0S26S35GaS3cA2G4A3S1S34G4GaA2S1S0S1fS44S48GbA1G9S2aG3A1McA3S21A3S1S0S1fS3dS3eGbA1G9GcA3S21A3S1S0S1fS60G6A1S24A3S1SdS5aSdR1S13RcA1A3S18S17RcR2A2S20S26S26S8G1S5R6G8A2A2MdS32GdS29S5R6G2A2A1A2A4A2F_;Fo;S1ReRaR5R3A3S1RdS52RaS5bS15RaA1G9GcA3A2MeR5S2fG6R3G9GcA4A3RcGeR5S2eR3G9GcA3A3A2A2A2A2A2A2A2A2A2A2A2A2A2F_;F_;Fmd;Fms;Ftr;S4fVsegs;RcS1cVsegs;RbR7R6A4S4eS4S1cVsegs;RbS55R8S57A2MfR7R1A5S4S1cVsegs;RaS4dR8ScR8ZaA2M10S13R8A1SfR8A1A4S52R7S5bS15R7A1SeR7G10A2S2aSeR7ScR8ZbA2A2A1A3A2M11R1A5S1cVsegs;R9GfG11R1A5A2A2Lw;A4F_;F_;F_;F_;F_;Frho;FS;FJd;FJo;FJf;FJ;Fok;").
Proof using .
  intros ok J Jf Jo Jd S rho Hokf Hokp Hi H17 HJ.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  destruct (pending_args rho S tr ms md Hsp) as (G0 & G1 & _).
  destruct (HJ tr ms md Hsp Hk) as (Hlen & Hsh & Hnn & Hnrw & Hceil & Hal & Hpos & Hfree & Hcont & Hnr & Hdisj & HJf & HJo & HJd).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_nw _ (ms_gpr ms 0) (ms_gpr ms 1) Hceil) as [En Hnw].
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). eapply (@mmap_fixed_only_ok segs ms md); eassumption.
  - intros w' Hw.
    eapply (@wstep_mmap_fixed_inv segs ms md) in Hw; try eassumption. destruct Hw as [-> | [-> | ->]].
    + left. split; [|exact HJf]. unfold S_ret_lit, enomem_ret. eapply smatch_after_ret_lit; [exact Hsp | exact Hh].
    + right; left. split.
      * rewrite <- G0, <- G1. rewrite after_sys_mem_with_mem.
        eapply smatch_after_ret_expr; [| | apply sv_below_reg; exact Hwf | rewrite eval_set_rm; symmetry; exact G0].
        -- apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
        -- split; [| apply mmap_fixed_ok_model_lazy; [exact Hnr | apply (model_idle_lazy Hh)]].
           unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Hnr), m_halted_vm_forget_range.
           apply (model_idle_halted Hh).
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJo.
    + right; right. split.
      * rewrite <- G0, <- G1. unfold S_ret_lit, enomem_ret.
        eapply smatch_after_mem_lit.
        -- apply smatch_pending_reunmap; [exact Hsp | lia | rewrite En; exact Hdisj].
        -- split; [| apply mmap_fixed_dead_model_lazy; apply (model_idle_lazy Hh)].
           unfold mmap_fixed_dead_model, with_mmap_destroyed. rewrite m_halted_vm_forget_range. apply (model_idle_halted Hh).
      * cbn [w_tr w_cfg fst snd cfg_model]. rewrite <- G0, <- G1. exact HJd.
Qed.

End Heap.
