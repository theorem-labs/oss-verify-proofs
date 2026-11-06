(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib RefMemcpyLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MemcpyBase Memcpy.
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RefStep RefStep3.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_ameta1.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac am_calls Hp HS Hag HI HW t := sys_calls Hp HS Hag HI HW t ltac:(fun t => mach_jal Hp HS).

Section AllocMeta.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.
Let MM := mmap_refines. Let MF := mmap_fixed_refines.
Let MP := mprotect_refines. Let MU := munmap_refines.


Theorem alloc_meta_refines : alloc_meta_stmt.
Proof.
  unfold alloc_meta_stmt.
  intros md regs mm rom s sp ret P L Hp Hvm Hag H2 Hal Hlo0 Hlo Hhi Hhi64 Hwt Hstk H1 Hret H4 HS HK.
  pose proof (minv_init s sp 144 Hlo0 Hlo ltac:(lia) Hhi Hhi64 Hwt) as HI.
  pose proof (mwin_init s mm sp 144 Hstk) as HW.
  rewrite <- (with_vmmaps_same md), <- Hvm. note_win HI.
  rewrite (m_alloc_meta_pieces (at_ sp (-64))) in HS |- *.
  unfold am_init in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x34). mark_frame 56.
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x40).
  (* [comment removed for export] *)
  mach_cut HS Hag HI HW unit (fun _ : unit => (pc+ PC_ALLOC_META 0xa4))
     [1;5;6;7;9;10;11;12;13;14;15;16;17;20;28;29;30;31]%Z (fun (_ : unit) (_ : bvmap 5 word) (_ : mstate) => True)
     (bv_unsigned sp - 64) (bv_unsigned sp - 56) as CUT Kx.
  - mstepx Hp HS Hag HI HW HK Hret am_calls.
    2: { (* [comment removed for export] *) use_cut_kx CUT Kx Hag HI HS. }
    (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x84).
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (m_scan_auxv _ _ _ _) ?K2 _) _) => set (Ks := K2) in HS |- *
    end.
    lazymatch goal with
    | |- realizes _ (mkCfg (mkst ?Rf _ ?mmL _) (with_vmmaps _ ?md0)) (tshape _ ?L0) =>
    lazymatch type of HS with tsafe _ ?P0 =>
    enough (LOOP : forall (fuel : nat) (auxv i secret : word) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
      magree s' mm' -> minv s s' ->
      (forall a : word, ms_lo s <= bv_unsigned a < ms_hi s ->
                         ~ (bv_unsigned sp - 64 <= bv_unsigned a < bv_unsigned sp - 56) -> mm' a = mmL a) ->
      rdn ml_segs mm' (v_addi sp (-64)) 8 = Some (word_to_le_bytes 8 secret) ->
      (forall a : word, bv_unsigned sp - 64 <= bv_unsigned a < bv_unsigned sp - 56 -> mm' a <> None) ->
      (forall r : reg, wreg [1;5;6;7;9;10;11;12;13;14;15;16;17;28;29;30;31]%Z r = false -> getr R' r = getr Rf r) ->
      getr R' 10 = auxv -> getr R' 9 = i ->
      tsafe ((sec <- m_scan_auxv fuel auxv i secret ;; Ks sec) s') P0 ->
      realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_META 0x84) mm' rom) (with_vmmaps (ms_vm s') md0))
               (tshape ((sec <- m_scan_auxv fuel auxv i secret ;; Ks sec) s') L0))
    end end.
    { eapply (LOOP AUXV_FUEL);
        [ exact Hag | exact HI | win_pres | frame_rd | win_nn | keep_tac
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | exact HS ]. }
    (* [comment removed for export] *)
    clear HS Hag.
    induction fuel as [|fuel IH]; intros auxv i secret s' mm' R' Hag HI' HJ Hslot HJn Hkeep Ha0 Hs1 HS.
    { exfalso. clear -HS. cbn [m_scan_auxv MallocTree.mbind mcrash tbind tsafe] in HS. exact HS. }
    clear HI; rename HI' into HI; note_win HI. keep_facts Hkeep.
    unfold m_scan_auxv in HS |- *; fold m_scan_auxv in HS |- *. munf. mnorm HS.
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x8c).
    mstepx Hp HS Hag HI HW HK Hret am_calls.
    + (* [comment removed for export] *)
      mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x78).
      mach_passert HS.
      destruct (tsafe_ld_inv _ _ _ _ HS) as (rb & Hokr & Hrdr & Hvr & EQ); rewrite EQ in HS; rewrite EQ; clear EQ.
      pose proof (rdn_length _ _ _ _ _ Hrdr) as Hlenr.
      mach_jal Hp HS.
      match goal with Hb : c_ltu (le_val _) (Z_to_bv 64 (2 ^ 64 - 24)) = true |- _ => apply c_ltu_lt in Hb; rename Hb into Hval end.
      change (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 24))) with (2^64 - 24) in Hval.
      lazymatch type of Hval with bv_unsigned ?v < _ => pose proof (u64_range v) as Hval0 end.
      pose proof (acc_ok_cases _ _ _ Hokr) as Hdisj.
      cbn [MallocTree.ms_lo MallocTree.ms_hi MallocTree.ms_mem MallocTree.ms_vm MallocTree.upd] in Hdisj.
      rewrite at_u in Hdisj by lia.
      lazymatch type of Hrdr with rdn _ _ ?src _ = Some _ =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst ?R _ ?M _) _) _ =>
        edestruct (@ref_memcpy fx _ _ M (v_addi sp (-64)) src 8 rb rom
                     ltac:(constructor;
                            [ lia
                            | rewrite Hlenr; reflexivity
                            | rewrite Hlenr; exact (magree_rd _ _ _ 8%nat _ Hag (minv_lo64 _ _ HI) Hokr Hrdr)
                            | rewrite Hlenr; frame_ok
                            | unfold at_; rewrite ?u64_lit by alia; uaddr; cbn [Z.of_nat]; alia
                            | unfold at_; rewrite ?u64_lit by alia; alia
                            | uaddr; alia ])
                     R (zpc+ PC_ALLOC_META 0x7c))
          as (R2 & Hms & Hkp);
        [ rl_ret_ok
        | regnorm; reflexivity
        | regnorm; reflexivity
        | regnorm; reflexivity
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | ]
      end end.
      eapply rz_msteps_p; [ mpure Hp | exact Hms | ]. clear Hms.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ (wbytes ?M ?d ?bs) _) _) _ =>
        replace (wbytes M d bs) with (wbytes M (v_addi sp (-64)) (word_to_le_bytes 8 (le_val rb)))
          by (rewrite w2l_le_val by exact Hlenr; reflexivity)
      end.
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst _ _ (wbytes ?M ?a ?bs) _) _) _ =>
          apply (magree_wbytes_win _ M a bs) in Hag;
          [ | rewrite length_w2l; uaddr; alia
            | cbn [ms_lo ms_hi upd]; uaddr; alia
            | rewrite length_w2l; cbn [ms_lo ms_hi upd]; uaddr; alia ]
      end.
      keeps_facts Hkp. pc_lit. mnorm HS.
      mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x84).
      eapply (IH _ (v_addi i 16) (le_val rb));
        [ exact Hag | exact HI | win_pres | frame_rd | win_nn | keep_tac
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | exact HS ].
    + (* [comment removed for export] *)
      mstepx Hp HS Hag HI HW HK Hret am_calls.
      * (* [comment removed for export] *)
        cbv delta [Ks] beta in HS |- *. mnorm HS.
        mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xa4).
        use_cut_kx CUT Kx Hag HI HS.
      * mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x84).
        eapply (IH auxv (v_addi i 16) secret);
        [ exact Hag | exact HI | exact HJ | exact Hslot | exact HJn | keep_tac
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; reflexivity
        | exact HS ].
  - (* [comment removed for export] *)
    intros [] _ HS.
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xac).
    mach_passert HS.
    match goal with Hb : c_eq (le_val ?b) (Z_to_bv 64 4096) = true |- _ =>
      apply c_eq_eq in Hb; rename Hb into Hpg;
      match goal with Hr : rdn ml_segs _ _ 8 = Some b |- _ => rename Hr into Hpgrd end
    end.
    rewrite Hpg in HS |- *.
    replace (if c_ltu (Z_to_bv 64 4096) (Z_to_bv 64 4096) then Z_to_bv 64 4096 else Z_to_bv 64 4096)
      with (Z_to_bv 64 4096) in HS by reflexivity.
    replace (if c_ltu (Z_to_bv 64 4096) (Z_to_bv 64 4096) then Z_to_bv 64 4096 else Z_to_bv 64 4096)
      with (Z_to_bv 64 4096) by reflexivity.
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xb4).
    (* [comment removed for export] *)
    use_piece (am_res_piece MM MF MP) Hp Hag HI HW HS.
    intros res HX HS. mnorm HS.
    (* [comment removed for export] *)
    mrunx Hp HS Hag HI HW HK Hret am_calls.
Qed.
End AllocMeta.
