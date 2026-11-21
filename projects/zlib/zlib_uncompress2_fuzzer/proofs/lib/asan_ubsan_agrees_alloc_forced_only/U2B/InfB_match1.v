(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import InfBGlue_p04.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32).

  Definition ml_post (r1 r2 r3 r4 r7 r8 r9 r15 r18 r19 r20 r21 r22 r23 r24 r26 r27 r28 r29 r30 r31 : word) (osz cout c : Z) (me : amem) : machine_state -> Prop :=
    fun ms' => exists (fo' : Z -> Z) (m' : amem) (y5 y6 y11 y12 y13 y14 y16 y17 : word),
      ms' = MS (mkR r1 r2 r3 r4 y5 y6 r7 r8 r9 (Z_to_bv 64 (6341696 + cout + c)) y11 y12 y13 y14 r15 y16 y17
                    r18 r19 r20 (Z_to_bv 64 2147450880) r22 r23 r24 r21 r26 r27 r28 r29 r30 r31)
               FR (Z_to_bv 64 0x92544) fc None m' (seg_rom bsegs)
      /\ munch [(6341696, 6341696 + osz)] me m' /\ wmono bsegs me m' /\ mem_inv bsegs m'
      /\ f8arr bsegs m' 6341696 (Z.to_nat osz) fo' /\ (forall i, 0 <= fo' i < 256).
  Lemma m_loop_o : forall (N : nat) (r1 r2 r3 r4 r7 r8 r9 r15 r18 r19 r20 r21 r22 r23 r24 r26 r27 r28 r29 r30 r31 x5 x6 x10 x17 : word)
      (me mc : amem) (osz cout fi c k : Z) (fo : Z -> Z),
    munch [(6341696, 6341696 + osz)] me mc -> wmono bsegs me mc -> mem_inv bsegs mc ->
    f8arr bsegs mc 6341696 (Z.to_nat osz) fo ->
    shadow_bytes me 2148243592 (2148243592 + 32768) (fun _ => 0) ->
    rng RNG 6341696 262144 -> rng RNG 2148243592 32768 ->
    1 <= osz <= 262144 -> 0 <= cout -> 0 <= fi <= cout -> cout + c <= osz -> c < 2147483648 ->
    0 <= k < c -> c - k < Z.of_nat N ->
    evtF bsegs RNG (ml_post r1 r2 r3 r4 r7 r8 r9 r15 r18 r19 r20 r21 r22 r23 r24 r26 r27 r28 r29 r30 r31 osz cout c me)
      (MS (mkR r1 r2 r3 r4 x5 x6 r7 r8 r9 x10 (Z_to_bv 64 (6341696 + cout + k)) (Z_to_bv 64 (6341696 + fi + k)) (Z_to_bv 64 (c - k)) (Z_to_bv 64 (6341696 + fi + k)) r15
               (Z_to_bv 64 (6341696 + cout + k)) x17
               r18 r19 r20 (Z_to_bv 64 2147450880) r22 r23 r24 r21 r26 r27 r28 r29 r30 r31)
          FR (Z_to_bv 64 0x924c8) fc None mc (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until fo; intros MU WM MI OUT SHO ROB ROBS OSZ COUT0 HFI HCO HC31 HK HN; [lia|].
    assert (DJO : disjoint_from [(6341696, 6341696 + osz)] 2148243592 (2148243592 + 32768 - 2148243592)) by (cbn [disjoint_from]; lia).
    pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOk.
    pose proof (tab_sh0 mc 6341696 32768 (6341696 + fi + k) SHOk eq_refl ltac:(lia) ltac:(lia)) as RSH1.
    pose proof (tab_sh_acc RNG 6341696 32768 (6341696 + fi + k) ROBS eq_refl ltac:(lia) ltac:(lia)) as ASH1.
    pose proof (tab_sh0 mc 6341696 32768 (6341696 + cout + k) SHOk eq_refl ltac:(lia) ltac:(lia)) as RSH2.
    pose proof (tab_sh_acc RNG 6341696 32768 (6341696 + cout + k) ROBS eq_refl ltac:(lia) ltac:(lia)) as ASH2.
    assert (RDS : ov_read_bytes bsegs mc (Z_to_bv 64 (6341696 + fi + k)) 1 = Some [Z_to_bv 8 (fo (fi + k))])
      by (eapply (f8arr_read bsegs mc 6341696 (Z.to_nat osz) fo (fi + k)); [exact OUT| lia| unfold wa; f_equal; lia]).
    assert (ADS : acc_in RNG (Z_to_bv 64 (6341696 + fi + k), 1%nat))
      by (apply (rng_acc_litZ RNG 6341696 262144 _ 1%nat 1 ROB eq_refl); lia).
    zrung [0x92514].
    replace (6341696 + cout + k) with (6341696 + (cout + k)) by lia.
    assert (SOK : store_ok bsegs mc (Z_to_bv 64 (6341696 + (cout + k))) 1 = true)
      by (eapply (f8arr_store_ok bsegs mc 6341696 (Z.to_nat osz) fo (cout + k)); [exact OUT| lia| reflexivity]).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      destruct (out_write bsegs mc 6341696 (Z.to_nat osz) fo (cout + k) bs OUT ltac:(lia) (length_le1 _)) as (fo' & OUT' & FOR') end.
    store_done.
    zrung [0x92524].
    zs. zbr0 KL.
    -
      replace (6341696 + fi + k + 1) with (6341696 + fi + (k + 1)) by lia.
      replace (6341696 + (cout + k) + 1) with (6341696 + cout + (k + 1)) by lia.
      replace (c - k + -1) with (c - (k + 1)) by lia.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me _ osz cout fi c (k + 1) fo');
        [exact MU| exact WM| eassumption| exact OUT'| exact SHO| exact ROB| exact ROBS| exact OSZ| exact COUT0| exact HFI| exact HCO| exact HC31| lia| lia].
    -
      zs.
      replace (6341696 + (cout + k) + 1) with (6341696 + cout + c) by lia.
      apply evtF_done. unfold ml_post. eexists fo', _, _, _, _, _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact OUT'| exact FOR'].
  Qed.

  Lemma m_loop_w : forall (N : nat) (r1 r2 r3 r4 r7 r8 r9 r15 r18 r19 r20 r21 r22 r23 r24 r26 r27 r28 r29 r30 r31 x5 x6 x10 x17 : word)
      (me mc : amem) (osz cout Wd wi c k : Z) (fo fw : Z -> Z),
    munch [(6341696, 6341696 + osz)] me mc -> wmono bsegs me mc -> mem_inv bsegs mc ->
    f8arr bsegs mc 6341696 (Z.to_nat osz) fo ->
    shadow_bytes me 2148243592 (2148243592 + 32768) (fun _ => 0) ->
    rng RNG 6341696 262144 -> rng RNG 2148243592 32768 ->
    f8arr bsegs me Wd (Z.to_nat 32768) fw ->
    shadow_bytes me (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0) ->
    rng RNG Wd 32768 -> rng RNG (Z.shiftr Wd 3 + 2147450880) 4096 -> Wd mod 8 = 0 -> 6675392 <= Wd -> Wd + 32768 <= 140737488355328 ->
    1 <= osz <= 262144 -> 0 <= cout -> 0 <= wi -> wi + c <= 32768 -> cout + c <= osz -> c < 2147483648 ->
    0 <= k < c -> c - k < Z.of_nat N ->
    evtF bsegs RNG (ml_post r1 r2 r3 r4 r7 r8 r9 r15 r18 r19 r20 r21 r22 r23 r24 r26 r27 r28 r29 r30 r31 osz cout c me)
      (MS (mkR r1 r2 r3 r4 x5 x6 r7 r8 r9 x10 (Z_to_bv 64 (6341696 + cout + k)) (Z_to_bv 64 (Wd + wi + k)) (Z_to_bv 64 (c - k)) (Z_to_bv 64 (Wd + wi + k)) r15
               (Z_to_bv 64 (6341696 + cout + k)) x17
               r18 r19 r20 (Z_to_bv 64 2147450880) r22 r23 r24 r21 r26 r27 r28 r29 r30 r31)
          FR (Z_to_bv 64 0x924c8) fc None mc (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until fw; intros MU WM MI OUT SHO ROB ROBS FW SHW RW RWS W8 WLO WHI OSZ COUT0 HWI0 HWI1 HCO HC31 HK HN; [lia|].
    assert (DJO : disjoint_from [(6341696, 6341696 + osz)] 2148243592 (2148243592 + 32768 - 2148243592)) by (cbn [disjoint_from]; lia).
    assert (DJW : disjoint_from [(6341696, 6341696 + osz)] (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096 - (Z.shiftr Wd 3 + 2147450880)))
      by (cbn [disjoint_from]; pose proof (Z.shiftr_nonneg Wd 3); lia).
    assert (DJF : disjoint_from [(6341696, 6341696 + osz)] Wd (Z.of_nat (Z.to_nat 32768))) by (cbn [disjoint_from]; lia).
    pose proof (sh0_mu _ _ _ _ _ SHO MU DJO) as SHOk.
    pose proof (sh0_mu _ _ _ _ _ SHW MU DJW) as SHWk.
    assert (FWk : f8arr bsegs mc Wd (Z.to_nat 32768) fw).
    { unfold f8arr in *. eapply u8arr_transport; [exact FW| exact MU| exact WM|]. rewrite map_length, seq_length. exact DJF. }
    pose proof (tab_sh0 mc Wd 4096 (Wd + wi + k) SHWk W8 ltac:(lia) ltac:(lia)) as RSH1.
    pose proof (tab_sh_acc RNG Wd 4096 (Wd + wi + k) RWS W8 ltac:(lia) ltac:(lia)) as ASH1.
    pose proof (tab_sh0 mc 6341696 32768 (6341696 + cout + k) SHOk eq_refl ltac:(lia) ltac:(lia)) as RSH2.
    pose proof (tab_sh_acc RNG 6341696 32768 (6341696 + cout + k) ROBS eq_refl ltac:(lia) ltac:(lia)) as ASH2.
    assert (RDS : ov_read_bytes bsegs mc (Z_to_bv 64 (Wd + wi + k)) 1 = Some [Z_to_bv 8 (fw (wi + k))])
      by (eapply (f8arr_read bsegs mc Wd (Z.to_nat 32768) fw (wi + k)); [exact FWk| lia| unfold wa; f_equal; lia]).
    assert (ADS : acc_in RNG (Z_to_bv 64 (Wd + wi + k), 1%nat))
      by (apply (rng_acc_litZ RNG Wd 32768 _ 1%nat 1 RW eq_refl); lia).
    clear FWk SHWk.
    zrung [0x92514].
    replace (6341696 + cout + k) with (6341696 + (cout + k)) by lia.
    assert (SOK : store_ok bsegs mc (Z_to_bv 64 (6341696 + (cout + k))) 1 = true)
      by (eapply (f8arr_store_ok bsegs mc 6341696 (Z.to_nat osz) fo (cout + k)); [exact OUT| lia| reflexivity]).
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      destruct (out_write bsegs mc 6341696 (Z.to_nat osz) fo (cout + k) bs OUT ltac:(lia) (length_le1 _)) as (fo' & OUT' & FOR') end.
    store_done.
    zrung [0x92524].
    zs. zbr0 KL.
    -
      replace (Wd + wi + k + 1) with (Wd + wi + (k + 1)) by lia.
      replace (6341696 + (cout + k) + 1) with (6341696 + cout + (k + 1)) by lia.
      replace (c - k + -1) with (c - (k + 1)) by lia.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me _ osz cout Wd wi c (k + 1) fo' fw);
        [exact MU| exact WM| eassumption| exact OUT'| exact SHO| exact ROB| exact ROBS| exact FW| exact SHW| exact RW| exact RWS| exact W8| exact WLO| exact WHI
        | exact OSZ| exact COUT0| exact HWI0| exact HWI1| exact HCO| exact HC31| lia| lia].
    -
      zs.
      replace (6341696 + (cout + k) + 1) with (6341696 + cout + c) by lia.
      apply evtF_done. unfold ml_post. eexists fo', _, _, _, _, _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact OUT'| exact FOR'].
  Qed.
End S.
End CANSEC1.
