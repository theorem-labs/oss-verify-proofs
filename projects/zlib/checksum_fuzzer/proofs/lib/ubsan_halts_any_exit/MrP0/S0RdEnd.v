(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require PropExec StoreOk Frame ShapeAlg ModelAmb StdModel S0ReadBase S0ReadStage S0World S0TargetPre.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Plain Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom MrRulesS0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MrP0 Require Import S0HeapPre S0HBase S0HConv S0Ivs S0TrTail S0RdLib S0RdInv S0HeaderMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section END_.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.
Variables (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

Abbreviation GPOST := (G_post stdin0 fs0 tid).
Let L : Z := Z.of_nat (length content).

Lemma rdn_of_C8 : forall (M : word -> option byte) A (v : word),
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M A [C8 v] -> OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 A) 8 = Some (word_to_le_bytes 8 v).
Proof.
  intros M A v H. pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M A (le8 v) 0 8 B ltac:(unfold le8; rewrite CatExec.length_N_to_le_bytes; lia)) as X.
  rewrite Z.add_0_r in X. cbn [skipn] in X. unfold le8 in X.
  rewrite firstn_all2 in X by (rewrite CatExec.length_N_to_le_bytes; lia). exact X.
Qed.

Lemma main_frame_of_cells : forall (M : word -> option byte) junk,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) (main_cells sp0 junk) -> S0World.main_frame sp0 M.
Proof.
  intros M junk H. unfold main_cells in H.
  repeat lazymatch type of H with
  | rw_cells _ _ ?A (?c :: ?rest) =>
      lazymatch rest with
      | [] => idtac
      | _ => let H1 := fresh "C" in
             apply (proj1 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M A [c] rest)) in H; destruct H as [H1 H];
             cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H
      end
  end.
  change (Z.of_nat 8) with 8 in *.
  constructor; unfold S0World.cell;
    lazymatch goal with |- OP.rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
      first [ replace a with (sp0 - 128 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption
            | replace a with (sp0 - 128 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) by lia; apply rdn_of_C8; assumption ]
    end.
Qed.

Lemma stack_writable_of_base : forall M, rd_base sp0 tid M -> S0TargetPre.stack_writableZ M sp0.
Proof.
  intros M [ST UP (junk & FRM) _ _ _ _ _]. destruct ST as (_ & _ & STW). destruct FRM as [_ FW]. cbn [cells_size csize main_cells Nat.add] in FW.
  assert (WIN : wr_at (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 6144513) 6144513).
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec (sp0 - 6144513 + i) (sp0 - 128)) as [A|A].
    - apply STW. lia.
    - destruct (Z_lt_le_dec (sp0 - 6144513 + i) (sp0 - 48)) as [B|B].
      + destruct FW as (_ & _ & FW). specialize (FW (sp0 - 6144513 + i - (sp0 - 128)) ltac:(lia)).
        replace (sp0 - 128 + (sp0 - 6144513 + i - (sp0 - 128))) with (sp0 - 6144513 + i) in FW by lia. exact FW.
      + destruct UP as (_ & _ & UW). specialize (UW (sp0 - 6144513 + i - (sp0 - 48)) ltac:(lia)).
        replace (sp0 - 48 + (sp0 - 6144513 + i - (sp0 - 48))) with (sp0 - 6144513 + i) in UW by lia. exact UW. }
  intros d m Hd Hm. exact (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 6144513) 6144513 d m WIN Hd Hm).
Qed.

Lemma rd_end_rz : forall (K : ShapeAlg.TSet) (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rd_inv sp0 tid content GPOST pb buf cap L M s mo ->
  65536 <= cap -> 6 + S0TargetPre.hdr_cfglen content <= L < 2 ^ 26 ->
  drv_state s -> room (2 ^ 27) mo ->
  (forall R' : bvmap 5 word, target_pre_h sp0 buf cap content R' M mo ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' (Z_to_bv 64 0x14020) M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) K) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                                 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 L) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x13e4c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) K.
Proof.
  intros until x31. intros RI HCAP HL HDRV HROOM HK.
  pose proof (rd_blk_range _ _ _ _ _ _ _ _ _ _ _ RI) as (BR1 & BR2 & BR3 & BR4).
  pose proof RI as [HH HOWN (bs & BLK & PRE) [LEN1 LEN2] BASE].
  pose proof HOWN as [(Ld & _ & HKL & _) [_ HG]]. unfold G_post in HG.
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  assert (CONT : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 buf) (length content) = Some content).
  { pose proof (rw_cells_bytes_at _ _ _ _ BLK) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    assert (LBS : length bs = Z.to_nat cap) by (destruct BLK as [[[W _] _] _]; exact W).
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M buf bs 0 (length content) B ltac:(unfold L in *; lia)) as X.
    rewrite Z.add_0_r in X. cbn [skipn] in X. unfold L in PRE. rewrite Nat2Z.id in PRE. rewrite PRE in X.
    rewrite firstn_all in X. exact X. }
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    destruct (header_ok_ms RR M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)) sp0 buf content) as (R' & HMS & G1 & G2 & G10 & G11 & G12 & G13 & G8 & G9 & G18 & G19 & G20 & G21 & GK) end.
  1: reflexivity. 1: reflexivity. 1: reflexivity. 1: exact SP0. 1: lia. 1: fold L; lia. 1: exact HL. 1: exact CONT.
  eapply rz_ours; [exact Hh | exact Hl | exact HMS |].
  apply HK.
  pose proof BASE as [ST UP (junk & FRM) ERR MI AUX IMG TIDC].
  assert (IMG' : pristine_in pristine_ivs M) by exact (pristine_in_sub M pristine_ivs rd_ivs eq_refl IMG).
  constructor; try assumption.
  - etransitivity; [apply GK; cbn [In]; left; reflexivity | reflexivity].
  - etransitivity; [apply GK; cbn [In]; right; left; reflexivity | reflexivity].
  - split; [exact SP0 | exact SP16].
  - split; [exact HL | fold L; lia].
  - exact (stack_writable_of_base M BASE).
  - exact (main_frame_of_cells M junk FRM).
  - exists (bv_unsigned tid). split; [lia|]. rewrite Z_to_bv_bv_unsigned. exact TIDC.
  - exists s, pb. split; [exact HH|]. split; [|split; [exact HDRV | exact HROOM]].
    eapply OWN_weaken; [exact HOWN|]. split; [rewrite HG; reflexivity | reflexivity].
  - rewrite HG. apply StdModel.std_model_mk.
Qed.
End END_.
