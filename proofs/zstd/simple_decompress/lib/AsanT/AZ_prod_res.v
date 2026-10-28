(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_frame_iface AZ_prod_iface AZ_kx AZ_prod.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
(* [comment removed for export] *)
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RESERVE.
  Hypothesis U32R : zd_u32r_stmtA.
  Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (RNG : footprint) (SP P D : Z) (pl : list Z) (size lo : Z).
  Hypothesis PR : prod_at m P D size.
  Hypothesis PL : payload_at m D pl.
  Hypothesis SZ : 0 <= size <= zlen pl.
  Hypothesis SZ31 : size < 2^31.
  Hypothesis P0 : 0 < P.  Hypothesis P8 : P mod 8 = 0.  Hypothesis D0 : 0 < D.  Hypothesis DE : D + zlen pl < 2^64.
  Hypothesis ST : stk bsegs m lo SP.
  Hypothesis LO : lo <= SP - 64.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis SP47 : SP < 2^47.
  Hypothesis PLO : P + 16 <= lo.
  Hypothesis DLO : D + zlen pl <= lo.
  Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
  Hypothesis ARP : areg RNG m P 16.
  Hypothesis ARD : aro RNG m D (zlen pl).
  Hypothesis ART : art m.
  Hypothesis AST : astk RNG lo SP.
  Hypothesis MI : mem_inv bsegs m.

  Notation W := [(P, P + 16); (SP - 64, SP)].
  Notation POST := (zd_reserve_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size lo m).

  (* [comment removed for export] *)
  Lemma le8_small_split : forall v, 0 <= v < 4294967296 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
  Proof.
    intros v Hv. rewrite <- store_bytes_8'. unfold le4.
    assert (E : bv_unsigned (Z_to_bv 64 v) = v) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    rewrite E. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
    assert (Z0 : forall k, 32 <= k -> v ≫ k = 0) by (intros k Hk; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; split; [lia|];
                                                      apply Z.lt_le_trans with (2^32); [change (2^32) with 4294967296; lia| apply Z.pow_le_mono_r; lia]).
    rewrite (Z0 (8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8 + 8)), (Z0 (8 + 8 + 8 + 8 + 8 + 8 + 8)) by lia.
    rewrite !Z.shiftr_0_l. reflexivity.
  Qed.

  Lemma reserve_body : evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_RESERVE) fc None m (seg_rom bsegs)).
  Proof.
    pose proof PR as PR0. unfold prod_at in PR0. pose proof PL as [PLB PLR].
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
    change (2^31) with 2147483648 in SZ31.
    destruct ART as (GOT & RIC & SHB & INI & LAY & REAL).
    destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
    destruct (ARP ltac:(lia)) as (ABP & UP & RP & RPS). destruct ARD as (UD & RD & RDS).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (ablk_lin _ _ ABP) as PLIN. unfold AIMG_HI in PLIN.
    assert (PA : P + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= P) by (unfold ablk, AIMG_HI, KLS in ABP; lia).
    assert (PR4 : rw_cells bsegs m P [C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_recell; [exact PR0 | cbn; tauto |]. cbn [cells_bytes cbytes]. rewrite (le8_small_split size) by lia. rewrite <- app_assoc. reflexivity. }
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    kx_autoFLAx [KAUnp P 16; KAApp P 16] [0xb02cc] 40%nat
      [KZRange P 4096 (2^47 - 16); KZAlign P 8; KZRange SP 0x10007fff8000 (2^47 - 1); KZWr (SP - 48) 48; KZDisj (SP - 48) 48 P 16]
      [(P, 16); (SP - 48, 48)] [(P, 16); (SP - 48, 48)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_acc RSTK. all: try kx_z.
    all: kx_mem.
    (* [comment removed for export] *)
    zstep. rewrite sx32w_small by lia. clear PR4.
    zstep. zstep. zstep.
    unp_now UP MU UP1. unp_now UD MU UD1.
    call (U32R RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -48) P D pl size 0 size lo).
    all: try eassumption. all: try reflexivity. all: try (clear - SZ SZ31 P0 D0 LO RSP SP47 PLO DLO DP KLO; lia).
    all: try (lazymatch goal with
              | |- payload_at _ _ _ => split; assumption
              | |- areg _ _ _ _ => intros _; split; [exact ABP|]; split; [assumption|]; split; assumption
              | |- aro _ _ _ _ => split; [assumption|]; split; assumption
              | |- art _ => split; [assumption|]; repeat (split; [assumption|]); assumption
              | |- astk _ _ _ => split; [unfold KHIGH; lia|]; split; [eapply rng_sub; [exact RSTK| lia| lia] | exact RI]
              end).
    pose proof (uint32Range_range pl size 0 size ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia) ltac:(change (2^32) with 4294967296; lia)) as UR.
    unfold zd_reserve_postA, reserve_data_prefix, producer_contract.
    destruct (uint32Range pl size 0 size) as [slice size1]. cbn [fst snd] in *. destruct UR as [RSL RS1].
    unfold prod_at in POST.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    unp_now UP MU UP2.
    (* [comment removed for export] *)
    replace ((P + 8) mod 18446744073709551616 / 8 + 2147450880) with (2147450880 + (P + 8) / 8) by (rewrite Z.mod_small by lia; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ ?Q _ => remember Q as KQ eqn:EKQ end.
    all: kx_autoFLAx [KAUnp P 16; KAApp P 16; KAApp (SP - 48) 48; KAShp (2147450880 + P / 8) P; KAShp (2147450880 + (P + 8) / 8) (P + 8)] [] 60%nat
      [KZRange P 4096 (2^47 - 16); KZAlign P 8; KZRange SP 0x10007fff8000 (2^47 - 1); KZRange slice 0 (2^31); KZRange size1 0 (2^31);
       KZRange D 1 (2^47); KZRange (D + zlen pl) 1 (2^47);
       KZWr P 16; KZWr (SP - 48) 48; KZDisj (SP - 48) 48 P 16]
      [(P, 16); (SP - 48, 48)] [(P, 16); (SP - 48, 48)].
    all: try kx_cell_lit. all: try kx_acc RI. all: try kx_acc RSTK. all: try kx_z.
    all: kx_mem.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mf (SP + -48) _, STc : stk _ ?mf lo (SP + -48) |- _ => release_frame FRc STc SP end.
    all: subst KQ.
    all: first
      [ (* [comment removed for export] *)
        replace (slice `min` size1) with slice by lia;
        replace (-1 * slice + size1) with (size1 - slice) by lia; replace (-1 * slice + (size1 + D)) with (D + (size1 - slice)) in POST by lia;
        apply evtF_done; do 14 eexists; eexists; split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact PC|]; unfold prod_at; exact POST
      | (* [comment removed for export] *)
        replace (slice `min` size1) with size1 by lia; replace (size1 - size1) with 0 by lia;
        apply evtF_done; do 14 eexists; eexists; split; [reflexivity|];
        split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact PC|]; unfold prod_at; rewrite Z.add_0_r; exact POST ].
  Qed.
End RESERVE.

Theorem zd_reserve_proofA : zd_u32r_stmtA -> zd_reserve_stmtA.
Proof.
  intros U32R. unfold zd_reserve_stmtA. intros until lo.
  intros PR PL SZ SZ31 P0 P8 D0 DE ST LO RSP PLO DLO DP ARP ARD ART AST SP47 MI ->.
  eapply reserve_body; eassumption.
Qed.
End CANSEC1.
