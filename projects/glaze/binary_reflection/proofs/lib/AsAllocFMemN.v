(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3Nf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3Nf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFMem.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsAtom HsAtom2.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac rd_layersN := (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_P3f, fr_e1e, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
                   repeat (wd_rdstep rd8_side).

Section P3NMEM.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id cnt24 k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis GpT : hideW (U p + n8 <= T \/ T + 4096 <= U p - 16).   (* [comment removed for export] *)
  Hypothesis Gba : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584.
  Hypothesis GbaT : hideW (ba + 8192 <= T \/ T + 4096 <= ba).   (* [comment removed for export] *)
  Hypothesis Gbap : hideW (ba + 8192 <= U p - 16 \/ U p + n8 <= ba).   (* [comment removed for export] *)
  Hypothesis Glast : 0x10007fff8000 <= last /\ last + 8192 <= U S - 3584.
  Hypothesis GlastT : hideW (last + 8192 <= T \/ T + 4096 <= last).   (* [comment removed for export] *)
  Hypothesis Glastp : hideW (last + 8192 <= U p - 16 \/ U p + n8 <= last).   (* [comment removed for export] *)
  Hypothesis Gbalast : hideW (last + 8192 <= ba \/ ba + 8192 <= last).   (* [comment removed for export] *)
  Lemma TSB_P3NMEM : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3NMEM : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation Me := (fr_P3e memD S p x22 T n n8 id cnt24 k ba qb bst bcs).
  #[local] Abbreviation Mf := (fr_P3f memD S p x22 T n n8 id cnt24 k ba qb last len bst bcs).

  Lemma shlen8N : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8N : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gn8 GT Gp GS T x22 S memD. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  #[local] Ltac sd_only_disj H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end.
  #[local] Ltac sd_lia_pick :=
    first [ solve [ ha_tiersR ltac:(ha_lia0) ]
          | solve [ repeat match goal with H : _ \/ _ |- _ => clear H end; lia ]
          | match goal with H : _ \/ _ |- _ => solve [ sd_only_disj H; lia ] end ].
  Ltac lsideN := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8N; rewrite ?Z2Nat.id by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end);
                 first [ solve [ wd_unorm1; wd_zofnat; sd_lia_pick ] | wd_ulia ].

  (* [comment removed for export] *)
  Lemma fr_P3e_outside : forall a : word,
    (U a < U S - 2272 \/ U S - 2128 <= U a) -> (U a < U p \/ U p + 8 <= U a) ->
    (U a < SB + U p / 8 \/ SB + U p / 8 + n8 / 8 <= U a) ->
    (U a < ba \/ ba + 32 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) ->
    (U a < T + 2128 \/ T + 2132 <= U a) -> (U a < T + 2784 \/ T + 2792 <= U a) -> Me a = memD a.
  Proof using Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros a A1 A2 A3 A4 A5 A6 A7. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_e1e, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideN. reflexivity.
  Qed.
  Lemma fr_P3e_foot : forall a : word, Me a <> memD a ->
    (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)
    \/ (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792).
  Proof using Glast Gba Gn8 GT Gp GS last. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros a NE.
    destruct (decide (U S - 2272 <= U a < U S - 2128)); [am_tauto|].
    destruct (decide (U p <= U a < U p + 8)); [am_tauto|].
    destruct (decide (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)); [am_tauto|].
    destruct (decide (ba <= U a < ba + 32)); [am_tauto|].
    destruct (decide (T + 80 <= U a < T + 112)); [am_tauto|].
    destruct (decide (T + 2128 <= U a < T + 2132)); [am_tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)); [(first [clear - a0 | idtac]; am_tauto)|].
    exfalso. apply NE. apply fr_P3e_outside; lia.
  Qed.
  Lemma fr_P3f_outside : forall a : word,
    (U a < U S - 2272 \/ U S - 2128 <= U a) -> (U a < U p \/ U p + 8 <= U a) ->
    (U a < SB + U p / 8 \/ SB + U p / 8 + n8 / 8 <= U a) ->
    (U a < ba \/ ba + 32 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) ->
    (U a < T + 2128 \/ T + 2132 <= U a) -> (U a < T + 2784 \/ T + 2792 <= U a) -> (U a < last \/ last + 8 <= U a) -> Mf a = memD a.
  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros a A1 A2 A3 A4 A5 A6 A7 A8. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideN. reflexivity.
  Qed.
  Lemma fr_P3f_foot : forall a : word, Mf a <> memD a ->
    (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)
    \/ (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792)
    \/ (last <= U a < last + 8).
  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros a NE.
    destruct (decide (U S - 2272 <= U a < U S - 2128)); [am_tauto|].
    destruct (decide (U p <= U a < U p + 8)); [am_tauto|].
    destruct (decide (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)); [am_tauto|].
    destruct (decide (ba <= U a < ba + 32)); [am_tauto|].
    destruct (decide (T + 80 <= U a < T + 112)); [am_tauto|].
    destruct (decide (T + 2128 <= U a < T + 2132)); [am_tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)); [(first [clear - a0 | idtac]; am_tauto)|].
    destruct (decide (last <= U a < last + 8)); [(first [clear - a0 | idtac]; am_tauto)|].
    exfalso. apply NE. apply fr_P3f_outside; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fr_P3f_first : forall a : word, T + 88 <= U a < T + 96 -> Mf a = memD a.
  Proof using GlastT Glast GbaT Gba GpT Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros a Ha. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold SB in *.
    unfold hideW in GpT, GbaT, GlastT.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideN. reflexivity.
  Qed.
  Lemma fr_P3e_grows : mem_grows memD Me.
  Proof using GT Gp. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_e1e, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma fr_P3f_grows : mem_grows memD Mf.
  Proof using GT Gp. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3e_b0 : rdn ASEGS Me (Z_to_bv 64 ba) 8 = Some (LE8 (Z_to_bv 64 0)).                 Proof using GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3e_b8 : rdn ASEGS Me (Z_to_bv 64 (ba + 8)) 8 = Some (LE8 (Z_to_bv 64 (n + 8192))).    Proof using GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3e_b16 : rdn ASEGS Me (Z_to_bv 64 (ba + 16)) 8 = Some (LE8 (Z_to_bv 64 1)).           Proof using GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3e_b24 : rdn ASEGS Me (Z_to_bv 64 (ba + 24)) 8 = Some (LE8 (at_ p (-16))).            Proof using GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3e_q80 : rdn ASEGS Me (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 1)).            Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3e_q88 : rdn ASEGS Me (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 ba)).           Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3e_q96 : rdn ASEGS Me (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 ba)).           Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3e_q104 : rdn ASEGS Me (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (qb + (n + 8192)))).  Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3f_b0 : rdn ASEGS Mf (Z_to_bv 64 ba) 8 = Some (LE8 (Z_to_bv 64 0)).                 Proof using Gbalast Glast GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - Gbalast Glast GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3f_b8 : rdn ASEGS Mf (Z_to_bv 64 (ba + 8)) 8 = Some (LE8 (Z_to_bv 64 (n + 8192))).    Proof using Gbalast Glast GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - Gbalast Glast GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3f_b16 : rdn ASEGS Mf (Z_to_bv 64 (ba + 16)) 8 = Some (LE8 (Z_to_bv 64 1)).           Proof using Gbalast Glast GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. first [clear - Gbalast Glast GbaT Gba GT GS | idtac]; (rd_layersN). Qed.
  Lemma fr_P3f_b24 : rdn ASEGS Mf (Z_to_bv 64 (ba + 24)) 8 = Some (LE8 (at_ p (-16))).            Proof using Gbalast Glast GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3f_q80 : rdn ASEGS Mf (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (len + 1))).    Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3f_q96 : rdn ASEGS Mf (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 ba)).           Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3f_q104 : rdn ASEGS Mf (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (qb + (n + 8192)))).  Proof using Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.
  Lemma fr_P3f_last : rdn ASEGS Mf (Z_to_bv 64 last) 8 = Some (LE8 (Z_to_bv 64 ba)).              Proof using GlastT Glast Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. rd_layersN. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3e_cnt : rdn ASEGS Me (Z_to_bv 64 (T + 2128)) 4 = Some (LE4 (cnt24 - 1)).
  Proof using GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_e1e in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    repeat (rewrite rdn_wbytes_out; [ | (first [clear - GT GS GbaT Gba | idtac]; rd8_side) | (first [clear - GT GS | idtac]; rd8_side) | (first [clear - GT GS Gba | idtac]; rd8_side) ]).
    pose proof (rdn_wbytes_hit ASEGS (LE4 (cnt24 - 1))) as Hh. rewrite length_N_to_le_bytes in Hh. apply Hh. unorm. lia.
  Qed.
  Lemma fr_P3f_cnt : rdn ASEGS Mf (Z_to_bv 64 (T + 2128)) 4 = Some (LE4 (cnt24 - 1)).
  Proof using GlastT Glast GbaT Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    pose proof (u64_range S). pose proof (u64_range p). unfold hideW in GbaT, GlastT, Gbalast. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    repeat (rewrite rdn_wbytes_out; [ | (first [clear - GT GS GlastT Glast GbaT Gba | idtac]; rd8_side) | (first [clear - GT GS | idtac]; rd8_side) | (first [clear - GT GS Glast Gba | idtac]; rd8_side) ]).
    pose proof (rdn_wbytes_hit ASEGS (LE4 (cnt24 - 1))) as Hh. rewrite length_N_to_le_bytes in Hh. apply Hh. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_P3e_shadow : forall i, 0 <= i < n8 / 8 -> Me (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd).
  Proof using Glast Gba Gn8 GT Gp GS last. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros i Hi. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_e1e, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideN.
    rewrite wbytes_inside by lsideN.
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    rewrite shlen8N. (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia.
  Qed.
  Lemma fr_P3f_shadow : forall i, 0 <= i < n8 / 8 -> Mf (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd).
  Proof using Glast Gba Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1.
    intros i Hi. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_e1f, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideN.
    rewrite wbytes_inside by lsideN.
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    rewrite shlen8N. (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia.
  Qed.
  Lemma fr_P3e_hdr16 : Me (at_ p (-16)) = memD (at_ p (-16)).
  Proof using Glast Gbap Gba GpT Gn8 GT Gp GS last. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold hideW in GpT, Gbap, Glastp. apply fr_P3e_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB, at_ in G in change_no_check G' end); wd_ulia. Qed.
  Lemma fr_P3f_hdr16 : Mf (at_ p (-16)) = memD (at_ p (-16)).
  Proof using Glastp Glast Gbap Gba GpT Gn8 GT Gp GS. pose proof TSB_P3NMEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3NMEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8N. unfold hideW in GpT, Gbap, Glastp. apply fr_P3f_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB, at_ in G in change_no_check G' end); wd_ulia. Qed.
End P3NMEM.
