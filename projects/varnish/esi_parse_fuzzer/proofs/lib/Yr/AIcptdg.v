(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcppc0 AIcp2qw.

Module AIcp8qs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcppc0 AIcp2qw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.
Ltac br K := brf K; try (exfalso; lia).

Definition PCM_ENTRY : Z := 0x4a388.
Definition PCM_TOP : Z := 0x4a49c.      (* [comment removed for export] *)
Definition PCM_NEXT : Z := 0x4a494.     (* [comment removed for export] *)
Definition PCM_EXIT : Z := 0x4ac74.     (* [comment removed for export] *)
Definition PCM_STACK : Z := 2320.       (* [comment removed for export] *)
Definition PAT : Z := 0xaaaaaaaaaaaaaaaa.   (* [comment removed for export] *)
Definition FLAGCHARS : Z := 0x154f6.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition S_FLAGS : list byte := [Z_to_bv 8 39; Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 35; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Definition S_LENMOD : list byte := [Z_to_bv 8 106; Z_to_bv 8 122; Z_to_bv 8 116; Z_to_bv 8 76; Z_to_bv 8 113; Z_to_bv 8 0].        (* [comment removed for export] *)
Definition S_cCsS : list byte := [Z_to_bv 8 99; Z_to_bv 8 67; Z_to_bv 8 115; Z_to_bv 8 83; Z_to_bv 8 0].                            (* [comment removed for export] *)
Definition S_CS : list byte := [Z_to_bv 8 67; Z_to_bv 8 83; Z_to_bv 8 0].                                                          (* [comment removed for export] *)
Definition S_csB : list byte := [Z_to_bv 8 99; Z_to_bv 8 115; Z_to_bv 8 91; Z_to_bv 8 0].                                           (* [comment removed for export] *)
Definition S_sS : list byte := [Z_to_bv 8 115; Z_to_bv 8 83; Z_to_bv 8 0].                                                         (* [comment removed for export] *)
Definition S_FLOAT : list byte := [Z_to_bv 8 97; Z_to_bv 8 65; Z_to_bv 8 101; Z_to_bv 8 69; Z_to_bv 8 102; Z_to_bv 8 70; Z_to_bv 8 103; Z_to_bv 8 71; Z_to_bv 8 0]. (* [comment removed for export] *)

Lemma S_FLAGS_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x154f6 S_FLAGS.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x154f6 S_FLAGS MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_LENMOD_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1b922 S_LENMOD.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x1b922 S_LENMOD MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_cCsS_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x14277 S_cCsS.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x14277 S_cCsS MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_CS_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x19fbd S_CS.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x19fbd S_CS MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_csB_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x107e6 S_csB.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x107e6 S_csB MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_sS_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x13b79 S_sS.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x13b79 S_sS MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.
Lemma S_FLOAT_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x165ac S_FLOAT.
Proof. intros m MI. exact (proj2 (ro_cells_image rsegs m 0x165ac S_FLOAT MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).

  Definition pcm_saved : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition pcm_at (pc : Z) (off k : Z) : machine_state -> Prop :=
    fun ms => exists (rax x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
                     (vq cq : word) (jm jd j8 : list byte) (m : word -> option byte),
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 10) (Z_to_bv 64 (A + off)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * k)) x22 (Z_to_bv 64 9)
                   (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m
      /\ stk rsegs m lo (bv_unsigned sp + -2240)
      /\ rw_cells rsegs m (bv_unsigned sp + -104) pcm_saved
      /\ rw_cells rsegs m (bv_unsigned sp + -2176) [CB 2072 jm]
      /\ rw_cells rsegs m (bv_unsigned sp + -2216) [CB 40 jd]
      /\ rw_cells rsegs m (bv_unsigned sp + -2240) [CB 8 j8; C8 vq; C8 cq]
      /\ bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0])
      /\ bytes_at rsegs m VA (u64s slots).
End TOP.

Ltac unpack_pcm H :=
  destruct H as (rax & x5 & x6 & x7 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x22 & x28 & x29 & x30 & x31
                 & vq & cq & jm & jd & j8 & mq & -> & MU & WM & MI & ST & FRT & FRM & DIR & FRL & FB & VAA);
  unfold pcm_saved in FRT.
(* [comment removed for export] *)
Ltac pack_pcm :=
  unfold pcm_at, pcm_saved, PCM_TOP, PCM_NEXT, PCM_EXIT, PCM_STACK, FLAGCHARS, PAT;
  hot_eexists_all;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
  [ | eassumption | eassumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption ].

Definition pcm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pcm_exit : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc
    (lo A : Z) fbytes VA slots (m0 : word -> option byte) off k ms,
  pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0 PCM_EXIT off k ms ->
  (lo + PCM_STACK <= bv_unsigned sp)%Z ->
  evt rsegs (pcm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0) ms.
Proof.
  intros until ms. intros TOP LOLE. unpack_pcm TOP. unfold PCM_STACK, PCM_EXIT in *.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  do 15 zs.
  (* [comment removed for export] *)
  lazymatch type of FRL with rw_cells _ ?mq _ ?c0 => lazymatch type of DIR with rw_cells _ _ _ ?c1 => lazymatch type of FRM with rw_cells _ _ _ ?c2 =>
  lazymatch type of FRT with rw_cells _ _ _ ?c3 =>
    assert (FR : rw_cells rsegs mq (bv_unsigned sp + -2240) (c0 ++ c1 ++ c2 ++ c3));
    [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FRL|]; cbn [cells_size csize Nat.add];
      apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact DIR| lia]|]; cbn [cells_size csize Nat.add];
      apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact FRM| lia]|]; cbn [cells_size csize Nat.add];
      eapply rwc_eq; [exact FRT| lia]
    | clear FRL DIR FRM FRT; cbn [app] in FR ] end end end end.
  release_frame FR ST (bv_unsigned sp).
  zs.
  first [ apply evt_done | idtac ]. unfold pcm_post, PCM_STACK. hot_eexists_all.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ENTRY.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m : word -> option byte).
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length fbytes)).
  (* [comment removed for export] *)
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) fbytes.
  Hypothesis FNE : fbytes <> [].
  Hypothesis L63 : (Z.of_nat (length fbytes) <= 62)%Z.
  Hypothesis LOLE : (lo + PCM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
  Hypothesis FLO : (A + L + 1 <= lo)%Z.       (* [comment removed for export] *)
  Hypothesis K : forall ms1, pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m PCM_TOP 0 0 ms1 -> evt rsegs Q ms1.

  Section PHASE.
    Variables (m1 : word -> option byte) (jm jd jl : list byte).
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis MU1 : munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2240).
    Hypothesis FRT : rw_cells rsegs m1 (bv_unsigned sp + -104) (pcm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
    Hypothesis FRM : rw_cells rsegs m1 (bv_unsigned sp + -2176) [CB 2072 jm].
    Hypothesis DIR : rw_cells rsegs m1 (bv_unsigned sp + -2216) [CB 40 jd].
    Hypothesis FRL : rw_cells rsegs m1 (bv_unsigned sp + -2240) [CB 24 jl].
    Hypothesis FB1 : bytes_at rsegs m1 A (fbytes ++ [Z_to_bv 8 0]).
    Hypothesis VA1 : bytes_at rsegs m1 VA (u64s slots).
    (* [comment removed for export] *)
    Notation AT pc x10 x11 x12 x13 x14 :=
      (MS (mkR (Z_to_bv 64 0x4a3e4) (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp _ _ _ sp s1 x10 x11 x12 x13 x14 _ _ _
               (Z_to_bv 64 (L + 1)) (Z_to_bv 64 A) s4 (Z_to_bv 64 VA) s6 _ (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 _ _ _ _)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

    #[using="VA1 FB1 FRL DIR FRM FRT ST1 WM1 MU1 MI1 jl jd jm K FLO VLO LOLE L63 FNE NONUL m slots lo s8 s7 s5 s3 s2 s0 ra Clg"] Lemma pcm_after_check : forall x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x4a3e4) (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (L + 1)) (Z_to_bv 64 A) s4 (Z_to_bv 64 VA) s6 x23 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31)
                      F (Z_to_bv 64 0x4a430) fc None m1 (seg_rom rsegs)).
    Proof.
      intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
      (* [comment removed for export] *)
      pose proof MU1 as MU; unfold PCM_STACK in MU. pose proof WM1 as WM. pose proof MI1 as MIq.
      pose proof LOLE as LOLE'; unfold PCM_STACK in LOLE'.
      pose proof ST1 as ST'. pose proof FRT as FRT'; unfold pcm_saved in FRT'. pose proof FRM as FRM'. pose proof DIR as DIR'. pose proof FRL as FRL'.
      pose proof FB1 as FB'. pose proof VA1 as VA'.
      clear MU1 WM1 MI1 ST1 FRT FRM DIR FRL FB1 VA1 || idtac.
      pose proof (bytes_at_bound _ _ _ _ FB') as AB. rewrite length_app in AB. cbn [length] in AB.
      assert (LO0 : (0 <= lo)%Z) by (destruct ST' as [? _]; assumption).
      (* [comment removed for export] *)
      assert (HB0 : exists b0 ft, fbytes = b0 :: ft) by (destruct fbytes as [|b0 ft]; [congruence| exists b0, ft; reflexivity]).
      destruct HB0 as (b0 & ft & Efb).
      assert (Hb0 : nth_error (fbytes ++ [Z_to_bv 8 0]) 0 = Some b0) by (rewrite Efb; reflexivity).
      assert (B0NZ : bv_unsigned b0 <> 0%Z).
      { intros E. apply NONUL. rewrite Efb. left. apply bv_eq. rewrite E. reflexivity. }
      pose proof (bv_unsigned_in_range _ b0) as B0R.
      zs. zs. replace (bv_unsigned sp - 4096)%Z with (bv_unsigned sp + -4096)%Z by lia. zs. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        pose proof (u8ro_read rsegs mq A _ 0 b0 (Z_to_bv 64 A) FB' Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0 end.
      zs. cbv beta. zs. brf K0. { exfalso. lia. }
      do 15 zs. replace (bv_unsigned sp - 4096)%Z with (bv_unsigned sp + -4096)%Z by lia. zs. zs.
      apply K. pack_pcm. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity.
    Qed.

    Section Slow.
      Variables (ng : nat) (lastb : Z) (sf sl : Z).
      Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
      Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
      Hypothesis SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z.

      #[using="ng VA1 FB1 FRL DIR FRM FRT ST1 WM1 MU1 MI1 jl jd jm K FLO VLO LOLE L63 FNE NONUL m slots lo s8 s7 s5 s3 s2 s0 ra Clg"] Lemma pcm_slow_end : forall x5 x6 x7 x10 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
        evt rsegs Q (MS (mkR (Z_to_bv 64 0x4a3e4) (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 x10 (Z_to_bv 64 sl) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                          (Z_to_bv 64 (L + 1)) (Z_to_bv 64 A) s4 (Z_to_bv 64 VA) s6 x23 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x4ad5c) fc None m1 (seg_rom rsegs)).
      Proof.
        intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        zs. zs. brf Kb; try (deadK Kb).
        apply pcm_after_check.
      Qed.

      #[using="SFB ESL ESF SH1 lastb VA1 FB1 FRL DIR FRM FRT ST1 WM1 MU1 MI1 jl jd jm K FLO VLO LOLE L63 FNE NONUL m slots lo s8 s7 s5 s3 s2 s0 ra Clg"] Lemma pcm_slow_loop : forall (cc : nat) (j : Z) x5 x6 x7 x10 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
        Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x10 = Z_to_bv 64 (sf + j) ->
        evt rsegs Q (MS (mkR (Z_to_bv 64 0x4a3e4) (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp s1 x10 (Z_to_bv 64 sl) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                          (Z_to_bv 64 (L + 1)) (Z_to_bv 64 A) s4 (Z_to_bv 64 VA) s6 x23 (Z_to_bv 64 (bv_unsigned sp + -2184)) s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x4ad4c) fc None m1 (seg_rom rsegs)).
      Proof.
        induction cc as [|cc IH]; intros j x5 x6 x7 x10 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 Hc Hj ->; [lia|].
        pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
        rewrite length_app, zeros_length in SB. cbn [length] in SB.
        pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
        specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                               replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                       ltac:(lia) ltac:(unfold wa; f_equal; lia)).
        zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zs. zs.
        zs. brf Kb.
        - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
        - apply pcm_slow_end.
      Qed.
    End Slow.
  End PHASE.

  #[using="K FLO VLO CEIL LOLE L63 FNE NONUL Clg"] Lemma pcm_entry : forall t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0]) ->
    bytes_at rsegs m VA (u64s slots) ->
    map_cells m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    range_ok m A (L + 1) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 A) (Z_to_bv 64 VA) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PCM_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    intros until t6. intros FB VAA MC MI ST RNG. unfold PCM_ENTRY, PCM_STACK in *.
    pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB. rewrite length_app in AB. cbn [length] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof MC as MC'. open_map_cells MC'.
    (* [comment removed for export] *)
    destruct RNG as (IR & (ng & lastb & NG & SH & LBl) & QW1 & QW2).
    assert (AF : (0 <= A /\ A + (L + 1) + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
    destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
    destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
    assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (A + (L + 1) - 1) - sha (A + (L + 1) - 1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
    assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
    { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    (* [comment removed for export] *)
    freeze FB; freeze VAA; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SH; freeze QB1; freeze QB2.
    pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 104%nat ST. carve_frame 2072%nat ST. carve_frame 40%nat ST. carve_frame 24%nat ST.
    do 15 zs.
    thaw FB MUp WM; thaw VAA MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM;
    thaw Ghe MUp WM; thaw Che MUp WM; thaw SH MUp WM; thaw QB1 MUp WM; thaw QB2 MUp WM. clear MUp.
    do 7 zs.
    (* [comment removed for export] *)
    zs. call_lit istrlen_spec by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; exact FB
      | |- ~ In _ _ => exact NONUL
      | |- _ => eassumption
      end).
    zs. zs. rewrite zb_lxor_ones by lia.
    zs. brf K1. { exfalso. lia. }
    zs. zs. brf K2. { exfalso. lia. }
    (* [comment removed for export] *)
    assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    assert (HS2 : (0 <= Z.shiftr (L + A) 3 <= L + A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    do 10 zs.
    replace (A + (L + 1) - 1)%Z with (L + A)%Z in QB2 by lia.
    pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
    pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
    zs. zs. zs.
    zs. brf K7.
    - (* [comment removed for export] *)
      subst sbs.
      assert (LBR : (0 <= lastb < 128)%Z) by lia.
      pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                    (Z_to_bv 64 (2147450880 + Z.shiftr (L + A) 3)) SH) as RD.
      specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                     ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
      zs. rewrite sxb_small by lia.
      zs. zs. zs. zs. zs.
      rewrite (poisoned_last_zero (L + A) lastb) by
        (first [lia | destruct LBl as [LB0|LB1]; [left; exact LB0| right; replace (A + (L + 1) - 1)%Z with (L + A)%Z in LB1 by lia; lia]]).
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
      set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (L + A) / 8)%Z).
      assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
      assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
      assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
      { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
      clearbody sf sl.
      zs. brf K8.
      + eapply pcm_slow_end; try eassumption.
      + eapply pcm_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
    - subst sbs. eapply pcm_after_check; try eassumption.
  Qed.
End ENTRY.
End AIcp8qs.


Module AIcpa7e.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcppc0 AIcp2qw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.

Definition PCM_DIR : Z := 0x4a4e0.      (* [comment removed for export] *)
Definition PCM_SCAN : Z := 0x4a4c8.     (* [comment removed for export] *)
Definition m1w : word := Z_to_bv 64 4294967295.
(* [comment removed for export] *)
Definition dir_fresh : list cell :=
  [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 m1w; C4 m1w; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (zeros 3)].
(* [comment removed for export] *)
Definition dir_raw : list cell := [CB 8 (zeros 8); C8 (Z_to_bv 64 (-1)); CB 24 (zeros 24)].

Lemma le8_m1 : le8 (Z_to_bv 64 (-1)) = repeat (Z_to_bv 8 255) 8.
Proof.
  unfold le8, word_to_le_bytes. cbn -[Z_to_bv bv_unsigned Z.shiftr]. rewrite Z_to_bv_unsigned.
  repeat (refine (f_equal2 cons _ _); [apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|]). reflexivity.
Qed.
Lemma le4_m1w : le4 m1w = repeat (Z_to_bv 8 255) 4.
Proof.
  unfold le4, m1w. rewrite Z_to_bv_unsigned. cbn -[Z_to_bv bv_unsigned Z.shiftr].
  repeat (refine (f_equal2 cons _ _); [apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|]). reflexivity.
Qed.
Lemma le8_z0 : le8 (Z_to_bv 64 0) = zeros 8.
Proof. unfold le8, word_to_le_bytes. cbn -[Z_to_bv bv_unsigned Z.shiftr]. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_z0 : le4 (Z_to_bv 64 0) = zeros 4.
Proof. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma dir_fresh_wf : cells_wf dir_fresh. Proof. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma dir_fresh_bytes : cells_bytes dir_fresh = cells_bytes dir_raw.
Proof. unfold dir_fresh, dir_raw. cbn [cells_bytes cbytes]. rewrite !le4_z0, !le4_m1w, !le8_z0, le8_m1. reflexivity. Qed.
Lemma dir_raw_fresh : forall segs m a, rw_cells segs m a dir_raw -> rw_cells segs m a dir_fresh.
Proof. intros. eapply rw_cells_recast; [exact H| apply dir_fresh_wf| apply dir_fresh_bytes]. Qed.

Lemma rw_cells_to_CB : forall segs (m : word -> option byte) a cs, rw_cells segs m a cs -> rw_cells segs m a [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros segs m a cs H. pose proof H as [[W _] _]. eapply rw_cells_recast; [exact H| | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
  cbn. split; [| exact I]. apply cells_bytes_length. exact W.
Qed.

(* [comment removed for export] *)
Lemma fmt_read : forall m A fbytes (i : nat) b a,
  bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0]) -> nth_error (fbytes ++ [Z_to_bv 8 0]) i = Some b -> a = Z_to_bv 64 (A + Z.of_nat i) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m A fbytes i b a FB Hb ->. pose proof (bytes_at_bound _ _ _ _ FB) as AB.
  assert (IL2 : (i < length (fbytes ++ [Z_to_bv 8 0]))%nat).
  { destruct (Nat.lt_ge_cases i (length (fbytes ++ [Z_to_bv 8 0]))) as [L|G]; [exact L|]. rewrite (proj2 (nth_error_None _ i) G) in Hb. discriminate. }
  exact (u8ro_read rsegs m A _ (Z.of_nat i) b (Z_to_bv 64 (A + Z.of_nat i)) FB ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) ltac:(unfold wa; f_equal; lia)).
Qed.

Section DIRINV.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).

  (* [comment removed for export] *)
  Definition pcm_dir (off k : Z) : machine_state -> Prop :=
    fun ms => exists (rax x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
                     (vq cq : word) (jm j8 : list byte) (m : word -> option byte),
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 37) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 10) (Z_to_bv 64 (A + off)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * k)) x22 (Z_to_bv 64 9)
                   (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31)
              F (Z_to_bv 64 PCM_DIR) fc None m (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m
      /\ stk rsegs m lo (bv_unsigned sp + -2240)
      /\ rw_cells rsegs m (bv_unsigned sp + -104) (pcm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ rw_cells rsegs m (bv_unsigned sp + -2176) [CB 2072 jm]
      /\ rw_cells rsegs m (bv_unsigned sp + -2216) dir_fresh
      /\ rw_cells rsegs m (bv_unsigned sp + -2240) [CB 8 j8; C8 vq; C8 cq]
      /\ bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0])
      /\ bytes_at rsegs m VA (u64s slots).
End DIRINV.

Ltac unpack_dir H :=
  destruct H as (rax & x5 & x6 & x7 & x9 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x22 & x28 & x29 & x30 & x31
                 & vq & cq & jm & j8 & mq & -> & MU & WM & MI & ST & FRT & FRM & DIR & FRL & FB & VAA);
  unfold pcm_saved in FRT; unfold PCM_STACK in MU; unfold dir_fresh, m1w in DIR.
(* [comment removed for export] *)
Ltac pack_dir :=
  unfold pcm_dir, pcm_saved, PCM_DIR, PCM_STACK, FLAGCHARS, PAT, dir_fresh, m1w;
  hot_eexists_all;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
  [ | eassumption | eassumption | assumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SCAN.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 m1 : word -> option byte) (k e : Z).
  Variables (rax x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 vq cq : word) (jm j8 : list byte).
  Variable Q : machine_state -> Prop.
  Hypothesis FB1 : bytes_at rsegs m1 A (fbytes ++ [Z_to_bv 8 0]).
  Notation SAT pc p va0 :=
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 va0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 10) (Z_to_bv 64 (A + p)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * k)) x22 (Z_to_bv 64 9)
             (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).
  Hypothesis K37 : nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat e) = Some (Z_to_bv 8 37) -> evt rsegs Q (SAT 0x4a4e0 e 37).
  Hypothesis K0 : nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat e) = Some (Z_to_bv 8 0) -> evt rsegs Q (SAT 0x4a570 e 0).

  #[using="K0 K37 FB1 Clg"] Lemma pcm_scan : forall (cc : nat) (p : Z) (va0 : Z),
    (0 <= p)%Z -> (p + Z.of_nat cc = e)%Z ->
    (forall j b, (j < cc)%nat -> nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat p + j) = Some b -> bv_unsigned b <> 37%Z /\ bv_unsigned b <> 0%Z) ->
    (forall j, (j < cc)%nat -> exists b, nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat p + j) = Some b) ->
    (nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat e) = Some (Z_to_bv 8 37) \/ nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat e) = Some (Z_to_bv 8 0)) ->
    evt rsegs Q (SAT 0x4a4c8 p va0).
  Proof.
    induction cc as [|cc IH]; intros p va0 P0 PE LIT EX END.
    - cbn [Z.of_nat] in PE. rewrite Z.add_0_r in PE. subst e. pose proof (bytes_at_bound _ _ _ _ FB1) as AB.
      destruct END as [E37 | E0].
      + pose proof (fmt_read m1 A fbytes (Z.to_nat p) _ (Z_to_bv 64 (A + p)) FB1 E37 ltac:(f_equal; lia)) as RD.
        zs. cbv beta. change (bv_unsigned (Z_to_bv 8 37)) with 37%Z.
        zs. brf Kb; [| exfalso; apply Kb; reflexivity].
        apply K37; assumption.
      + pose proof (fmt_read m1 A fbytes (Z.to_nat p) _ (Z_to_bv 64 (A + p)) FB1 E0 ltac:(f_equal; lia)) as RD.
        zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zs. brf Kb. { exfalso. try (generalize alloc_ceiling_val); clear -Kb; try pose proof alloc_ceiling_val. cbv in Kb. lia. }
        zs. brf Kb2; [| exfalso; apply Kb2; reflexivity].
        apply K0; assumption.
    - destruct (EX 0%nat ltac:(lia)) as [b Hb]. destruct (LIT 0%nat b ltac:(lia) Hb) as [B37 B0].
      rewrite Nat.add_0_r in Hb. pose proof (bv_unsigned_in_range _ b) as BR.
      pose proof (fmt_read m1 A fbytes (Z.to_nat p) _ (Z_to_bv 64 (A + p)) FB1 Hb ltac:(f_equal; lia)) as RD.
      zs. cbv beta.
      zs. brf Kb. { exfalso. lia. }
      zs. brf Kb2. { exfalso. lia. }
      zs. zs. zs.
      replace (A + p + 1)%Z with (A + (p + 1))%Z by lia.
      apply IH; [lia| lia | | |].
      + intros j b' Hj Hb'. apply (LIT (S j) b' ltac:(lia)). replace (Z.to_nat p + S j)%nat with (Z.to_nat (p + 1) + j)%nat by lia. exact Hb'.
      + intros j Hj. destruct (EX (S j) ltac:(lia)) as [b' Hb']. exists b'. replace (Z.to_nat (p + 1) + j)%nat with (Z.to_nat p + S j)%nat by lia. exact Hb'.
      + exact END.
  Qed.
End SCAN.

(* [comment removed for export] *)
Definition lit_run (fbytes : list byte) (off : Z) (nl : nat) : Prop :=
  (forall j b, (j < nl)%nat -> nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off + j) = Some b -> bv_unsigned b <> 37%Z /\ bv_unsigned b <> 0%Z)
  /\ (forall j, (j < nl)%nat -> exists b, nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off + j) = Some b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TOPSEG.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).
  Hypothesis LOLE : (lo + PCM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis FLO : (A + Z.of_nat (length fbytes) + 1 <= lo)%Z.
  Notation DIRQ := (pcm_dir ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).
  Notation ATQ := (pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).
  Notation POSTQ := (pcm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0).

  (* [comment removed for export] *)
  #[using="FLO VLO CEIL LOLE Clg"] Lemma pcm_top_prefix : forall (Q : machine_state -> Prop) off k ms,
    ATQ PCM_TOP off k ms -> (0 <= off)%Z ->
    (forall rax x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 vq cq jm j8 m1,
        munch [(bv_unsigned sp - PCM_STACK, bv_unsigned sp)]%Z m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
        stk rsegs m1 lo (bv_unsigned sp + -2240) ->
        rw_cells rsegs m1 (bv_unsigned sp + -104) (pcm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
        rw_cells rsegs m1 (bv_unsigned sp + -2176) [CB 2072 jm] ->
        rw_cells rsegs m1 (bv_unsigned sp + -2216) dir_raw ->
        rw_cells rsegs m1 (bv_unsigned sp + -2240) [CB 8 j8; C8 vq; C8 cq] ->
        bytes_at rsegs m1 A (fbytes ++ [Z_to_bv 8 0]) -> bytes_at rsegs m1 VA (u64s slots) ->
        evt rsegs Q (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (bv_unsigned sp + -2216)) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 10) (Z_to_bv 64 (A + off)) (Z_to_bv 64 FLAGCHARS) (Z_to_bv 64 (VA + 8 * k)) x22 (Z_to_bv 64 9)
             (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31)
          F (Z_to_bv 64 PCM_SCAN) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms TOP OFF0 K. unpack_pcm TOP. unfold PCM_STACK, PCM_TOP, PCM_SCAN in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB. rewrite length_app in AB. cbn [length] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    do 5 zs.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (bv_unsigned sp + -2216)%Z _ |- _ => apply rw_cells_to_CB in H; cbn [cells_size csize cells_bytes cbytes Nat.add app] in H end.
    zs. zs. zs. zs.
    zs. call_lit imemset_spec by (idtac;
      lazymatch goal with
      | |- rw_cells _ _ _ _ => rewrite ?unsigned_lit by lia; match goal with H : rw_cells _ _ (bv_unsigned sp + -2216)%Z _ |- _ => eapply rwc_eq; [exact H| lia] end
      | |- mem_inv _ _ => eassumption
      | |- (Z.land _ _ <> _)%Z => vm_compute; discriminate
      | |- _ => rewrite ?unsigned_lit by lia; first [reflexivity | lia]
      end).
    change ((bv_unsigned (Z_to_bv 64 0) mod 256)%Z) with 0%Z in *.
    zs. (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mq (bv_unsigned sp + -2216)%Z _ |- _ =>
      rewrite ?firstn_repeat, ?skipn_repeat in H by lia;
      assert (DR : rw_cells rsegs mq (bv_unsigned sp + -2216) dir_raw) by (unfold dir_raw, zeros; eapply rwc_eq; [exact H| lia] || exact H); clear H end.
    eapply K; try eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="FLO VLO CEIL LOLE Clg"] Lemma pcm_top_dir : forall (Q : machine_state -> Prop) off k (nl : nat) ms,
    ATQ PCM_TOP off k ms -> (0 <= off)%Z -> lit_run fbytes off nl ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off + nl) = Some (Z_to_bv 8 37) ->
    (forall ms1, DIRQ (off + Z.of_nat nl) k ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k nl ms TOP OFF0 [LIT EX] E37 K.
    eapply pcm_top_prefix; [exact TOP| exact OFF0|]. intros.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    eapply pcm_scan with (e := (off + Z.of_nat nl)%Z) (cc := nl).
    all: try eassumption. all: try lia.
    all: lazymatch goal with
      | |- _ = Some (Z_to_bv 8 37) -> _ =>
          intros E; apply K; unfold PCM_STACK in *;
          match goal with H : rw_cells _ _ (bv_unsigned sp + -2216)%Z dir_raw |- _ => apply dir_raw_fresh in H end;
          pack_dir; reflexivity
      | |- _ = Some (Z_to_bv 8 0) -> _ =>
          intros E0; exfalso; replace (Z.to_nat (off + Z.of_nat nl)) with (Z.to_nat off + nl)%nat in E0 by lia; rewrite E37 in E0;
          assert (EE : Z_to_bv 8 37 = Z_to_bv 8 0) by congruence; apply (f_equal bv_unsigned) in EE; rewrite !Z_to_bv_unsigned in EE; vm_compute in EE; lia
      | |- _ \/ _ => left; replace (Z.to_nat (off + Z.of_nat nl)) with (Z.to_nat off + nl)%nat by lia; exact E37
      end.
  Qed.

  (* [comment removed for export] *)
  #[using="FLO VLO CEIL LOLE Clg"] Lemma pcm_top_end : forall off k (nl : nat) ms,
    ATQ PCM_TOP off k ms -> (0 <= off)%Z -> lit_run fbytes off nl ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off + nl) = Some (Z_to_bv 8 0) ->
    evt rsegs POSTQ ms.
  Proof.
    intros off k nl ms TOP OFF0 [LIT EX] E0.
    eapply pcm_top_prefix; [exact TOP| exact OFF0|]. intros.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    eapply pcm_scan with (e := (off + Z.of_nat nl)%Z) (cc := nl).
    all: try eassumption. all: try lia.
    all: lazymatch goal with
      | |- _ = Some (Z_to_bv 8 37) -> _ =>
          intros E37; exfalso; replace (Z.to_nat (off + Z.of_nat nl)) with (Z.to_nat off + nl)%nat in E37 by lia; rewrite E0 in E37;
          assert (EE : Z_to_bv 8 0 = Z_to_bv 8 37) by congruence; apply (f_equal bv_unsigned) in EE; rewrite !Z_to_bv_unsigned in EE; vm_compute in EE; lia
      | |- _ \/ _ => right; replace (Z.to_nat (off + Z.of_nat nl)) with (Z.to_nat off + nl)%nat by lia; exact E0
      | |- _ = Some (Z_to_bv 8 0) -> _ => intros E
      end.
    unfold PCM_STACK in *.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mq (bv_unsigned sp + -2216)%Z dir_raw |- _ =>
      pose proof (rw_cells_bytes_at_cell rsegs mq _ dir_raw 16 _ H ltac:(reflexivity)) as DB end.
    cbn [cbytes cells_size csize Nat.add] in DB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (u8ro_read rsegs mq _ _ 20 (Z_to_bv 8 0) (Z_to_bv 64 (bv_unsigned sp + -2184 + 4)) DB ltac:(reflexivity) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
    zs. brf Kb. { exfalso. apply Kb. reflexivity. }
    zs.
    match goal with H : bytes_at _ ?mq A _ |- _ =>
      pose proof (fmt_read mq A fbytes (Z.to_nat (off + Z.of_nat nl)) _ (Z_to_bv 64 (A + (off + Z.of_nat nl))) H E ltac:(f_equal; lia)) as RD2 end.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
    zs. brf Kb2. 2:{ exfalso. apply Kb2. reflexivity. }
    eapply pcm_exit; [| exact LOLE].
    match goal with H : rw_cells _ _ (bv_unsigned sp + -2216)%Z dir_raw |- _ => apply rw_cells_to_CB in H; cbn [cells_size csize Nat.add] in H end.
    pack_pcm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_next_top : forall (Q : machine_state -> Prop) off k ms b,
    ATQ PCM_NEXT off k ms -> (0 <= off)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some b -> bv_unsigned b <> 0%Z ->
    (forall ms1, ATQ PCM_TOP off k ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms b TOP OFF0 Hb BNZ K. unpack_pcm TOP. unfold PCM_STACK, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bv_unsigned_in_range _ b) as BR.
    pose proof (fmt_read mq A fbytes (Z.to_nat off) _ (Z_to_bv 64 (A + off)) FB Hb ltac:(f_equal; lia)) as RD.
    zs. cbv beta. zs. brf Kb. { exfalso. lia. }
    apply K. pack_pcm. reflexivity.
  Qed.

  #[using="LOLE"] Lemma pcm_next_exit : forall off k ms,
    ATQ PCM_NEXT off k ms -> (0 <= off)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 0) ->
    evt rsegs POSTQ ms.
  Proof.
    intros off k ms TOP OFF0 Hb. pose proof TOP as TOP'. unpack_pcm TOP. unfold PCM_STACK, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (fmt_read mq A fbytes (Z.to_nat off) _ (Z_to_bv 64 (A + off)) FB Hb ltac:(f_equal; lia)) as RD.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. brf Kb. 2:{ exfalso. apply Kb. reflexivity. }
    eapply pcm_exit; [| exact LOLE]. pack_pcm. reflexivity.
  Qed.
End TOPSEG.
End AIcpa7e.


Module AIcpo65.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm AIcppc0 AIcp2qw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpa7e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sf.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].
Ltac brf K := if_cases K; zify_cond K.

(* [comment removed for export] *)
Ltac call_istrchr SAT :=
  call_lit istrchr_spec by (idtac;
    lazymatch goal with
    | |- bytes_at _ _ _ _ => unfold FLAGCHARS; apply SAT; assumption
    | |- mem_inv _ _ => assumption
    | |- (bv_unsigned _ mod 256 = _)%Z => rewrite ?unsigned_lit by lia; reflexivity
    | |- strchr_scan _ _ _ = _ => vm_compute; reflexivity
    end);
  cbn [strchr_scan_val].

(* [comment removed for export] *)
Ltac fmt_rd i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
    lazymatch goal with FBq : bytes_at rsegs mq ?A (?fbytes ++ [Z_to_bv 8 0]) |- _ =>
      let RD := fresh "RD" in
      epose proof (fmt_read mq A fbytes (Z.to_nat i) _ (Z_to_bv 64 (A + i)) FBq ltac:(eassumption || (rewrite ?Z2Nat.inj_add by lia; eassumption)) ltac:(f_equal; lia)) as RD
    end end.

(* [comment removed for export] *)
Lemma slot_read8 : forall m VA slots (i : Z) w a,
  bytes_at rsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Section DIRSEG.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A : Z) (fbytes : list byte) (VA : Z) (slots : list word) (m0 : word -> option byte).
  Hypothesis LOLE : (lo + PCM_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis VLO : (bv_unsigned sp <= VA)%Z.
  Hypothesis VHI : (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z.
  Hypothesis FLO : (A + Z.of_nat (length fbytes) + 1 <= lo)%Z.
  Notation DIRQ := (pcm_dir ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).
  Notation ATQ := (pcm_at ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A fbytes VA slots m0).

  (* [comment removed for export] *)
  #[using="FLO VLO LOLE Clg"] Lemma pcm_dir_c : forall (Q : machine_state -> Prop) off k ms,
    DIRQ off k ms -> (0 <= off)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 37) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 1)) = Some (Z_to_bv 8 99) ->
    (forall ms1, ATQ PCM_NEXT (off + 2) (k + 1) ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms TOP OFF0 H37 H99 K. unpack_dir TOP. unfold PCM_STACK, PCM_DIR, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB. rewrite length_app in AB. cbn [length] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    zs. (* [comment removed for export] *)
    fmt_rd (off + 1)%Z.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 99)) with 99%Z.
    zto 0x6a344%Z. call_istrchr S_FLAGS_at.
    zto 0x4a584%Z. fmt_rd (off + 1)%Z.
    zto 0x6a344%Z. call_istrchr S_LENMOD_at.
    zto 0x6a344%Z. call_istrchr S_cCsS_at.
    zto 0x6a344%Z. call_istrchr S_CS_at.
    zto 0x6a344%Z. call_istrchr S_csB_at.
    zto 0x6a344%Z. call_istrchr S_sS_at.
    zto 0x6a344%Z. call_istrchr S_FLOAT_at.
    zto 0x4a494%Z.
    apply K. apply rw_cells_to_CB in DIR. cbn [cells_size csize Nat.add] in DIR.
    pack_pcm.
    replace (A + off + 2)%Z with (A + (off + 2))%Z by lia. replace (VA + 8 * k + 8)%Z with (VA + 8 * (k + 1))%Z by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="FLO VLO LOLE Clg"] Lemma pcm_dir_s : forall (Q : machine_state -> Prop) off k ms (hsw : word),
    DIRQ off k ms -> (0 <= off)%Z -> (0 <= k)%Z ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat off) = Some (Z_to_bv 8 37) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 1)) = Some (Z_to_bv 8 46) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 2)) = Some (Z_to_bv 8 42) ->
    nth_error (fbytes ++ [Z_to_bv 8 0]) (Z.to_nat (off + 3)) = Some (Z_to_bv 8 115) ->
    nth_error slots (Z.to_nat (k + 1)) = Some hsw -> bv_unsigned hsw <> 0%Z ->
    (forall ms1, ATQ PCM_NEXT (off + 4) (k + 2) ms1 -> evt rsegs Q ms1) ->
    evt rsegs Q ms.
  Proof.
    intros Q off k ms hsw TOP OFF0 K0 H37 H46 H42 H115 HS HSNZ K. unpack_dir TOP. unfold PCM_STACK, PCM_DIR, PCM_NEXT in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (bytes_at_bound _ _ _ _ FB) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (bytes_at_bound _ _ _ _ VAA) as VB. rewrite u64s_length in VB.
    pose proof (nth_error_Some_length _ _ HS) as KL || assert (KL : (Z.to_nat (k + 1) < length slots)%nat) by (destruct (Nat.lt_ge_cases (Z.to_nat (k + 1)) (length slots)) as [L|G]; [exact L| rewrite (proj2 (nth_error_None _ _) G) in HS; discriminate]).
    pose proof (bv_unsigned_in_range _ hsw) as HSR.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    zs. (* [comment removed for export] *)
    fmt_rd (off + 1)%Z.
    zs. cbv beta. change (bv_unsigned (Z_to_bv 8 46)) with 46%Z.
    zto 0x6a344%Z. call_istrchr S_FLAGS_at.
    zto 0x4a584%Z. fmt_rd (off + 1)%Z. fmt_rd (off + 2)%Z.
    zto 0x4a5cc%Z. fmt_rd (off + 3)%Z.
    zto 0x6a344%Z. call_istrchr S_LENMOD_at.
    zto 0x6a344%Z. call_istrchr S_FLOAT_at.
    zto 0x6a344%Z. call_istrchr S_cCsS_at.
    zto 0x6a344%Z. call_istrchr S_CS_at.
    zto 0x6a344%Z. call_istrchr S_csB_at.
    zto 0x6a344%Z. call_istrchr S_sS_at.
    zto 0x4a828%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with VAq : bytes_at rsegs mq VA (u64s slots) |- _ =>
        pose proof (slot_read8 mq VA slots (k + 1) hsw (Z_to_bv 64 (VA + 8 * k + 8)) VAq HS ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDV end end.
    zto 0x4a494%Z.
    apply K. apply rw_cells_to_CB in DIR. cbn [cells_size csize Nat.add] in DIR.
    pack_pcm.
    replace (A + off + 4)%Z with (A + (off + 4))%Z by lia. replace (VA + 8 * k + 16)%Z with (VA + 8 * (k + 2))%Z by lia. reflexivity.
  Qed.
End DIRSEG.
End AIcpo65.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpa7e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcpo65.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition FMTB_C : list byte := [Z_to_bv 8 37; Z_to_bv 8 99].                                          (* [comment removed for export] *)
Definition FMTB_PFX : list byte := [Z_to_bv 8 37; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 115; Z_to_bv 8 47].   (* [comment removed for export] *)
Definition FMTB_HOST : list byte :=                                                                        (* [comment removed for export] *)
  [Z_to_bv 8 72; Z_to_bv 8 111; Z_to_bv 8 115; Z_to_bv 8 116; Z_to_bv 8 58; Z_to_bv 8 32;
   Z_to_bv 8 37; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 115; Z_to_bv 8 37; Z_to_bv 8 99].

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition pcm_stmt (fbytes : list byte) (SLOTS : list word -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo A VA : Z) (slots : list word),
    a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    bytes_at rsegs m A (fbytes ++ [Z_to_bv 8 0]) -> bytes_at rsegs m VA (u64s slots) -> SLOTS slots ->
    map_cells m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    (lo + PCM_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
    (bv_unsigned sp <= VA)%Z -> (VA + 8 * Z.of_nat (length slots) <= 2^63)%Z ->
    range_ok m A (Z.of_nat (length fbytes) + 1) -> (A + Z.of_nat (length fbytes) + 1 <= lo)%Z ->
    evt rsegs (pcm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PCM_ENTRY) fc None m (seg_rom rsegs)).

End CEIL.

Definition SLOTS_C (slots : list word) : Prop := True.
Definition SLOTS_S (slots : list word) : Prop := exists hsw, nth_error slots 1 = Some hsw /\ bv_unsigned hsw <> 0%Z.

Ltac byte_neq := apply (f_equal bv_unsigned) || idtac; rewrite ?Z_to_bv_unsigned; vm_compute; lia.
Ltac lit_run_tac :=
  split;
  [ intros j b Hj Hb; do 13 (try (destruct j as [|j]; [cbn in Hb; inversion Hb; subst; rewrite !Z_to_bv_unsigned; vm_compute; lia |])); lia
  | intros j Hj; do 13 (try (destruct j as [|j]; [eexists; reflexivity|])); lia ].
Ltac seg_sides :=
  lazymatch goal with
  | |- pcm_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
  | |- pcm_dir _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eassumption
  | |- lit_run _ _ _ => lit_run_tac
  | |- nth_error _ _ = Some _ => first [reflexivity | eassumption]
  | |- (bv_unsigned _ <> _)%Z => first [eassumption | byte_neq]
  | |- (_ <= _)%Z => lia
  | |- (_ < _)%Z => lia
  | |- forall _, _ => idtac
  | |- ?G => idtac "seg_sides: unexpected goal" G
  end.
Ltac no_nul := cbv; intros HH; repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; rewrite !Z_to_bv_unsigned in HH; vm_compute in HH; lia|]); exact HH.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem pcm_fmt_c : pcm_stmt FMTB_C SLOTS_C.
Proof.
  unfold pcm_stmt. intros until slots. intros -> -> FB VAA _ MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_C VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_C VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 0%nat); [seg_sides ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_c _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_C VA slots m) with (off := 0%Z) (k := 0%Z); [seg_sides ..].
    intros ms3 T3.
    eapply (@pcm_next_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_C VA slots m); [seg_sides ..].
Qed.

Theorem pcm_fmt_pfx : pcm_stmt FMTB_PFX SLOTS_S.
Proof.
  unfold pcm_stmt. intros until slots. intros -> -> FB VAA (hsw & HS & HSNZ) MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_PFX VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_PFX VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 0%nat); [seg_sides ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_s _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_PFX VA slots m) with (off := 0%Z) (k := 0%Z) (hsw := hsw); [seg_sides ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_PFX VA slots m) with (off := 4%Z) (k := 2%Z); [seg_sides ..].
    intros ms4 T4.
    eapply (@pcm_top_end _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_PFX VA slots m) with (off := 4%Z) (k := 2%Z) (nl := 1%nat); [seg_sides ..].
Qed.

Theorem pcm_fmt_host : pcm_stmt FMTB_HOST SLOTS_S.
Proof.
  unfold pcm_stmt. intros until slots. intros -> -> FB VAA (hsw & HS & HSNZ) MC MI ST LOLE CEIL VLO VHI RNG FLO.
  eapply (@pcm_entry _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m); try eassumption.
  - no_nul.
  - discriminate.
  - cbn; lia.
  - intros ms1 T1.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m) with (off := 0%Z) (k := 0%Z) (nl := 6%nat); [seg_sides ..].
    intros ms2 T2. cbn [Z.of_nat Z.add] in T2.
    eapply (@pcm_dir_s _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m) with (off := 6%Z) (k := 0%Z) (hsw := hsw); [seg_sides ..].
    intros ms3 T3. cbn [Z.add] in T3.
    eapply (@pcm_next_top ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m) with (off := 10%Z) (k := 2%Z); [seg_sides ..].
    intros ms4 T4.
    eapply (@pcm_top_dir _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m) with (off := 10%Z) (k := 2%Z) (nl := 0%nat); [seg_sides ..].
    intros ms5 T5. cbn [Z.of_nat Z.add] in T5.
    eapply (@pcm_dir_c _ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m) with (off := 10%Z) (k := 2%Z); [seg_sides ..].
    intros ms6 T6.
    eapply (@pcm_next_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo A FMTB_HOST VA slots m); [seg_sides ..].
Qed.

End CEIL2.
