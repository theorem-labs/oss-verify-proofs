(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTail.v, with its module paths and module names changed; 534 of its 819 lines of code are new or changed and 1220 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/YTail.v blob 3b859284448d at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives YTail.v's <r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that
   its type is the type of YTail.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (ExecF.evtF) forms of the six instruction runs of Seg/YTail.v (segments Y3, Y2, Y1 and Jrel of
   fuzz_ctrl LLVMFuzzerTestOneInput, asan image A, libreac v1.9.0: the release tail 0x82b80-0x82bf0). Each
   <run>_F is YTail.v's <run> with a footprint binder RNG FIRST, the same binders and premises in the same order,
   plain ExecF.rng premises appended, and the run an ExecF.evtF under RNG. The regions, per run:
   - y3_evt_F (0x82bb0-): the 13 reloads of the saved registers, [S - 104, S);
   - jrel_evt_real_F / jrel_evt_side_F (0x82b80-0x82bac / 0x82b9c): the frame header store, [fr, fr + 8);
   - y2_evt_F / y2_evt_r_F (0x82bac, the call of meta_fill_00): the callee's footprint, the general contract
     asan_set_shadow_00_contract_F: the image and the 392 shadow bytes [A, A + 392) it clears;
   - y1_evt_F (0x82b9c, the call of frame_release_6, and the `j 0x82bb0` at 0x82ba0, which accesses no memory):
     the callee's footprint (stack_free_6_F below): the image, its stack window [sp - 32, sp), the side stack
     [FS, FS + FS_SIZE) (the flag byte and the frame's last word) and the 512 shadow bytes of the frame.
   No access of these runs is instrumented (the reloads of Y3 and the header store of Jrel have no shadow check
   before them), so no shadow premise of an instrumented access is needed.
   y2_evt and y1_evt are lifted through MemNorm.evt_normalize; their footprint forms use lib/A/MemNormF.v
   evtF_normalize_ro, the evtF form of the same lemma (a run already lifted through evt_normalize keeps that lift).

   stack_free_6_F RNG is the in-tree contract (asan_stack_free_c.v asan_stack_free_6_contract) with the run an
   evtF under RNG and one rng premise per region the callee touches, in the form of Seg/X12F.v memchr_wrap_F (RNG
   alone quantified outside); the call target is named (ASAN_STACK_FREE_6 = 0x3dbf4, v1.9 on this base), and
   stack_free_6_F_gen proves it at EVERY footprint from the general-footprint theorem
   ASF.asan_stack_free_6_holds_F (lib/A/Prog/asan_stack_freeF.v, whose asan_stack_free_6_contract_F of
   lib/A/Prog/asan_stack_free_cF.v is this definition's text); stack_free_6_F_all is its RNG_all instance,
   which is how the corollary discharges it.
   The meta_fill_00 premise is NOT restated here: it is the general footprint contract
   asan_set_shadow_00_contract_F of lib/A/Prog/asan_set_shadow_cF.v (ASAN_SET_SHADOW_00 = 0x54ee8), itself
   quantified over the footprint, taken as a premise of the two _F runs in the shape Seg/R19F.v takes
   bcmp_wrap_contract_F. SSF.asan_set_shadow_00_holds_F (lib/A/Prog/asan_set_shadowF.v) proves it from
   memset_holds, which is how the two corollaries discharge it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_free_c asan_set_shadow_c asan_stack_malloc_c asan_set_shadow memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_set_shadowF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_freeF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sf6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs YTail.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF_all RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_free_c_on.
(* LAST: StepF's step / store_done / finish match evtF goals and shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* After StepF: the image-A YK11 by full path, as in YTail.v, to restore getr. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module EFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF_all.
Module RB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module SYT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.YTail.
Module SSF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadowF.
Module ASF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_freeF.
Module SFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_free_c_on.

(* ---------------------------------------------------------------- the second callee's footprint need *)

(* meta_fill_00 (ASAN_SET_SHADOW_00) needs no local statement: the two runs below take the general footprint
   contract asan_set_shadow_00_contract_F (lib/A/Prog/asan_set_shadow_cF.v) itself, and the corollaries discharge
   it from SSF.asan_set_shadow_00_holds_F memset_holds. *)

(* frame_release_6 (ASAN_STACK_FREE_6): asan_stack_free_6_contract with the run an evtF under RNG; it reads the
   image cells, uses its stack window [sp - 32, sp), reads the frame's last word and writes the flag byte (both in
   the side stack [FS, FS + FS_SIZE)), and writes the frame's fs_shadow_n 6 L shadow bytes. *)
Definition stack_free_6_F (RNG : ExecF.footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M 6 -> fr = fs_frame FS 6 j ->
  1 <= L <= fs_B 6 -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + 32 <= S0 -> FS + FS_SIZE <= S0 - 32 ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (S0 - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) (fs_shadow_n 6 L) ->
  ExecF.evtF rsegs RNG (SF.asan_stack_free_post 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SF.ASAN_STACK_FREE_6) fc None m (seg_rom rsegs)).

(* At every footprint it is the proved contract: lib/A/Prog/asan_stack_freeF.v's asan_stack_free_6_holds_F
   proves asan_stack_free_6_contract_F of lib/A/Prog/asan_stack_free_cF.v, whose text is this definition's. *)
Lemma stack_free_6_F_gen : forall RNG, stack_free_6_F RNG.
Proof. exact ASF.asan_stack_free_6_holds_F. Qed.

(* At RNG_all it is the proved contract. *)
Lemma stack_free_6_F_all : stack_free_6_F ExecF.RNG_all.
Proof. exact (stack_free_6_F_gen ExecF.RNG_all). Qed.

(* Route (C) (a Theorem Labs lane 09:20Z; frozen form a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery); R = the shadow bytes the run reads and
   stores through its shadow_rw premise, a Theorem Labs lane 10:33Z): stack_free_6_F over frame_release_6's _on contract
   (a Theorem Labs lane's leaf asan_stack_free_c_on.v, f99fbd501ea). Its shadow premise is the callee's own region
   SFO.asan_stack_free_shadow_R 6 L FS j (the frame shadow it fills with 0xf5; it reads no shadow), its post
   SFO.asan_stack_free_post_on (the POST form). stack_free_6_F and stack_free_6_F_all above are unchanged. *)
Definition stack_free_6_F_on (RNG : ExecF.footprint) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M 6 -> fr = fs_frame FS 6 j ->
  1 <= L <= fs_B 6 -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (SFO.asan_stack_free_shadow_R 6 L FS j) m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + 32 <= S0 -> FS + FS_SIZE <= S0 - 32 ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (S0 - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) (fs_shadow_n 6 L) ->
  ExecF.evtF rsegs RNG
    (SFO.asan_stack_free_post_on 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SF.ASAN_STACK_FREE_6) fc None m (seg_rom rsegs)).

(* At RNG_all it is the _on contract. *)
Lemma stack_free_6_F_on_all : SFO.asan_stack_free_6_contract_on -> stack_free_6_F_on ExecF.RNG_all.
Proof.
  intros HSF6. unfold stack_free_6_F_on. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS j
    HJ EFR HL HL8 PL FLG FLW AC SRW MI ST LOK ROOM HLO HHI _ _ _ _ _.
  apply EFA.evt_evtF_all.
  pose proof HSF6 as HS.
  unfold SFO.asan_stack_free_6_contract_on, SFO.asan_stack_free_contract_on, SF.ASAN_STACK_FREE_K in HS.
  cbv zeta in HS.
  exact (HS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS j
           HJ EFR HL HL8 PL FLG FLW AC SRW MI ST LOK ROOM HLO HHI).
Qed.

(* At EVERY footprint stack_free_6_F_on is proved, with no premise: lib/A/Prog/asan_stack_freeF.v's
   asan_stack_free_6_holds_F_on is the route (C) twin of asan_stack_free_6_holds_F (the general-footprint run of
   Tk/AW/Sf6L.stack_free_6_L on the restricted memory), stated with this definition's text. Its R is
   SFO.asan_stack_free_shadow_R 6 L FS j, which the run needs PRESENT: its 64 stores fill exactly those 512 shadow
   bytes and it reads no shadow. A consumer at its own footprint (ACtlG/Y1.v, RNG := PB.RNG_W (w_H W3)) takes this
   lemma at that RNG. *)
Lemma stack_free_6_F_on_gen : forall RNG : ExecF.footprint, stack_free_6_F_on RNG.
Proof. exact ASF.asan_stack_free_6_holds_F_on. Qed.

(* ---------------------------------------------------------------- the footprint runs *)

(* YTail.v's ytail_br on evtF goals. *)
Ltac ytailf_br b H :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* Y3's run: 0x82bb0 li a0,0; addi sp,s0,-416; ld ra / s0-s11 from [sp+408 .. sp+312] = [S-8 .. S-104];
   addi sp,sp,416; ret. *)
Lemma y3_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sv Rv : Z)
         (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
    v0 = Z_to_bv 64 Sv -> 416 <= Sv < 2 ^ 64 -> Rv mod 2 = 0 -> 0 <= Rv < 2 ^ 64 ->
    w1 = Z_to_bv 64 Rv ->
    bytes_at rsegs m (Sv - 104) (le8 w27 ++ le8 w26 ++ le8 w25 ++ le8 w24 ++ le8 w23 ++ le8 w22 ++ le8 w21 ++
      le8 w20 ++ le8 w19 ++ le8 w18 ++ le8 w9 ++ le8 w8 ++ le8 w1) ->
    (* the 13 reloads *)
    ExecF.rng RNG (Sv - 104) 104 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR w1 (Z_to_bv 64 Sv) gp tp t0' t1' t2' w8 w9
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 Rv) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82bb0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Fr fc m Sv Rv w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
    -> HS HRe HRb -> HSV RSV.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 104) (le8 w27) _) HSV) as (B27 & Q1).
  rewrite length_le8 in Q1. replace (Sv - 104 + Z.of_nat 8) with (Sv - 96) in Q1 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 96) (le8 w26) _) Q1) as (B26 & Q2).
  rewrite length_le8 in Q2. replace (Sv - 96 + Z.of_nat 8) with (Sv - 88) in Q2 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 88) (le8 w25) _) Q2) as (B25 & Q3).
  rewrite length_le8 in Q3. replace (Sv - 88 + Z.of_nat 8) with (Sv - 80) in Q3 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 80) (le8 w24) _) Q3) as (B24 & Q4).
  rewrite length_le8 in Q4. replace (Sv - 80 + Z.of_nat 8) with (Sv - 72) in Q4 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 72) (le8 w23) _) Q4) as (B23 & Q5).
  rewrite length_le8 in Q5. replace (Sv - 72 + Z.of_nat 8) with (Sv - 64) in Q5 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 64) (le8 w22) _) Q5) as (B22 & Q6).
  rewrite length_le8 in Q6. replace (Sv - 64 + Z.of_nat 8) with (Sv - 56) in Q6 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 56) (le8 w21) _) Q6) as (B21 & Q7).
  rewrite length_le8 in Q7. replace (Sv - 56 + Z.of_nat 8) with (Sv - 48) in Q7 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 48) (le8 w20) _) Q7) as (B20 & Q8).
  rewrite length_le8 in Q8. replace (Sv - 48 + Z.of_nat 8) with (Sv - 40) in Q8 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 40) (le8 w19) _) Q8) as (B19 & Q9).
  rewrite length_le8 in Q9. replace (Sv - 40 + Z.of_nat 8) with (Sv - 32) in Q9 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 32) (le8 w18) _) Q9) as (B18 & Q10).
  rewrite length_le8 in Q10. replace (Sv - 32 + Z.of_nat 8) with (Sv - 24) in Q10 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 24) (le8 w9) _) Q10) as (B9 & Q11).
  rewrite length_le8 in Q11. replace (Sv - 24 + Z.of_nat 8) with (Sv - 16) in Q11 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 16) (le8 w8) _) Q11) as (B8 & Q12).
  rewrite length_le8 in Q12. replace (Sv - 16 + Z.of_nat 8) with (Sv - 8) in Q12 by lia.
  pose proof (rd8 m (Sv - 104) w27 B27) as L27.
  pose proof (rd8 m (Sv - 96) w26 B26) as L26.
  pose proof (rd8 m (Sv - 88) w25 B25) as L25.
  pose proof (rd8 m (Sv - 80) w24 B24) as L24.
  pose proof (rd8 m (Sv - 72) w23 B23) as L23.
  pose proof (rd8 m (Sv - 64) w22 B22) as L22.
  pose proof (rd8 m (Sv - 56) w21 B21) as L21.
  pose proof (rd8 m (Sv - 48) w20 B20) as L20.
  pose proof (rd8 m (Sv - 40) w19 B19) as L19.
  pose proof (rd8 m (Sv - 32) w18 B18) as L18.
  pose proof (rd8 m (Sv - 24) w9 B9) as L9.
  pose proof (rd8 m (Sv - 16) w8 B8) as L8.
  pose proof (rd8 m (Sv - 8) (Z_to_bv 64 Rv) Q12) as L1.
  clear B27 B26 B25 B24 B23 B22 B21 B20 B19 B18 B9 B8 Q12 HSV.
  step. step.
  do 13 step.
  step. step.
  rewrite ?Z.add_0_r.
  replace (Sv + -416 + 416) with Sv by lia.
  replace (ret_pc (Z_to_bv 64 Rv)) with (Z_to_bv 64 Rv)
    by (symmetry; apply ret_pc_even; [lia | exact HRe]).
  apply ExecF.evtF_done. do 14 eexists. reflexivity.
Qed.

Lemma y3_evt_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sv Rv : Z)
         (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
    v0 = Z_to_bv 64 Sv -> 416 <= Sv < 2 ^ 64 -> Rv mod 2 = 0 -> 0 <= Rv < 2 ^ 64 ->
    w1 = Z_to_bv 64 Rv ->
    bytes_at rsegs m (Sv - 104) (le8 w27 ++ le8 w26 ++ le8 w25 ++ le8 w24 ++ le8 w23 ++ le8 w22 ++ le8 w21 ++
      le8 w20 ++ le8 w19 ++ le8 w18 ++ le8 w9 ++ le8 w8 ++ le8 w1) ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR w1 (Z_to_bv 64 Sv) gp tp t0' t1' t2' w8 w9
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 Rv) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82bb0) fc None m (seg_rom rsegs)).
Proof.
  intros. eapply ExecF.evtF_evt. eapply y3_evt_F with (RNG := ExecF.RNG_all); try eassumption.
  apply ExecF.rng_all; lia.
Qed.

(* ---- Y2's call (0x82bac `jal 54ee8 <meta_fill_00>`) and Y1's call (0x82b9c `jal 3dbf4 <frame_release_6>`), on
   the normalized memory as in YTail.v; the lift is MemNormF.evtF_normalize_ro. *)
Section Runs.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

Lemma y2_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  (* the callee's footprint at 0x82bac: the image and the 392 shadow bytes it clears *)
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG A 392 ->
  asan_set_shadow_00_contract_F ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch [(A, A + 392)] mem m' /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk HAb HSh Hrw Hac HRO RBY RIMG RSH HSS.
  step.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  pose proof HSS as SS0.
  unfold asan_set_shadow_00_contract_F, asan_set_shadow_contract_F, ASAN_SET_SHADOW_00 in SS0. cbv zeta in SS0.
  assert (HC : ExecF.evtF rsegs RNG
      (asan_set_shadow_post 0 (Z_to_bv 64 0x82bb0) sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         fp_regs fp_csr (Z_to_bv 64 A) (Z_to_bv 64 392) (normalize rsegs mem))
      (MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 0x54ee8) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (SS0 RNG (Z_to_bv 64 0x82bb0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             fp_regs fp_csr (normalize rsegs mem) junk).
    - rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia.
      rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 392) by lia. exact HSh.
    - rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia.
      rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 392) by lia. exact Hrw.
    - exact Hac.
    - apply mem_inv_normalize.
    - exact RBY.
    - unfold IMG_LO, IMG_HI. exact RIMG.
    - (* the helper's own stack window is empty (ASAN_SET_SHADOW_K = 0); rng_bytes gives every empty range *)
      unfold ASAN_SET_SHADOW_K.
      pose proof (bv_unsigned_in_range 64 sp0) as Rsp.
      unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
      split; [lia|]. split; [lia|]. intros b j Hb Hj.
      apply RBY; [lia | lia | intros k Hk; exfalso; lia].
    - rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) by lia.
      rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 392) by lia. exact RSH. }
  pose proof (MNF.evtF_normalize_ro RNG _ _ fp_regs _ fp_csr None mem (seg_rom rsegs) HRO HC) as HE.
  eapply ExecF.evtF_mono; [exact HE|].
  intros ms (st0 & Hp & Hrel & Hro2).
  unfold asan_set_shadow_post in Hp.
  destruct Hp as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m0' & -> & MU & WM & MI & RW).
  rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit A) in MU, RW by lia.
  rewrite !(OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 392) in MU, RW by lia.
  destruct ms as [R' F' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (HRg & HFg & HPg & HSg & HRv & HFc & HRo & HMR).
  cbn in HRg, HFg, HPg, HSg, HRv, HFc, HRo, HMR. subst.
  cbn in Hro2.
  exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
  split.
  { replace (ret_pc (Z_to_bv 64 0x82bb0)) with (Z_to_bv 64 0x82bb0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  split; [exact (munch_rel rsegs [(A, A + 392)] mem (normalize rsegs mem) m' m0' REL HMR Hro2 MU)|].
  split; [exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' REL HMR Hro2 WM)|].
  split; [exact (ro_agree_same rsegs mem m' HRO Hro2)|].
  destruct RW as ((Hwf & Hba) & Hwr). cbn [cells_bytes app] in Hba. rewrite app_nil_r in Hba.
  exact (proj2 (bytes_at_rel rsegs m' m0' A _ HMR) Hba).
Qed.

Lemma y2_evt_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(A, A + 392)] mem m' /\ Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk HAb HSh Hrw Hac HRO.
  pose proof (HSh 391 ltac:(lia)) as H391.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H391.
  eapply ExecF.evtF_evt. eapply y2_evt_F with (RNG := ExecF.RNG_all); try eassumption.
  - intros ? ? ? ? ?; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - exact (SSF.asan_set_shadow_00_holds_F memset_holds).
Qed.

(* y2_evt_F with the two argument registers as plain words plus their value equations (YTail.v y2_evt_r). *)
Lemma y2_evt_r_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  a0w = Z_to_bv 64 A -> a1w = Z_to_bv 64 392 ->
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG A 392 ->
  asan_set_shadow_00_contract_F ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch [(A, A + 392)] mem m' /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk -> -> HAb HSh Hrw Hac HRO RBY RIMG RSH HSS.
  exact (y2_evt_F RNG ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk HAb HSh Hrw Hac HRO RBY RIMG RSH HSS).
Qed.

Lemma y2_evt_r_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  a0w = Z_to_bv 64 A -> a1w = Z_to_bv 64 392 ->
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(A, A + 392)] mem m' /\ Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk E0 E1 HAb HSh Hrw Hac HRO.
  pose proof (HSh 391 ltac:(lia)) as H391.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H391.
  eapply ExecF.evtF_evt. eapply y2_evt_r_F with (RNG := ExecF.RNG_all); try eassumption.
  - intros ? ? ? ? ?; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - exact (SSF.asan_set_shadow_00_holds_F memset_holds).
Qed.

(* ---- Y1's call (0x82b9c `jal 3dbf4 <frame_release_6>`, side arm) and the `j 0x82bb0` at 0x82ba0. *)
Lemma y1_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (fr FS j lo spv : Z),
  a0w = Z_to_bv 64 fr -> a1w = Z_to_bv 64 3136 -> bv_unsigned sp0 = spv ->
  fr = fs_frame FS 6 j -> 0 <= j < fs_M 6 ->
  fs_place mem FS ->
  bytes_at rsegs mem (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs mem (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells mem -> shadow_rw mem ->
  stk rsegs mem lo spv -> lo + 32 <= spv -> FS + FS_SIZE <= spv - 32 ->
  HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
  ro_agree rsegs mem ->
  (* the callee's footprint at 0x82b9c: the image, its stack window, the side stack, the frame's shadow *)
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (spv - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) 512 ->
  stack_free_6_F RNG ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch
                   [(fs_flag FS 6 j, fs_flag FS 6 j + 1); (shadow_addr fr, shadow_addr fr + 512);
                    (spv - 32, spv)] mem m' /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       stk rsegs m' lo spv /\
       bytes_at rsegs m' (fs_flag FS 6 j) [Z_to_bv 8 0] /\
       bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) 512) /\
       shadow_rw m')
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b9c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem fr FS j lo spv -> -> Esp EFR Hj PL FLG FLW HAC HSW HST
    HLOK HROOM HHI HSPA HRO RBY RIMG RSTK RFS RSHF HSF.
  subst spv fr.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (Hfrv : fs_frame FS 6 j = FS + 6328320 + j * 4096) by (unfold fs_frame, fs_B; cbn; lia).
  assert (HFSz : FS_SIZE = 11571200) by reflexivity.
  pose proof PL as (HFS0 & _ & _ & _ & _).
  assert (Hfrb : 0 <= fs_frame FS 6 j < 2 ^ 64) by (rewrite Hfrv; rewrite HM6 in Hj; unfold APPMEM_END in *; lia).
  assert (Hlo0 : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in HHI; lia).
  assert (Hsp64 : bv_unsigned sp0 <= 2 ^ 64) by (unfold APPMEM_END in HSPA; lia).
  step.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  pose proof HSF as SF0.
  unfold stack_free_6_F, SF.ASAN_STACK_FREE_6 in SF0. cbv zeta in SF0.
  assert (HC : ExecF.evtF rsegs RNG
      (SF.asan_stack_free_post 6 32 (Z_to_bv 64 0x82ba0) sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         fp_regs fp_csr (bv_unsigned (Z_to_bv 64 3136)) FS j lo (normalize rsegs mem))
      (MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 0x3dbf4) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (SF0 (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             fp_regs fp_csr (normalize rsegs mem) lo FS j).
    - exact Hj.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      reflexivity.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia. rewrite HB6. lia.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia. reflexivity.
    - destruct PL as (P1 & P2 & P3 & P4 & P5).
      split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      apply (stk_rel_hi mem _ FS (FS + FS_SIZE) REL); [unfold ASAN_GT in P3; lia | lia | exact P5].
    - exact (ba_rel1 mem _ _ _ REL FLG).
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      exact (ba_rel1 mem _ _ _ REL FLW).
    - exact (asan_cells_rel mem _ REL HAC).
    - exact (shadow_rw_rel mem _ REL HSW).
    - exact (mem_inv_normalize rsegs mem).
    - exact (stk_rel_hi mem _ lo (bv_unsigned sp0) REL Hlo0 Hsp64 HST).
    - exact HLOK.
    - exact HROOM.
    - exact HHI.
    - exact HSPA.
    - exact RBY.
    - exact RIMG.
    - exact RSTK.
    - exact RFS.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia.
      replace (fs_shadow_n 6 3136) with 512 by (vm_compute; reflexivity). exact RSHF. }
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) in HC by lia.
  pose proof (MNF.evtF_normalize_ro RNG _ _ fp_regs _ fp_csr None mem (seg_rom rsegs) HRO HC) as HE.
  eapply ExecF.evtF_cut; [exact HE|].
  intros ms (st0 & Hp & Hrel & Hro2).
  unfold SF.asan_stack_free_post in Hp. cbv zeta in Hp.
  destruct Hp as (q0 & q1 & q2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & m0' &
                  -> & MU & WM & MI & ST' & PL' & FLG' & SHB' & AC' & SW').
  replace (fs_shadow_n 6 3136) with 512 in MU by (vm_compute; reflexivity).
  replace (Z.to_nat (fs_shadow_n 6 3136)) with 512%nat in SHB' by (vm_compute; reflexivity).
  destruct Hrel as (HRg & HFg & HPg & HSg & HRv & HFc & HRo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS]
    in HRg, HFg, HPg, HSg, HRv, HFc, HRo, HMR.
  (* the state after the return, in MS form so that the `j` at 0x82ba0 can be stepped *)
  assert (Ems : ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp q0 q1 q2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
                     fp_regs (Z_to_bv 64 0x82ba0) fp_csr None (ms_mem ms) (seg_rom rsegs)).
  { destruct ms as [R' F' pcv' svc' rv' fc' m' ro']. cbn in HRg, HFg, HPg, HSg, HRv, HFc, HRo |- *. subst.
    replace (ret_pc (Z_to_bv 64 0x82ba0)) with (Z_to_bv 64 0x82ba0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  rewrite Ems. set (m' := ms_mem ms) in *. clear Ems HRg HFg HPg HSg HRv HFc HRo.
  step.
  apply ExecF.evtF_done.
  exists q0, q1, q2, b0, b1, b2, b3, b4, b5, b6, b7, q3, q4, q5, q6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' REL HMR Hro2 MU)|].
  split; [exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' REL HMR Hro2 WM)|].
  split; [exact (ro_agree_same rsegs mem m' HRO Hro2)|].
  split; [exact (stk_rel_hi_back m' m0' lo (bv_unsigned sp0) HMR Hlo0 Hsp64 ST')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) FLG')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) SHB')|].
  exact (shadow_rw_rel_back m' m0' HMR SW').
Qed.

Lemma y1_evt_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (fr FS j lo spv : Z),
  a0w = Z_to_bv 64 fr -> a1w = Z_to_bv 64 3136 -> bv_unsigned sp0 = spv ->
  fr = fs_frame FS 6 j -> 0 <= j < fs_M 6 ->
  fs_place mem FS ->
  bytes_at rsegs mem (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs mem (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells mem -> shadow_rw mem ->
  stk rsegs mem lo spv -> lo + 32 <= spv -> FS + FS_SIZE <= spv - 32 ->
  HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(fs_flag FS 6 j, fs_flag FS 6 j + 1); (shadow_addr fr, shadow_addr fr + 512);
                    (spv - 32, spv)] mem m' /\
       Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\ stk rsegs m' lo spv /\
       bytes_at rsegs m' (fs_flag FS 6 j) [Z_to_bv 8 0] /\
       bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) 512) /\
       shadow_rw m')
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b9c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem fr FS j lo spv E0 E1 Esp EFR Hj PL FLG FLW HAC HSW HST
    HLOK HROOM HHI HSPA HRO.
  pose proof PL as (HFS0 & _ & _ & _ & _).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite EFR; unfold fs_frame, fs_B; cbn; lia).
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (Hj' : 0 <= j < 256) by (rewrite <- HM6; exact Hj).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr1 : fr < 2 ^ 64) by (unfold FS_SIZE, APPMEM_END in *; lia).
  eapply ExecF.evtF_evt. eapply y1_evt_F with (RNG := ExecF.RNG_all); try eassumption.
  - intros ? ? ? ? ?; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold FS_SIZE, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - exact stack_free_6_F_all.
Qed.

(* ---- Route (C) twins of y1_evt_F / y1_evt_of_F (the old two above are unchanged). The run's own instructions
   (the jal at 0x82b9c and the `j` at 0x82ba0) access no memory, so R is the callee's region at the call
   (a0 = fr = fs_frame FS 6 j, a1 = 3136): SFO.asan_stack_free_shadow_R 6 3136 FS j, the frame's 512 shadow bytes
   frame_release_6 stores; it is moved to the normalized memory by A.ShadowRwOnT.shadow_rw_on_rel and each kept
   region back by shadow_rw_on_of_rel (in place of YTail.shadow_rw_rel / shadow_rw_rel_back). The callee is
   stack_free_6_F_on (y1_evt_F_on) and SFO.asan_stack_free_6_contract_on (y1_evt_of_F_on). *)
Lemma y1_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (fr FS j lo spv : Z),
  a0w = Z_to_bv 64 fr -> a1w = Z_to_bv 64 3136 -> bv_unsigned sp0 = spv ->
  fr = fs_frame FS 6 j -> 0 <= j < fs_M 6 ->
  fs_place mem FS ->
  bytes_at rsegs mem (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs mem (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells mem -> A.ShadowRwOn.shadow_rw_on (SFO.asan_stack_free_shadow_R 6 3136 FS j) mem ->
  stk rsegs mem lo spv -> lo + 32 <= spv -> FS + FS_SIZE <= spv - 32 ->
  HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
  ro_agree rsegs mem ->
  (* the callee's footprint at 0x82b9c: the image, its stack window, the side stack, the frame's shadow *)
  RB.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (spv - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) 512 ->
  stack_free_6_F_on RNG ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch
                   [(fs_flag FS 6 j, fs_flag FS 6 j + 1); (shadow_addr fr, shadow_addr fr + 512);
                    (spv - 32, spv)] mem m' /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       stk rsegs m' lo spv /\
       bytes_at rsegs m' (fs_flag FS 6 j) [Z_to_bv 8 0] /\
       bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) 512) /\
       (forall P, A.ShadowRwOn.shadow_rw_on P mem -> A.ShadowRwOn.shadow_rw_on P m'))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b9c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem fr FS j lo spv -> -> Esp EFR Hj PL FLG FLW HAC HSW HST
    HLOK HROOM HHI HSPA HRO RBY RIMG RSTK RFS RSHF HSF.
  subst spv fr.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (Hfrv : fs_frame FS 6 j = FS + 6328320 + j * 4096) by (unfold fs_frame, fs_B; cbn; lia).
  assert (HFSz : FS_SIZE = 11571200) by reflexivity.
  pose proof PL as (HFS0 & _ & _ & _ & _).
  assert (Hfrb : 0 <= fs_frame FS 6 j < 2 ^ 64) by (rewrite Hfrv; rewrite HM6 in Hj; unfold APPMEM_END in *; lia).
  assert (Hlo0 : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in HHI; lia).
  assert (Hsp64 : bv_unsigned sp0 <= 2 ^ 64) by (unfold APPMEM_END in HSPA; lia).
  step.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  pose proof HSF as SF0.
  unfold stack_free_6_F_on, SF.ASAN_STACK_FREE_6 in SF0. cbv zeta in SF0.
  assert (HC : ExecF.evtF rsegs RNG
      (SFO.asan_stack_free_post_on 6 32 (Z_to_bv 64 0x82ba0) sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         fp_regs fp_csr (bv_unsigned (Z_to_bv 64 3136)) FS j lo (normalize rsegs mem))
      (MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 0x3dbf4) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (SF0 (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             fp_regs fp_csr (normalize rsegs mem) lo FS j).
    - exact Hj.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      reflexivity.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia. rewrite HB6. lia.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia. reflexivity.
    - destruct PL as (P1 & P2 & P3 & P4 & P5).
      split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      apply (stk_rel_hi mem _ FS (FS + FS_SIZE) REL); [unfold ASAN_GT in P3; lia | lia | exact P5].
    - exact (ba_rel1 mem _ _ _ REL FLG).
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      exact (ba_rel1 mem _ _ _ REL FLW).
    - exact (asan_cells_rel mem _ REL HAC).
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia.
      exact (A.ShadowRwOnT.shadow_rw_on_rel _ mem _ REL HSW).
    - exact (mem_inv_normalize rsegs mem).
    - exact (stk_rel_hi mem _ lo (bv_unsigned sp0) REL Hlo0 Hsp64 HST).
    - exact HLOK.
    - exact HROOM.
    - exact HHI.
    - exact HSPA.
    - exact RBY.
    - exact RIMG.
    - exact RSTK.
    - exact RFS.
    - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb.
      rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) by lia.
      replace (fs_shadow_n 6 3136) with 512 by (vm_compute; reflexivity). exact RSHF. }
  rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit 3136) in HC by lia.
  pose proof (MNF.evtF_normalize_ro RNG _ _ fp_regs _ fp_csr None mem (seg_rom rsegs) HRO HC) as HE.
  eapply ExecF.evtF_cut; [exact HE|].
  intros ms (st0 & Hp & Hrel & Hro2).
  unfold SFO.asan_stack_free_post_on in Hp. cbv zeta in Hp.
  destruct Hp as (q0 & q1 & q2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & m0' &
                  -> & MU & WM & MI & ST' & PL' & FLG' & SHB' & AC' & SW').
  replace (fs_shadow_n 6 3136) with 512 in MU by (vm_compute; reflexivity).
  replace (Z.to_nat (fs_shadow_n 6 3136)) with 512%nat in SHB' by (vm_compute; reflexivity).
  destruct Hrel as (HRg & HFg & HPg & HSg & HRv & HFc & HRo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS]
    in HRg, HFg, HPg, HSg, HRv, HFc, HRo, HMR.
  (* the state after the return, in MS form so that the `j` at 0x82ba0 can be stepped *)
  assert (Ems : ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp q0 q1 q2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
                     fp_regs (Z_to_bv 64 0x82ba0) fp_csr None (ms_mem ms) (seg_rom rsegs)).
  { destruct ms as [R' F' pcv' svc' rv' fc' m' ro']. cbn in HRg, HFg, HPg, HSg, HRv, HFc, HRo |- *. subst.
    replace (ret_pc (Z_to_bv 64 0x82ba0)) with (Z_to_bv 64 0x82ba0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  rewrite Ems. set (m' := ms_mem ms) in *. clear Ems HRg HFg HPg HSg HRv HFc HRo.
  step.
  apply ExecF.evtF_done.
  exists q0, q1, q2, b0, b1, b2, b3, b4, b5, b6, b7, q3, q4, q5, q6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' REL HMR Hro2 MU)|].
  split; [exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' REL HMR Hro2 WM)|].
  split; [exact (ro_agree_same rsegs mem m' HRO Hro2)|].
  split; [exact (stk_rel_hi_back m' m0' lo (bv_unsigned sp0) HMR Hlo0 Hsp64 ST')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) FLG')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) SHB')|].
  intros P HP.
  exact (A.ShadowRwOnT.shadow_rw_on_of_rel P m' m0' HMR (SW' P (A.ShadowRwOnT.shadow_rw_on_rel P mem _ REL HP))).
Qed.

Lemma y1_evt_of_F_on : SFO.asan_stack_free_6_contract_on ->
  forall (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (fr FS j lo spv : Z),
  a0w = Z_to_bv 64 fr -> a1w = Z_to_bv 64 3136 -> bv_unsigned sp0 = spv ->
  fr = fs_frame FS 6 j -> 0 <= j < fs_M 6 ->
  fs_place mem FS ->
  bytes_at rsegs mem (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs mem (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells mem -> A.ShadowRwOn.shadow_rw_on (SFO.asan_stack_free_shadow_R 6 3136 FS j) mem ->
  stk rsegs mem lo spv -> lo + 32 <= spv -> FS + FS_SIZE <= spv - 32 ->
  HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch
                   [(fs_flag FS 6 j, fs_flag FS 6 j + 1); (shadow_addr fr, shadow_addr fr + 512);
                    (spv - 32, spv)] mem m' /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       stk rsegs m' lo spv /\
       bytes_at rsegs m' (fs_flag FS 6 j) [Z_to_bv 8 0] /\
       bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) 512) /\
       (forall P, A.ShadowRwOn.shadow_rw_on P mem -> A.ShadowRwOn.shadow_rw_on P m'))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b9c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros HSF6 ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem fr FS j lo spv E0 E1 Esp EFR Hj PL FLG FLW HAC HSW HST
    HLOK HROOM HHI HSPA HRO.
  pose proof PL as (HFS0 & _ & _ & _ & _).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite EFR; unfold fs_frame, fs_B; cbn; lia).
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (Hj' : 0 <= j < 256) by (rewrite <- HM6; exact Hj).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr1 : fr < 2 ^ 64) by (unfold FS_SIZE, APPMEM_END in *; lia).
  eapply ExecF.evtF_evt. eapply y1_evt_F_on with (RNG := ExecF.RNG_all); try eassumption.
  - intros ? ? ? ? ?; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold FS_SIZE, APPMEM_END in *; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - exact (stack_free_6_F_on_all HSF6).
Qed.

(* ---- The release join 0x82b80 (YTail.v jrel_evt_real / jrel_evt_side): the header store `sd a0,0(s6)` writes
   [fr, fr + 8). *)
Lemma jrel_evt_real_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr SHv lo hi : Z),
  s3w = Z_to_bv 64 SHv -> s5w = Z_to_bv 64 0 -> s6w = Z_to_bv 64 fr ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  (* the header store 0x82b88 *)
  ExecF.rng RNG fr 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHv) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
                    s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82bac) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr SHv lo hi -> -> -> HRW HST RFR.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true) by apply bv_eqb_refl.
  step.
  ytailf_br true HB.
  step. step.
  apply ExecF.evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma jrel_evt_real_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr SHv lo hi : Z),
  s3w = Z_to_bv 64 SHv -> s5w = Z_to_bv 64 0 -> s6w = Z_to_bv 64 fr ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHv) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
                    s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82bac) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr SHv lo hi E3 E5 E6 HRW HST.
  pose proof (rw_cells_bound _ _ _ _ HRW) as HB. cbn [cells_size csize Nat.add] in HB.
  eapply ExecF.evtF_evt. eapply jrel_evt_real_F with (RNG := ExecF.RNG_all); try eassumption.
  apply ExecF.rng_all; lia.
Qed.

Lemma jrel_evt_side_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr lo hi : Z),
  s5w = Z_to_bv 64 fr -> s6w = Z_to_bv 64 fr -> 0 < fr < 2 ^ 64 ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  (* the header store 0x82b88 *)
  ExecF.rng RNG fr 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 3136) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82b9c) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr lo hi -> -> Hfr HRW HST RFR.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in E by lia. lia. }
  step.
  ytailf_br false HB.
  step. step. step.
  apply ExecF.evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma jrel_evt_side_of_F :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr lo hi : Z),
  s5w = Z_to_bv 64 fr -> s6w = Z_to_bv 64 fr -> 0 < fr < 2 ^ 64 ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 3136) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82b9c) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr lo hi E5 E6 Hfr HRW HST.
  pose proof (rw_cells_bound _ _ _ _ HRW) as HB. cbn [cells_size csize Nat.add] in HB.
  eapply ExecF.evtF_evt. eapply jrel_evt_side_F with (RNG := ExecF.RNG_all); try eassumption.
  apply ExecF.rng_all; lia.
Qed.

(* The pins of the Section's runs stay inside it: SYT.<r>'s type needs the same FPState instance. *)

Lemma y2_evt_of_F_verbatim : True.
Proof. let A := type of SYT.y2_evt in let B := type of y2_evt_of_F in constr_eq A B; exact I. Qed.

Lemma y2_evt_r_of_F_verbatim : True.
Proof. let A := type of SYT.y2_evt_r in let B := type of y2_evt_r_of_F in constr_eq A B; exact I. Qed.

Lemma y1_evt_of_F_verbatim : True.
Proof. let A := type of SYT.y1_evt in let B := type of y1_evt_of_F in constr_eq A B; exact I. Qed.

Lemma jrel_evt_real_of_F_verbatim : True.
Proof. let A := type of SYT.jrel_evt_real in let B := type of jrel_evt_real_of_F in constr_eq A B; exact I. Qed.

Lemma jrel_evt_side_of_F_verbatim : True.
Proof. let A := type of SYT.jrel_evt_side in let B := type of jrel_evt_side_of_F in constr_eq A B; exact I. Qed.

End Runs.

(* ---------------------------------------------------------------- the verbatim pin of the Y3 run *)

Lemma y3_evt_of_F_verbatim : True.
Proof. let A := type of SYT.y3_evt in let B := type of y3_evt_of_F in constr_eq A B; exact I. Qed.
