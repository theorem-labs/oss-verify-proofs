(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v; 422 of its 634 lines of code are new or changed and 990 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P5.v blob 30d4e20a1163 at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives P5.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of P5.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/P5.v's two run lemmas (p5_memset_ro :310, p5_evt :376, the lines of
   S_P5 (segment-runs-A.tsv (a working note, not in this delivery))).
   - p5_memset_ro_F: P5.p5_memset_ro, the memset call alone on the memory the cut carries (ro_agree, not
     mem_inv): the footprint contract asan_memset_contract_F (lib/A/Prog/asan_memset_cF.v, proved by a Theorem Labs lane as
     asan_memset_holds_F in lib/A/Prog/asan_memsetF.v) on the normalized memory, moved back by
     MemNormF.evtF_normalize_ro, exactly as P5.p5_memset_ro uses MemNorm.evt_normalize.  The run steps no
     instruction of its own, so its footprint premises are the callee contract's own, passed through unchanged at
     this call site (bv_unsigned a0, bv_unsigned a2, bv_unsigned sp).  rng_bytes RNG is a forall-memory form and
     is passed through unchanged.
   - p5_evt_F: P5.p5_evt (0x81b90 -> 0x81bd4), the nine one-byte stores, the two spill loads and the memset call.
     The segment's own accesses, all named by the lemma's own premises: the frame-shadow window
     [S + 370, S + 386) (the stores at S+370 / +372 / +376 / +380 and S+382..385, inside the 392 frame-shadow
     bytes of `rw_cells rsegs m S [CB 392 sh]`), the spill loads [A + 280, A + 288) and [A + 240, A + 248)
     (`ro_cells` premises) and the one code byte [Y, Y + 1) (`rw_cells rsegs m Y [CB 1 jy]`): four rng premises.
     The call's regions follow, through p5_memset_ro_F, at this call site (D, 32, spv).
   P5.v's code is unchanged since release c5e779efe8c (comments edited); it differs from the source blob above: 5 of its code lines changed or removed, 182 added. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c asan_memset_cF.
(* route (C) (p5_memset_ro_F_on / p5_evt_F_on and their RNG_all twins): the memset's region-restricted footprint
   contract (a Theorem Labs lane 83ab88c3325, taken by path) and the form (lib/A/ShadowRwOn.v, ShadowRwOnT.v; a Theorem Labs lane
   9ec78006def); P5.p5_shadow_rw_on is a Theorem Labs lane's (Seg/P5.v f227e521dc4, taken by path). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c_on asan_memset_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require P5.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* P5.p5_sb with the evtF goal shape (the one helper the template shows must change: StepF's mem_after_store
   closes an evtF store goal where Step's closes an evt one). *)
Ltac p5F_sb :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (P5.p5_le1 z); mem_after_store
  | _ => idtac
  end.

(* ---- p5_memset_ro (P5.v:310) under a footprint RNG. ---- *)
Lemma p5_memset_ro_F : asan_memset_contract_F ->
  forall (RNG : ExecF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
  (* the callee's regions (asan_memset_contract_F's rng premises at this call site), unchanged *)
  rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExecF.rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  sh_word_rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  sh_word_rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO
    Gby Gimg Gstk Gd Gshd Gshs.
  unfold asan_memset_contract_F in MSET. cbv zeta in MSET.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  eapply ExecF.evtF_mono.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) junk lo).
    + exact (P5.p5_rw_rel m _ _ _ REL HD0 RWd).
    + exact HN.
    + exact (P5.p5_addressable_rel m _ _ _ REL HAD).
    + exact HEND.
    + exact HD7.
    + exact HDRT.
    + exact HSEP.
    + exact (P5.p5_stk_rel m _ lo (bv_unsigned sp) REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (P5.p5_cells_rel m _ REL HAC).
    + exact (P5.p5_shadow_rw_rel m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
    + exact Gby.
    + exact Gimg.
    + exact Gstk.
    + exact Gd.
    + exact Gshd.
    + exact Gshs.
  - intros s (s0' & HQ & MR & RS). unfold asan_memset_post in HQ.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    -> & MU0 & WM0 & _ & ST0 & RW0 & _ & _).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', ms.
    split; [reflexivity|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (P5.p5_stk_back ms m0' lo (bv_unsigned sp) Hmem ltac:(lia) ltac:(lia) ST0)|].
    eexists. exact (P5.p5_rw_back ms m0' _ _ Hmem RW0).
Qed.

(* P5.p5_memset_ro's conclusion under the footprint contract: p5_memset_ro_F at ExecF.RNG_all. *)
Lemma p5_memset_ro_of_F : asan_memset_contract_F ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
  evt rsegs
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof HAD as (HAD0 & HAD1 & HAD2 & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p5_memset_ro_F MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO).
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - unfold APPMEM_END in HAD2. apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

Example p5_memset_ro_of_F_verbatim : True.
Proof.
  lazymatch type of P5.p5_memset_ro with ?P -> ?A =>
    constr_eq P asan_memset_contract;
    lazymatch type of p5_memset_ro_of_F with ?Q -> ?B =>
      constr_eq Q asan_memset_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

(* ---- p5_evt (P5.v:376) under a footprint RNG. ---- *)
Lemma p5_evt_F : asan_memset_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    (* the segment's own accesses: the frame-shadow window the nine stores write, the two spill loads and the
       one code byte the store at 0x81bac writes *)
    ExecF.rng RNG (S + 370) 16 ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.rng RNG (A + 240) 8 ->
    ExecF.rng RNG Y 1 ->
    (* the callee's regions (asan_memset_contract_F's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG D 32 ->
    sh_word_rng RNG D 32 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk -> -> -> HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO
    Gsh Ga280 Ga240 Gy Gby Gimg Gstk Gd Gshd Gshs.
  pose proof (munch_refl [(S + 370, S + 386); (Y, Y + 1)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM1.
  (* li a0,2 ; li a1,1 ; sb a0,370(s3) ; sb zero,372(s3) ; sb zero,376(s3) ; sb a1,380(s3) *)
  step. step. step. p5F_sb.
  step. p5F_sb. step. p5F_sb. step. p5F_sb.
  (* li a0,-18 ; ld a1,280(s1) ; sb a0,0(a1) *)
  step. step. step. p5F_sb.
  (* sb zero,382..385(s3) *)
  step. p5F_sb. step. p5F_sb. step. p5F_sb. step. p5F_sb.
  (* li a2,32 ; ld s5,240(s1) ; mv a0,s5 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  (* the memset call's premises in the memory after the stores *)
  assert (Z0 : forall j, 0 <= j < 4 -> mrd rsegs m1 (wa (S + 382 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj' as [-> | [-> | [-> | ->]]].
    - replace (S + 382 + 0) with (S + Z.of_nat 382) by lia.
      apply (P5.p5_cells_read1 m1 S _ 382 _ RWsh). reflexivity.
    - replace (S + 382 + 1) with (S + Z.of_nat 383) by lia.
      apply (P5.p5_cells_read1 m1 S _ 383 _ RWsh). reflexivity.
    - replace (S + 382 + 2) with (S + Z.of_nat 384) by lia.
      apply (P5.p5_cells_read1 m1 S _ 384 _ RWsh). reflexivity.
    - replace (S + 382 + 3) with (S + Z.of_nat 385) by lia.
      apply (P5.p5_cells_read1 m1 S _ 385 _ RWsh). reflexivity. }
  assert (H380 : mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1)).
  { replace (S + 380) with (S + Z.of_nat 380) by lia.
    apply (P5.p5_cells_read1 m1 S _ 380 _ RWsh). reflexivity. }
  assert (HYp : exists b, mrd rsegs m1 (wa Y) = Some b).
  { replace (wa Y) with (wa (Y + Z.of_nat 0)) by (f_equal; lia).
    eexists. apply (P5.p5_cells_read1 m1 Y _ 0 _ RWy). reflexivity. }
  assert (HAD : addressable m1 D 32)
    by (apply (P5.p5_addr32 m1 D (S + 382)); [lia | exact HD8 | exact HDS | exact HappD | exact Z0]).
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI in *. lia. }
  pose proof (P5.p5_cells_bytes _ _ _ RWsh) as (HBsh & HLsh). cbn [cells_size csize Nat.add] in HLsh.
  assert (HSW1 : shadow_rw m1).
  { apply (P5.p5_shadow_rw m m1 S Y _ HSW MU1 WM1 HBsh HLsh). intro HYs. exact (app_not_shadow Y HappY HYs). }
  (* the stores write nothing below 0x5fe000, so the read-only image bytes are kept *)
  assert (HRO1 : MemNorm.ro_agree rsegs m1).
  { apply (MemNorm.ro_agree_same rsegs m m1 HRO). intros a Ha. apply MU1.
    pose proof (P5.p5_ro_lo a Ha) as Hlo. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  eapply ExecF.evtF_cut.
  { eapply (p5_memset_ro_F MSET RNG) with (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. apply HappD.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. apply HappD.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSEP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HAC1.
    - exact HSW1.
    - exact HRO1.
    - exact Gby.
    - exact Gimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & ROc & STc & (zs & RWc)).
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E32 in MUc, RWc. rewrite Esp in MUc, STc.
  replace (ret_pc (Z_to_bv 64 0x81bd8)) with (Z_to_bv 64 0x81bd8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done. eexists. exists m1, m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact HRO1|].
  split; [eexists; split; [exact HBsh | exact HLsh]|].
  split; [exact H380|]. split; [exact HYp|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|].
  split; [exact STc | eexists; exact RWc].
Qed.

(* P5.p5_evt's conclusion under the footprint contract: p5_evt_F at ExecF.RNG_all. *)
Lemma p5_evt_of_F : asan_memset_contract_F ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk E1 E2 E3 HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (ro_cells_bound rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] RO280) as HB280.
  pose proof (ro_cells_bound rsegs m (A + 240) [C8 (Z_to_bv 64 D)] RO240) as HB240.
  pose proof (rw_cells_bound rsegs m S [CB 392 sh] RWsh) as HBsh.
  pose proof (rw_cells_bound rsegs m Y [CB 1 jy] RWy) as HBy.
  pose proof (rw_cells_bound rsegs m D [CB 32 junk] RWd) as HBd.
  cbn [cells_size csize Nat.add] in HB280, HB240, HBsh, HBy, HBd.
  assert (HDapp : app_mem (D + 32)) by (apply HappD; lia).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HDapp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p5_evt_F MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m spv A S Y D lo sh jy junk E1 E2 E3 HA HSP HD RO280 RO240 RWsh RWy RWd
           HSA HYD HSY HYA HRTS HRTY HappY HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG in *; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

Example p5_evt_of_F_verbatim : True.
Proof.
  lazymatch type of P5.p5_evt with ?P -> ?A =>
    constr_eq P asan_memset_contract;
    lazymatch type of p5_evt_of_F with ?Q -> ?B =>
      constr_eq Q asan_memset_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery), 10:34Z amendment): ADDITIVE twins
   of p5_memset_ro_F, p5_memset_ro_of_F, p5_evt_F and p5_evt_of_F.  The four old lemmas stay byte-identical with their
   own proofs (a Theorem Labs lane 09:58Z: a run that takes a callee contract keeps X); the twins take the memset's region-restricted
   footprint contract asan_memset_contract_F_on.  Neither run's post states shadow_rw, so only the premise changes. ----
   R of p5_memset_ro_F: the run steps no instruction of its own (no shadow read or store); its shadow premise HSW
   has one use, the memset's premise across normalize (`P5.p5_shadow_rw_rel m _ REL HSW`, here
   ShadowRwOnT.shadow_rw_on_rel). So R is the memset's own region at the call's a0 / a2: asan_memset_shadow_R a0 a2
   (memset reads the shadow words of [a0, a0 + a2) and stores no shadow byte, asan_memset_c_on.v). *)
Definition p5_memset_ro_F_shadow_R (a0 a2 : word) : Z -> Prop := fun a => asan_memset_shadow_R a0 a2 a.

Lemma p5_memset_ro_F_on : asan_memset_contract_F_on ->
  forall (RNG : ExecF.footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_memset_ro_F_shadow_R a0 a2) m -> MemNorm.ro_agree rsegs m ->
  (* the callee's regions (asan_memset_contract_F_on's rng premises at this call site), unchanged *)
  rng_bytes RNG ->
  ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  ExecF.rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExecF.rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  sh_word_rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  sh_word_rng RNG (bv_unsigned sp - ASAN_MEMSET_K) ASAN_MEMSET_K ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO
    Gby Gimg Gstk Gd Gshd Gshs.
  unfold asan_memset_contract_F_on in MSET. cbv zeta in MSET.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  eapply ExecF.evtF_mono.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    apply (MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) junk lo).
    + exact (P5.p5_rw_rel m _ _ _ REL HD0 RWd).
    + exact HN.
    + exact (P5.p5_addressable_rel m _ _ _ REL HAD).
    + exact HEND.
    + exact HD7.
    + exact HDRT.
    + exact HSEP.
    + exact (P5.p5_stk_rel m _ lo (bv_unsigned sp) REL ltac:(lia) ltac:(lia) ST).
    + exact HLO.
    + exact HHM.
    + exact HAE.
    + exact (P5.p5_cells_rel m _ REL HAC).
    + exact (A.ShadowRwOnT.shadow_rw_on_rel _ m _ REL HSW).
    + exact (MemNorm.mem_inv_normalize rsegs m).
    + exact Gby.
    + exact Gimg.
    + exact Gstk.
    + exact Gd.
    + exact Gshd.
    + exact Gshs.
  - intros s (s0' & HQ & MR & RS). unfold asan_memset_post_on in HQ.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    -> & MU0 & WM0 & _ & ST0 & RW0 & _ & _).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', ms.
    split; [reflexivity|].
    split; [exact (MemNorm.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MemNorm.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MemNorm.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (P5.p5_stk_back ms m0' lo (bv_unsigned sp) Hmem ltac:(lia) ltac:(lia) ST0)|].
    eexists. exact (P5.p5_rw_back ms m0' _ _ Hmem RW0).
Qed.

(* p5_memset_ro_of_F's twin: p5_memset_ro_F_on at ExecF.RNG_all, the region-restricted footprint contract kept as
   the hypothesis (as p5_memset_ro_of_F keeps asan_memset_contract_F). R: p5_memset_ro_F_on's. No pin. *)
Lemma p5_memset_ro_of_F_on : asan_memset_contract_F_on ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z),
  0x5fe000 <= bv_unsigned a0 ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  bv_unsigned a2 <= 2 ^ 40 -> addressable m (bv_unsigned a0) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) ->
  (bv_unsigned a0 + bv_unsigned a2 <= RT_LO \/ RT_HI <= bv_unsigned a0) ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - ASAN_MEMSET_K \/ bv_unsigned sp <= bv_unsigned a0) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMSET_K <= bv_unsigned sp ->
  HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_memset_ro_F_shadow_R a0 a2) m -> MemNorm.ro_agree rsegs m ->
  evt rsegs
    (fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2);
              (bv_unsigned sp - ASAN_MEMSET_K, bv_unsigned sp)] m m' /\
       wmono rsegs m m' /\ MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
       (exists zs, rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) zs]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof HAD as (HAD0 & HAD1 & HAD2 & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p5_memset_ro_F_on MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m junk lo HD0 RWd HN HAD HEND HD7 HDRT HSEP ST HLO HHM HAE HAC HSW HRO).
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - unfold APPMEM_END in HAD2. apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

(* R of p5_evt_F: the run reads no shadow byte; its nine one-byte stores into the frame shadow [S + 370, S + 386)
   (0x81b98 .. 0x81bc0) go through the rw_cells premise of the 392 frame-shadow bytes and its store at Y through
   `rw_cells rsegs m Y [CB 1 jy]`, not through shadow_rw. Its shadow premise HSW has one use: the memset's premise
   at the call (a0 = D from the spill load ld s5,240(s1); a2 = 32 from li a2,32), carried across the stores by
   P5.p5_shadow_rw (here a Theorem Labs lane's P5.p5_shadow_rw_on, forall P). So R is the callee p5_memset_ro_F_on's region at the
   call's arguments. The same region as P5.v's plain twin (p5_evt_shadow_R D, a Theorem Labs lane f227e521dc4). *)
Definition p5_evt_F_shadow_R (D : Z) : Z -> Prop :=
  fun a => p5_memset_ro_F_shadow_R (Z_to_bv 64 D) (Z_to_bv 64 32) a.

Lemma p5_evt_F_on : asan_memset_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_evt_F_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    (* the segment's own accesses: the frame-shadow window the nine stores write, the two spill loads and the
       one code byte the store at 0x81bac writes *)
    ExecF.rng RNG (S + 370) 16 ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.rng RNG (A + 240) 8 ->
    ExecF.rng RNG Y 1 ->
    (* the callee's regions (asan_memset_contract_F_on's rng premises at this call site), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.rng RNG D 32 ->
    sh_word_rng RNG D 32 ->
    sh_word_rng RNG (spv - ASAN_MEMSET_K) ASAN_MEMSET_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk -> -> -> HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO
    Gsh Ga280 Ga240 Gy Gby Gimg Gstk Gd Gshd Gshs.
  pose proof (munch_refl [(S + 370, S + 386); (Y, Y + 1)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM1.
  (* li a0,2 ; li a1,1 ; sb a0,370(s3) ; sb zero,372(s3) ; sb zero,376(s3) ; sb a1,380(s3) *)
  step. step. step. p5F_sb.
  step. p5F_sb. step. p5F_sb. step. p5F_sb.
  (* li a0,-18 ; ld a1,280(s1) ; sb a0,0(a1) *)
  step. step. step. p5F_sb.
  (* sb zero,382..385(s3) *)
  step. p5F_sb. step. p5F_sb. step. p5F_sb. step. p5F_sb.
  (* li a2,32 ; ld s5,240(s1) ; mv a0,s5 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  (* the memset call's premises in the memory after the stores *)
  assert (Z0 : forall j, 0 <= j < 4 -> mrd rsegs m1 (wa (S + 382 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj' as [-> | [-> | [-> | ->]]].
    - replace (S + 382 + 0) with (S + Z.of_nat 382) by lia.
      apply (P5.p5_cells_read1 m1 S _ 382 _ RWsh). reflexivity.
    - replace (S + 382 + 1) with (S + Z.of_nat 383) by lia.
      apply (P5.p5_cells_read1 m1 S _ 383 _ RWsh). reflexivity.
    - replace (S + 382 + 2) with (S + Z.of_nat 384) by lia.
      apply (P5.p5_cells_read1 m1 S _ 384 _ RWsh). reflexivity.
    - replace (S + 382 + 3) with (S + Z.of_nat 385) by lia.
      apply (P5.p5_cells_read1 m1 S _ 385 _ RWsh). reflexivity. }
  assert (H380 : mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1)).
  { replace (S + 380) with (S + Z.of_nat 380) by lia.
    apply (P5.p5_cells_read1 m1 S _ 380 _ RWsh). reflexivity. }
  assert (HYp : exists b, mrd rsegs m1 (wa Y) = Some b).
  { replace (wa Y) with (wa (Y + Z.of_nat 0)) by (f_equal; lia).
    eexists. apply (P5.p5_cells_read1 m1 Y _ 0 _ RWy). reflexivity. }
  assert (HAD : addressable m1 D 32)
    by (apply (P5.p5_addr32 m1 D (S + 382)); [lia | exact HD8 | exact HDS | exact HappD | exact Z0]).
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI in *. lia. }
  pose proof (P5.p5_cells_bytes _ _ _ RWsh) as (HBsh & HLsh). cbn [cells_size csize Nat.add] in HLsh.
  (* every region across the stores (a Theorem Labs lane's P5.p5_shadow_rw_on), at R *)
  assert (HSW1 : A.ShadowRwOn.shadow_rw_on (p5_evt_F_shadow_R D) m1).
  { apply (P5.p5_shadow_rw_on m m1 S Y _ MU1 WM1 HBsh HLsh); [|exact HSW].
    intro HYs. exact (app_not_shadow Y HappY HYs). }
  (* the stores write nothing below 0x5fe000, so the read-only image bytes are kept *)
  assert (HRO1 : MemNorm.ro_agree rsegs m1).
  { apply (MemNorm.ro_agree_same rsegs m m1 HRO). intros a Ha. apply MU1.
    pose proof (P5.p5_ro_lo a Ha) as Hlo. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  eapply ExecF.evtF_cut.
  { eapply (p5_memset_ro_F_on MSET RNG) with (junk := junk) (lo := lo).
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact RWd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAD.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. apply HappD.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. apply HappD.
      lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. right. lia.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HSEP.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact ST.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HLO.
    - exact HHM.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact HAE.
    - exact HAC1.
    - (* the memset's region at the call's a0 = D, a2 = 32 is p5_evt_F_shadow_R D *)
      exact HSW1.
    - exact HRO1.
    - exact Gby.
    - exact Gimg.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gstk.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshd.
    - rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. exact Gshs. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & ROc & STc & (zs & RWc)).
  subst ms'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (E32 : bv_unsigned (Z_to_bv 64 32) = 32) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  rewrite ED in MUc, RWc. rewrite E32 in MUc, RWc. rewrite Esp in MUc, STc.
  replace (ret_pc (Z_to_bv 64 0x81bd8)) with (Z_to_bv 64 0x81bd8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done. eexists. exists m1, m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact HRO1|].
  split; [eexists; split; [exact HBsh | exact HLsh]|].
  split; [exact H380|]. split; [exact HYp|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact ROc|].
  split; [exact STc | eexists; exact RWc].
Qed.

(* p5_evt_of_F's twin: p5_evt_F_on at ExecF.RNG_all, the region-restricted footprint contract kept as the
   hypothesis (as p5_evt_of_F keeps asan_memset_contract_F). R: p5_evt_F_on's. No pin. *)
Lemma p5_evt_of_F_on : asan_memset_contract_F_on ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A S Y D lo : Z) (sh jy junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 S ->
    0 <= A < 2 ^ 64 -> 0 <= spv < 2 ^ 64 -> 0 <= D < 2 ^ 64 ->
    ro_cells rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] ->
    ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m S [CB 392 sh] ->
    rw_cells rsegs m Y [CB 1 jy] ->
    rw_cells rsegs m D [CB 32 junk] ->
    S + 392 <= A -> Y + 1 <= D -> (S + 392 <= Y \/ D + 32 <= S) -> (Y + 1 <= A + 240 \/ A + 288 <= Y) ->
    RT_HI <= S -> RT_HI <= Y -> app_mem Y -> 0x5fe000 <= S -> 0x5fe000 <= Y ->
    D mod 8 = 0 -> D / 8 + ASAN_K = S + 382 -> app_ivl D (D + 33) ->
    (D + 32 <= spv - ASAN_MEMSET_K \/ spv <= D) ->
    stk rsegs m lo spv -> lo + ASAN_MEMSET_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (p5_evt_F_shadow_R D) m -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81bd8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 26 = s10 /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch [(S + 370, S + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\ MemNorm.ro_agree rsegs m1 /\
         (exists sh', bytes_at rsegs m1 S sh' /\ length sh' = 392%nat) /\
         mrd rsegs m1 (wa (S + 380)) = Some (Z_to_bv 8 1) /\ (exists b, mrd rsegs m1 (wa Y) = Some b) /\
         munch [(D, D + 32); (spv - ASAN_MEMSET_K, spv)] m1 m' /\ wmono rsegs m1 m' /\
         MemNorm.ro_agree rsegs m' /\ stk rsegs m' lo spv /\ (exists zs, rw_cells rsegs m' D [CB 32 zs]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b90) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A S Y D lo sh jy junk E1 E2 E3 HA HSP HD RO280 RO240 RWsh RWy RWd HSA HYD HSY HYA HRTS HRTY HappY
    HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO.
  pose proof (ro_cells_bound rsegs m (A + 280) [C8 (Z_to_bv 64 Y)] RO280) as HB280.
  pose proof (ro_cells_bound rsegs m (A + 240) [C8 (Z_to_bv 64 D)] RO240) as HB240.
  pose proof (rw_cells_bound rsegs m S [CB 392 sh] RWsh) as HBsh.
  pose proof (rw_cells_bound rsegs m Y [CB 1 jy] RWy) as HBy.
  pose proof (rw_cells_bound rsegs m D [CB 32 junk] RWd) as HBd.
  cbn [cells_size csize Nat.add] in HB280, HB240, HBsh, HBy, HBd.
  assert (HDapp : app_mem (D + 32)) by (apply HappD; lia).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HDapp.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (p5_evt_F_on MSET ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 F fc m spv A S Y D lo sh jy junk E1 E2 E3 HA HSP HD RO280 RO240 RWsh RWy RWd
           HSA HYD HSY HYA HRTS HRTY HappY HS0 HY0 HD8 HDS HappD HSEP ST HLO HHM HAE HAC HSW HRO).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG in *; lia.
  - apply ExecF.rng_all; lia.
  - apply sh_word_rng_all; unfold APPMEM_END in *; lia.
  - apply sh_word_rng_all; unfold ASAN_MEMSET_K, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.
