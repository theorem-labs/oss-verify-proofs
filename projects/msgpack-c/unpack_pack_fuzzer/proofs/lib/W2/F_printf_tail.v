(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aunmap F_adepot1 F_aintal F_irt.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import F_mmapordie F_embrealloc F_embappend.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation PR_STACK := 1280 (only parsing).

Ltac pr_pre := step; step; step; if_lit; step; step.

Ltac pr_post STK :=
  step; step;
  step; step; lstep; step; if_lit; step;
  step; step; step; step;
  carve_frame 48%nat STK;
  step; step; step; step; step;
  step; if_lit;
  step; step; step; step; step; step.

Section CANSEC2. Context {rc : runConstT}.

Definition printf_fit_post (RA : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo d cap sz len : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
    /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (sz + len))]
    /\ junk_at m' d cap.

Lemma printf_fit_tail : forall RNG (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo d cap sz : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv asegs m ->
  ro_cells asegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73470)] ->
  ro_cells asegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73420)] ->
  ro_cells asegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at asegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)] ->
  rw_cells asegs m 0x16b628 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0xd9348)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 <= sz -> sz + Z.of_nat (length str) <= cap ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap ->
  evtF asegs RNG (printf_fit_post RA sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d cap sz (Z.of_nat (length str)) m)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x73ae8) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC OLD DLO DHI SZ0 FIT RIMG RSTK ROLD.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split asegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  pose proof (munch_refl [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  pr_pre.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (emb_fit_spec RNG) with (lo := lo) (d := d) (cap := cap) (sz := sz) (TXT := bv_unsigned sp + -512) (str := str);
      [ rewrite USP; exact STL | exact CEIL | rewrite USP; clear -LO; lia | exact MI | reflexivity | exact TXTB | exact NOZ
      | rewrite USP; clear; lia | fold len; clear -SPHI LENR; lia | exact LEN | exact PTR | exact MTX | exact VEC | exact OLD
      | exact DLO | exact DHI | exact SZ0 | exact FIT | rewrite unsigned_lit by (clear; lia); clear; lia
      | exact RIMG | rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia | exact ROLD
      | fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia ]
    | post_call asegs mc ]
  end.
  rename PC into STC. rewrite USP in STC. destruct POST as [jk POST].
  pr_post STC.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge asegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. unfold printf_fit_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STF|]. split; [exact PC0|]. split; [exact PC1|].
  split; [exact PC2| exists jk; exact POST].
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition printf_first_post (RNG : footprint) (sp : word) (lo a len : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + 65536 <= ATOP
  /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
  /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 65536); C8 (Z_to_bv 64 len)]
  /\ junk_at m' a 65536
  /\ rng RNG' a 65536 /\ rng RNG' (shad a) (shlen 65536)
  /\ rmap_cells m'.

Lemma printf_first_tail : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv asegs m ->
  ro_cells asegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73470)] ->
  ro_cells asegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73420)] ->
  ro_cells asegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at asegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)] ->
  rw_cells asegs m 0x16b628 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall a, FRESH a = true -> 0 < a -> a + 65536 <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + 65536 <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      FRESH a = true -> printf_first_post RNG sp lo a (Z.of_nat (length str)) m RNG' m' ->
      rw_cells asegs m' 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)] -> rw_cells asegs m' 0x16b628 [C1 (Z_to_bv 8 0)] ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 65536 3 34) (adec_mmap ATOP 65536 3)) K) (epostF Q)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x73ae8) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split asegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  iprefix.
  pr_pre.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_first_spec RNG K Q FRESH) with (lo := lo) (TXT := bv_unsigned sp + -512) (str := str) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite USP; exact STL
       | |- mem_inv _ _ => exact MI
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- bytes_at _ _ _ _ => exact TXTB
       | |- Forall _ _ => exact NOZ
       | |- (_ <= length _ <= _)%nat => exact LEN
       | |- rw_cells _ _ _ _ => eassumption
       | |- rng _ _ (bv_unsigned _ - _) => rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia
       | |- rng _ _ _ => fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia
       end.
  all: try (rewrite ?USP; rewrite ?unsigned_lit by (clear; lia); fold len; clear -LO SPR CEIL SPHI LENR; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & STC & PTR2 & MTX2 & VEC2 & JNK & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as DLO.
  rewrite USP in MU2, STC.
  assert (MUA : munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  eapply ro_cells_frameD in SL0; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL1; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL2; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL3; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply cells_frameD in CBC; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply cells_frameD in CF64; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply stk_transportD in STU; [| exact MU2 | cbn [disjoint_from fst snd]; clear -SPR CEIL LO DLO A0 ACE; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2). destruct JNK as [jk JNK].
  rename MUA into MU. pose proof WM2 as WM. clear MU2 WM2 PTR MTX VEC TXTB MI GPG PGSZ GOT DPM MLIM STL.
  iprefix.
  replace (ret_pc (Z_to_bv 64 473852)) with (Z_to_bv 64 473852 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  pr_post STC.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge asegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. eapply KONT; [exact HFR| | assumption | assumption].
  unfold printf_first_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STF|]. split; [exact PTR2|]. split; [exact MTX2|].
  split; [exact VEC2|]. split; [exists jk; exact JNK|]. split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition printf_grow_post (RNG : footprint) (sp : word) (lo d0 cap0 sz len a ncap : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
  /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 (sz + len))]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma printf_grow_tail : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo d0 cap0 sz ncap : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv asegs m ->
  ro_cells asegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73470)] ->
  ro_cells asegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73420)] ->
  ro_cells asegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at asegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)] ->
  rw_cells asegs m 0x16b628 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0xd9348)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 d0); C8 (Z_to_bv 64 cap0); C8 (Z_to_bv 64 sz)] ->
  junk_at m d0 cap0 -> AIMG_HI <= d0 -> d0 + cap0 <= ATOP -> 0 < cap0 -> cap0 mod 4096 = 0 -> cap0 < 2^38 ->
  1 <= sz -> sz <= cap0 -> cap0 < sz + Z.of_nat (length str) ->
  ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d0 cap0 ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d0 \/ d0 + cap0 <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d0 cap0) (adec_munmap d0 cap0)) (K2 a)) ->
  (forall a RNG' m' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      FRESH a = true -> printf_grow_post RNG sp lo d0 cap0 sz (Z.of_nat (length str)) a ncap m RNG' m' ->
      rw_cells asegs m' 0x16b7d0 [C8 (Z_to_bv 64 0x60de8)] -> rw_cells asegs m' 0x16b628 [C1 (Z_to_bv 8 0)] ->
      implS asegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x73ae8) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC OLD D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT NCAP RIMG RSTK ROLD0 FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split asegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  iprefix.
  pr_pre.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_grow_spec RNG K K2 Q FRESH) with (lo := lo) (d0 := d0) (cap0 := cap0) (sz := sz) (TXT := bv_unsigned sp + -512) (str := str) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite USP; exact STL
       | |- mem_inv _ _ => exact MI
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- bytes_at _ _ _ _ => exact TXTB
       | |- Forall _ _ => exact NOZ
       | |- (_ <= length _ <= _)%nat => exact LEN
       | |- rw_cells _ _ _ _ => eassumption
       | |- junk_at _ _ _ => exact OLD
       | |- _ = _ / _ * _ => exact NCAP
       | |- rng _ _ (bv_unsigned _ - _) => rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia
       | |- rng _ _ _ => first [exact ROLD0 | fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia]
       end.
  all: try (unfold AIMG_HI; rewrite ?USP; rewrite ?unsigned_lit by (clear; lia); fold len; clear -LO SPR CEIL SPHI LENR D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  { exact SHAPE. }

  intros a RNG' m2 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HFR PO.
  destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & STC & PTR2 & MTX2 & VEC2 & JNK & RCH & RC2).
  destruct (FROK a HFR A0 ACE) as [DLO ADJ].
  rewrite USP in MU2, STC.
  assert (MUA : munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  eapply ro_cells_frameD in SL0; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL1; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL2; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL3; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in CBC; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in CF64; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply stk_transportD in STU; [| exact MU2 | cbn [disjoint_from fst snd]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2). destruct JNK as [jk JNK].
  rename MUA into MU. clear MU2 PTR MTX VEC TXTB MI GPG PGSZ GOT DPM MLIM STL OLD.
  iprefix.
  replace (ret_pc (Z_to_bv 64 473852)) with (Z_to_bv 64 473852 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  pr_post STC.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge asegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. eapply KONT; [exact HFR| | assumption | assumption].
  unfold printf_grow_post.
  split; [exact FPLE|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [assumption|]. split; [exact STF|]. split; [exact PTR2|]. split; [exact MTX2|].
  split; [exact VEC2|]. split; [exists jk; exact JNK|]. split; [exact RCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ABytes.TwinB AFrameD.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz. Import F_aunmap.TwinB F_adepot1.TwinB F_aintal.TwinB F_irt.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_mmapordie.TwinB F_embrealloc.TwinB F_embappend.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation PR_STACK := 1280 (only parsing).

Ltac pr_pre := step; step; step; if_lit; step; step.

Ltac pr_post STK :=
  step; step;
  step; step; lstep; step; if_lit; step;
  step; step; step; step;
  carve_frame 48%nat STK;
  step; step; step; step; step;
  step; if_lit;
  step; step; step; step; step; step.

Section CANSEC2. Context {rc : runConstT}.

Definition printf_fit_post (RA : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo d cap sz len : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
    /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (sz + len))]
    /\ junk_at m' d cap.

Lemma printf_fit_tail : forall RNG (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo d cap sz : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv bsegs m ->
  ro_cells bsegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73e00)] ->
  ro_cells bsegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73db0)] ->
  ro_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at bsegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0x16d990 [C8 (Z_to_bv 64 0x61778)] ->
  rw_cells bsegs m 0x16d7e8 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 <= sz -> sz + Z.of_nat (length str) <= cap ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap ->
  evtF bsegs RNG (printf_fit_post RA sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d cap sz (Z.of_nat (length str)) m)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x74478) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC OLD DLO DHI SZ0 FIT RIMG RSTK ROLD.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split bsegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  pose proof (munch_refl [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  pr_pre.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (emb_fit_spec RNG) with (lo := lo) (d := d) (cap := cap) (sz := sz) (TXT := bv_unsigned sp + -512) (str := str);
      [ rewrite USP; exact STL | exact CEIL | rewrite USP; clear -LO; lia | exact MI | reflexivity | exact TXTB | exact NOZ
      | rewrite USP; clear; lia | fold len; clear -SPHI LENR; lia | exact LEN | exact PTR | exact MTX | exact VEC | exact OLD
      | exact DLO | exact DHI | exact SZ0 | exact FIT | rewrite unsigned_lit by (clear; lia); clear; lia
      | exact RIMG | rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia | exact ROLD
      | fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia ]
    | post_call bsegs mc ]
  end.
  rename PC into STC. rewrite USP in STC. destruct POST as [jk POST].
  pr_post STC.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge bsegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. unfold printf_fit_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STF|]. split; [exact PC0|]. split; [exact PC1|].
  split; [exact PC2| exists jk; exact POST].
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition printf_first_post (RNG : footprint) (sp : word) (lo a len : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + 65536 <= ATOP
  /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
  /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 65536); C8 (Z_to_bv 64 len)]
  /\ junk_at m' a 65536
  /\ rng RNG' a 65536 /\ rng RNG' (shad a) (shlen 65536)
  /\ rmap_cells m'.

Lemma printf_first_tail : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv bsegs m ->
  ro_cells bsegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73e00)] ->
  ro_cells bsegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73db0)] ->
  ro_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at bsegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0x16d990 [C8 (Z_to_bv 64 0x61778)] ->
  rw_cells bsegs m 0x16d7e8 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall a, FRESH a = true -> 0 < a -> a + 65536 <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + 65536 <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      FRESH a = true -> printf_first_post RNG sp lo a (Z.of_nat (length str)) m RNG' m' ->
      rw_cells bsegs m' 0x16d990 [C8 (Z_to_bv 64 0x61778)] -> rw_cells bsegs m' 0x16d7e8 [C1 (Z_to_bv 8 0)] ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 65536 3 34) (adec_mmap ATOP 65536 3)) K) (epostF Q)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x74478) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split bsegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  iprefix.
  pr_pre.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_first_spec RNG K Q FRESH) with (lo := lo) (TXT := bv_unsigned sp + -512) (str := str) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite USP; exact STL
       | |- mem_inv _ _ => exact MI
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- bytes_at _ _ _ _ => exact TXTB
       | |- Forall _ _ => exact NOZ
       | |- (_ <= length _ <= _)%nat => exact LEN
       | |- rw_cells _ _ _ _ => eassumption
       | |- rng _ _ (bv_unsigned _ - _) => rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia
       | |- rng _ _ _ => fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia
       end.
  all: try (rewrite ?USP; rewrite ?unsigned_lit by (clear; lia); fold len; clear -LO SPR CEIL SPHI LENR; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & STC & PTR2 & MTX2 & VEC2 & JNK & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as DLO.
  rewrite USP in MU2, STC.
  assert (MUA : munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  eapply ro_cells_frameD in SL0; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL1; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL2; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply ro_cells_frameD in SL3; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply cells_frameD in CBC; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply cells_frameD in CF64; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE; lia].
  eapply stk_transportD in STU; [| exact MU2 | cbn [disjoint_from fst snd]; clear -SPR CEIL LO DLO A0 ACE; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2). destruct JNK as [jk JNK].
  rename MUA into MU. pose proof WM2 as WM. clear MU2 WM2 PTR MTX VEC TXTB MI GPG PGSZ GOT DPM MLIM STL.
  iprefix.
  replace (ret_pc (Z_to_bv 64 476300)) with (Z_to_bv 64 476300 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  pr_post STC.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge bsegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. eapply KONT; [exact HFR| | assumption | assumption].
  unfold printf_first_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STF|]. split; [exact PTR2|]. split; [exact MTX2|].
  split; [exact VEC2|]. split; [exists jk; exact JNK|]. split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition printf_grow_post (RNG : footprint) (sp : word) (lo d0 cap0 sz len a ncap : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m' /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
  /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 (sz + len))]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma printf_grow_tail : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    (RA FMT : Z) ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6'
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 va
    (F : bvmap 5 word) fc (m : amem) (lo d0 cap0 sz ncap : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PR_STACK -> bv_unsigned sp < 2^63 ->
  mem_inv bsegs m ->
  ro_cells bsegs m (bv_unsigned sp + -640) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m (bv_unsigned sp + -600)
     [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FMT); C8 va; C8 (Z_to_bv 64 0x73e00)] ->
  ro_cells bsegs m (bv_unsigned sp + -112) [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 0x73db0)] ->
  ro_cells bsegs m (bv_unsigned sp + -72) [C8 (Z_to_bv 64 RA)] ->
  bytes_at bsegs m (bv_unsigned sp + -512) (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0x16d990 [C8 (Z_to_bv 64 0x61778)] ->
  rw_cells bsegs m 0x16d7e8 [C1 (Z_to_bv 8 0)] ->
  rmap_cells m ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 d0); C8 (Z_to_bv 64 cap0); C8 (Z_to_bv 64 sz)] ->
  junk_at m d0 cap0 -> AIMG_HI <= d0 -> d0 + cap0 <= ATOP -> 0 < cap0 -> cap0 mod 4096 = 0 -> cap0 < 2^38 ->
  1 <= sz -> sz <= cap0 -> cap0 < sz + Z.of_nat (length str) ->
  ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d0 cap0 ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d0 \/ d0 + cap0 <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d0 cap0) (adec_munmap d0 cap0)) (K2 a)) ->
  (forall a RNG' m' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      FRESH a = true -> printf_grow_post RNG sp lo d0 cap0 sz (Z.of_nat (length str)) a ncap m RNG' m' ->
      rw_cells bsegs m' 0x16d990 [C8 (Z_to_bv 64 0x61778)] -> rw_cells bsegs m' 0x16d7e8 [C1 (Z_to_bv 8 0)] ->
      implS bsegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -640)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (bv_unsigned sp + -512)) s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x74478) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO SPHI MI SL0 SL1 SL2 SL3 TXTB NOZ LEN CBC CF64 RC PTR MTX VEC OLD D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT NCAP RIMG RSTK ROLD0 FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI in *. word_range sp SPR. pose proof atop_range as ATR.
  destruct (stk_split bsegs m lo (bv_unsigned sp + -640) (bv_unsigned sp) ST ltac:(clear -LO SPR; lia)) as [STL STU].
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -640)) = bv_unsigned sp + -640) by (apply unsigned_lit; clear -LO SPR CEIL ATR; lia).
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  iprefix.
  pr_pre.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_grow_spec RNG K K2 Q FRESH) with (lo := lo) (d0 := d0) (cap0 := cap0) (sz := sz) (TXT := bv_unsigned sp + -512) (str := str) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite USP; exact STL
       | |- mem_inv _ _ => exact MI
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- bytes_at _ _ _ _ => exact TXTB
       | |- Forall _ _ => exact NOZ
       | |- (_ <= length _ <= _)%nat => exact LEN
       | |- rw_cells _ _ _ _ => eassumption
       | |- junk_at _ _ _ => exact OLD
       | |- _ = _ / _ * _ => exact NCAP
       | |- rng _ _ (bv_unsigned _ - _) => rewrite USP; eapply rng_sub'; [exact RSTK|]; clear -LO SPR; lia
       | |- rng _ _ _ => first [exact ROLD0 | fold len; eapply rng_sub'; [exact RSTK|]; clear -LO SPR LENR CEIL; lia]
       end.
  all: try (unfold AIMG_HI; rewrite ?USP; rewrite ?unsigned_lit by (clear; lia); fold len; clear -LO SPR CEIL SPHI LENR D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  { exact SHAPE. }

  intros a RNG' m2 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HFR PO.
  destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & STC & PTR2 & MTX2 & VEC2 & JNK & RCH & RC2).
  destruct (FROK a HFR A0 ACE) as [DLO ADJ].
  rewrite USP in MU2, STC.
  assert (MUA : munch [(bv_unsigned sp - PR_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  eapply ro_cells_frameD in SL0; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL1; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL2; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply ro_cells_frameD in SL3; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in CBC; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in CF64; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply stk_transportD in STU; [| exact MU2 | cbn [disjoint_from fst snd]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2). destruct JNK as [jk JNK].
  rename MUA into MU. clear MU2 PTR MTX VEC TXTB MI GPG PGSZ GOT DPM MLIM STL OLD.
  iprefix.
  replace (ret_pc (Z_to_bv 64 476300)) with (Z_to_bv 64 476300 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  pr_post STC.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -688) _ |- _ => release_frame FRM STC (bv_unsigned sp + -640) end.
  do 11 step. step. step.
  do 4 step. step. step.
  step. step. step.
  pose proof (stk_merge bsegs _ lo (bv_unsigned sp + -640) (bv_unsigned sp) STC STU ltac:(clear -LO SPR; lia)) as STF.
  apply evtF_done. eapply KONT; [exact HFR| | assumption | assumption].
  unfold printf_grow_post.
  split; [exact FPLE|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [assumption|]. split; [exact STF|]. split; [exact PTR2|]. split; [exact MTX2|].
  split; [exact VEC2|]. split; [exists jk; exact JNK|]. split; [exact RCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.
End TwinB.
