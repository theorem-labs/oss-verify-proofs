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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aunmap F_adepot1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import F_mmapordie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EMBR_STACK := 352 (only parsing).
Notation EMBV := 0xd9348 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition emb_realloc_entry := 0x64cd8.

Definition realloc0_post (RNG : footprint) (sp : word) (a ncap lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (a, a + ncap)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' EMBV [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' a [CB (Z.to_nat ncap) (repeat (Z_to_bv 8 0) (Z.to_nat ncap))]
  /\ rng RNG' a ncap /\ rng RNG' (shad a) (shlen ncap)
  /\ rmap_cells m'.

Lemma emb_realloc0_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (want ncap lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBR_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 EMBV -> a1 = Z_to_bv 64 want -> 0 < want -> want < 2^39 -> ncap = (want + 4095) / 4096 * 4096 ->
  rw_cells asegs m EMBV [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> realloc0_post RNG sp a ncap lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_realloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> WPOS WHI NCAP VEC RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_realloc_entry in *. word_range sp SPR. atop_facts.
  assert (NC : ncap mod 4096 = 0 /\ want <= ncap /\ ncap < want + 4096) by (rewrite NCAP; clear -WPOS; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  pose proof (munch_refl [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 WPOS WHI. lia. }
  step. step.
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 WPOS WHI. lia. }
  step. step. step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 ncap) ltac:(rewrite land_align4096 by lia; f_equal; rewrite NCAP; clear -WPOS WHI; Z.div_mod_to_equations; lia).
  step. step. step. step.
  step.

  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapordie_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => exact NCM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO NCL NCH WPOS WHI; lia).
  {
    intros a HFR A0 ACE. pose proof (FROK a HFR A0 ACE) as AH. rewrite unsigned_lit by (clear -SPR CEIL LO; lia). unfold AIMG_HI. clear -AH ACE CEIL LO SPR. lia. }
  {
    intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as AHI.
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (a, a + ncap)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport VEC MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2.
  iprefix.
  replace (ret_pc (Z_to_bv 64 413000)) with (Z_to_bv 64 413000 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step.
  step.
  step. if_lit.
  step.
  step. step. step.
  step.
  carve_frame 48%nat ST2.
  step. step. step. step. step.
  step. if_lit.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -80) _ |- _ => release_frame FRM ST2 (bv_unsigned sp + -32) end.
  step. step.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _ |- _ => release_frame FRM ST2 (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold realloc0_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MUA|]. split; [exact WMA|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact VEC|]. split; [exact ZCH|]. split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition realloc1_post (RNG : footprint) (sp : word) (d cap sz a ncap lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' EMBV [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 sz)]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma emb_realloc1_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (d cap sz want ncap lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBR_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 EMBV -> a1 = Z_to_bv 64 want -> want < 2^39 -> ncap = (want + 4095) / 4096 * 4096 ->
  rw_cells asegs m EMBV [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 < cap -> cap mod 4096 = 0 -> 1 <= sz -> sz <= cap -> sz <= want ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d \/ d + cap <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d cap) (adec_munmap d cap)) (K2 a)) ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> realloc1_post RNG sp d cap sz a ncap lo m RNG' m' ->
      implS asegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_realloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> WHI NCAP VEC OLD DLO DHI CPOS CAL SZ1 SZC SZW RC RIMG RSTK ROLD FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_realloc_entry in *. word_range sp SPR. atop_facts.
  assert (NC : ncap mod 4096 = 0 /\ want <= ncap /\ ncap < want + 4096) by (rewrite NCAP; clear -SZ1 SZW; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  destruct OLD as [junk OLD].
  pose proof (munch_refl [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 SZ1 SZW WHI. lia. }
  step. step.
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SZ1 SZW WHI. lia. }
  step. step. step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 ncap) ltac:(rewrite land_align4096 by lia; f_equal; rewrite NCAP; clear -SZ1 SZW WHI; Z.div_mod_to_equations; lia).
  step. step. step. step.
  step.

  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapordie_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => exact NCM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO NCL NCH SZ1 SZW WHI; lia).
  { intros a HFR A0 ACE. destruct (FROK a HFR A0 ACE) as [AH _]. rewrite unsigned_lit by (clear -SPR CEIL LO; lia). unfold AIMG_HI. clear -AH ACE CEIL LO SPR. lia. }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
  destruct (FROK a HFR A0 ACE) as [AHI ADJ].
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport VEC MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport OLD MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE ADJ DLO DHI CPOS; lia).
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in ROLD.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2.

  set (SRC := firstn (Z.to_nat sz) junk).
  assert (LJ : length junk = Z.to_nat cap) by (destruct OLD as [[[WF _] _] _]; exact WF).
  assert (LSRC : length SRC = Z.to_nat sz) by (unfold SRC; rewrite firstn_length, LJ; clear -SZ1 SZC; lia).
  assert (TB : bytes_at asegs m2 d (SRC ++ skipn (Z.to_nat sz) junk)).
  { unfold SRC. rewrite firstn_skipn. destruct OLD as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
  change (rw_cells asegs m2 a [CB (Z.to_nat ncap) (repeat (Z_to_bv 8 0) (Z.to_nat ncap))]) with (fill_at m2 a ncap 0) in ZCH.
  destruct (fill_split m2 a sz (ncap - sz) 0 ltac:(replace (sz + (ncap - sz)) with ncap by (clear; lia); exact ZCH) ltac:(clear -SZ1; lia) ltac:(clear -SZW NCL; lia)) as [DZ1 DZ2].
  unfold fill_at in DZ1, DZ2. rewrite <- LSRC in DZ1.
  iprefix.
  replace (ret_pc (Z_to_bv 64 413000)) with (Z_to_bv 64 413000 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (imemcpy_specZ RNG') with (src := SRC) (rest := skipn (Z.to_nat sz) junk) (junk := repeat (Z_to_bv 8 0) (length SRC));
      [ eassumption | exact TB | exact DZ1
      | rewrite LSRC; clear -SZ1; lia
      | rewrite length_app, skipn_length, LJ, LSRC; clear -ADJ SZ1 SZC SZW NCL CPOS; lia
      | pose proof atop_range as ATR; clear -ACE SZW NCL ATR A0 SZ1; lia
      | pose proof atop_range as ATR; rewrite length_app, skipn_length, LJ, LSRC; clear -DHI SZ1 SZC CPOS ATR DLO; lia
      | clear -SZ1; lia
      | eapply rng_sub'; [exact ROLD|]; clear -SZ1 SZC; lia
      | eapply rng_sub'; [exact RCH|]; clear -SZ1 SZW NCL; lia ]
    | post_call asegs mc ]
  end.
  step. step. step.
  step.

  apply evtF_done. rewrite (SHAPE a HFR).
  assert (GOTH : rw_cells asegs x3 0xd1508 [C8 (Z_to_bv 64 0x16b5e8)]).
  { apply (proj1 (rw_cells_app asegs x3 0xd1508 [C8 (Z_to_bv 64 0x16b5e8)] _)) in GOT2 as [G _]. exact G. }
  eapply (unmap_or_die_spec RNG' (K2 a) Q) with (addr := d) (size := cap) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST2
       | |- mem_inv _ _ => exact MI0
       | |- @eq word _ _ => reflexivity
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       | |- unmap_cells _ => split; [exact GOTH| exact MLIM2]
       | |- forall _, _ => idtac
       | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO DLO DHI CPOS CAL; lia
       end.

  intros rsp RNG3 m3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' HF MUu MIu STu UCu.
  rewrite unsigned_lit in MUu, STu by (clear -SPR CEIL LO; lia).
  destruct HF as [_ FPLE3]. cbn beta iota in FPLE3.
  assert (MUB : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m3).
  { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  Ltac fD H MUu tac := eapply cells_frameD in H; [| exact MUu | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; tac].
  fD FR MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD VEC MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD POST MUu ltac:(clear -SPR CEIL LO DLO DHI ADJ AHI ACE SZ1 SZW NCL LSRC; lia).
  fD DZ2 MUu ltac:(clear -SPR CEIL LO DLO DHI ADJ AHI ACE SZ1 SZW NCL; lia).
  fD GPG2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia). fD PGSZ2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD GOT2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia). fD DPM2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD MLIM2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  apply (rng_fp_le _ _ _ _ FPLE3) in RIMG. apply (rng_fp_le _ _ _ _ FPLE3) in RSTK. apply (rng_fp_le _ _ _ _ FPLE3) in RCH.
  clear MUA MUu MI0 ST2 OLD GOTH.
  iprefix.
  replace (ret_pc (Z_to_bv 64 413032)) with (Z_to_bv 64 413032 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _ |- _ => release_frame FRM STu (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold realloc1_post.
  split; [exact (fp_le_trans _ _ _ FPLE FPLE3)|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MUB|]. split; [assumption|]. split; [exact STu|].
  split; [exact VEC|].
  split. { replace ncap with (sz + (ncap - sz)) by (clear; lia). apply junk_merge; [| | clear -SZ1; lia| clear -SZW NCL; lia].
           - exists SRC. rewrite <- LSRC. exact POST.
           - eapply fill_is_junk. exact DZ2. }
  split; [exact RCH|].
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

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz. Import F_aunmap.TwinB F_adepot1.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_mmapordie.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EMBR_STACK := 352 (only parsing).
Notation EMBV := 0xdb508 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition emb_realloc_entry := 0x65668.

Definition realloc0_post (RNG : footprint) (sp : word) (a ncap lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (a, a + ncap)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' EMBV [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' a [CB (Z.to_nat ncap) (repeat (Z_to_bv 8 0) (Z.to_nat ncap))]
  /\ rng RNG' a ncap /\ rng RNG' (shad a) (shlen ncap)
  /\ rmap_cells m'.

Lemma emb_realloc0_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (want ncap lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBR_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 EMBV -> a1 = Z_to_bv 64 want -> 0 < want -> want < 2^39 -> ncap = (want + 4095) / 4096 * 4096 ->
  rw_cells bsegs m EMBV [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> realloc0_post RNG sp a ncap lo m RNG' m' ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_realloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> WPOS WHI NCAP VEC RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_realloc_entry in *. word_range sp SPR. atop_facts.
  assert (NC : ncap mod 4096 = 0 /\ want <= ncap /\ ncap < want + 4096) by (rewrite NCAP; clear -WPOS; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  pose proof (munch_refl [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 WPOS WHI. lia. }
  step. step.
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 WPOS WHI. lia. }
  step. step. step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 ncap) ltac:(rewrite land_align4096 by lia; f_equal; rewrite NCAP; clear -WPOS WHI; Z.div_mod_to_equations; lia).
  step. step. step. step.
  step.

  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapordie_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => exact NCM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO NCL NCH WPOS WHI; lia).
  {
    intros a HFR A0 ACE. pose proof (FROK a HFR A0 ACE) as AH. rewrite unsigned_lit by (clear -SPR CEIL LO; lia). unfold AIMG_HI. clear -AH ACE CEIL LO SPR. lia. }
  {
    intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as AHI.
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (a, a + ncap)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono bsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport VEC MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2.
  iprefix.
  replace (ret_pc (Z_to_bv 64 415448)) with (Z_to_bv 64 415448 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step.
  step.
  step. if_lit.
  step.
  step. step. step.
  step.
  carve_frame 48%nat ST2.
  step. step. step. step. step.
  step. if_lit.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -80) _ |- _ => release_frame FRM ST2 (bv_unsigned sp + -32) end.
  step. step.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _ |- _ => release_frame FRM ST2 (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold realloc0_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MUA|]. split; [exact WMA|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact VEC|]. split; [exact ZCH|]. split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition realloc1_post (RNG : footprint) (sp : word) (d cap sz a ncap lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' EMBV [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 sz)]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma emb_realloc1_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (d cap sz want ncap lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBR_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 EMBV -> a1 = Z_to_bv 64 want -> want < 2^39 -> ncap = (want + 4095) / 4096 * 4096 ->
  rw_cells bsegs m EMBV [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 < cap -> cap mod 4096 = 0 -> 1 <= sz -> sz <= cap -> sz <= want ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d \/ d + cap <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d cap) (adec_munmap d cap)) (K2 a)) ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> realloc1_post RNG sp d cap sz a ncap lo m RNG' m' ->
      implS bsegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_realloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> WHI NCAP VEC OLD DLO DHI CPOS CAL SZ1 SZC SZW RC RIMG RSTK ROLD FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_realloc_entry in *. word_range sp SPR. atop_facts.
  assert (NC : ncap mod 4096 = 0 /\ want <= ncap /\ ncap < want + 4096) by (rewrite NCAP; clear -SZ1 SZW; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  destruct OLD as [junk OLD].
  pose proof (munch_refl [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 SZ1 SZW WHI. lia. }
  step. step.
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SZ1 SZW WHI. lia. }
  step. step. step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 ncap) ltac:(rewrite land_align4096 by lia; f_equal; rewrite NCAP; clear -SZ1 SZW WHI; Z.div_mod_to_equations; lia).
  step. step. step. step.
  step.

  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapordie_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => exact NCM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO NCL NCH SZ1 SZW WHI; lia).
  { intros a HFR A0 ACE. destruct (FROK a HFR A0 ACE) as [AH _]. rewrite unsigned_lit by (clear -SPR CEIL LO; lia). unfold AIMG_HI. clear -AH ACE CEIL LO SPR. lia. }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
  destruct (FROK a HFR A0 ACE) as [AHI ADJ].
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport VEC MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE; lia).
  xport OLD MU2 WM2 ltac:(clear -SPR CEIL LO AHI A0 ACE ADJ DLO DHI CPOS; lia).
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in ROLD.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2.

  set (SRC := firstn (Z.to_nat sz) junk).
  assert (LJ : length junk = Z.to_nat cap) by (destruct OLD as [[[WF _] _] _]; exact WF).
  assert (LSRC : length SRC = Z.to_nat sz) by (unfold SRC; rewrite firstn_length, LJ; clear -SZ1 SZC; lia).
  assert (TB : bytes_at bsegs m2 d (SRC ++ skipn (Z.to_nat sz) junk)).
  { unfold SRC. rewrite firstn_skipn. destruct OLD as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
  change (rw_cells bsegs m2 a [CB (Z.to_nat ncap) (repeat (Z_to_bv 8 0) (Z.to_nat ncap))]) with (fill_at m2 a ncap 0) in ZCH.
  destruct (fill_split m2 a sz (ncap - sz) 0 ltac:(replace (sz + (ncap - sz)) with ncap by (clear; lia); exact ZCH) ltac:(clear -SZ1; lia) ltac:(clear -SZW NCL; lia)) as [DZ1 DZ2].
  unfold fill_at in DZ1, DZ2. rewrite <- LSRC in DZ1.
  iprefix.
  replace (ret_pc (Z_to_bv 64 415448)) with (Z_to_bv 64 415448 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (imemcpy_specZ RNG') with (src := SRC) (rest := skipn (Z.to_nat sz) junk) (junk := repeat (Z_to_bv 8 0) (length SRC));
      [ eassumption | exact TB | exact DZ1
      | rewrite LSRC; clear -SZ1; lia
      | rewrite length_app, skipn_length, LJ, LSRC; clear -ADJ SZ1 SZC SZW NCL CPOS; lia
      | pose proof atop_range as ATR; clear -ACE SZW NCL ATR A0 SZ1; lia
      | pose proof atop_range as ATR; rewrite length_app, skipn_length, LJ, LSRC; clear -DHI SZ1 SZC CPOS ATR DLO; lia
      | clear -SZ1; lia
      | eapply rng_sub'; [exact ROLD|]; clear -SZ1 SZC; lia
      | eapply rng_sub'; [exact RCH|]; clear -SZ1 SZW NCL; lia ]
    | post_call bsegs mc ]
  end.
  step. step. step.
  step.

  apply evtF_done. rewrite (SHAPE a HFR).
  assert (GOTH : rw_cells bsegs x3 0xd3620 [C8 (Z_to_bv 64 0x16d7a8)]).
  { apply (proj1 (rw_cells_app bsegs x3 0xd3620 [C8 (Z_to_bv 64 0x16d7a8)] _)) in GOT2 as [G _]. exact G. }
  eapply (unmap_or_die_spec RNG' (K2 a) Q) with (addr := d) (size := cap) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST2
       | |- mem_inv _ _ => exact MI0
       | |- @eq word _ _ => reflexivity
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       | |- unmap_cells _ => split; [exact GOTH| exact MLIM2]
       | |- forall _, _ => idtac
       | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO DLO DHI CPOS CAL; lia
       end.

  intros rsp RNG3 m3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' HF MUu MIu STu UCu.
  rewrite unsigned_lit in MUu, STu by (clear -SPR CEIL LO; lia).
  destruct HF as [_ FPLE3]. cbn beta iota in FPLE3.
  assert (MUB : munch [(bv_unsigned sp - EMBR_STACK, bv_unsigned sp); (EMBV, EMBV + 16); (d, d + cap); (a, a + ncap)]%Z m m3).
  { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  Ltac fD H MUu tac := eapply cells_frameD in H; [| exact MUu | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; tac].
  fD FR MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD VEC MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD POST MUu ltac:(clear -SPR CEIL LO DLO DHI ADJ AHI ACE SZ1 SZW NCL LSRC; lia).
  fD DZ2 MUu ltac:(clear -SPR CEIL LO DLO DHI ADJ AHI ACE SZ1 SZW NCL; lia).
  fD GPG2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia). fD PGSZ2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD GOT2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia). fD DPM2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  fD MLIM2 MUu ltac:(clear -SPR CEIL LO DLO DHI; lia).
  apply (rng_fp_le _ _ _ _ FPLE3) in RIMG. apply (rng_fp_le _ _ _ _ FPLE3) in RSTK. apply (rng_fp_le _ _ _ _ FPLE3) in RCH.
  clear MUA MUu MI0 ST2 OLD GOTH.
  iprefix.
  replace (ret_pc (Z_to_bv 64 415480)) with (Z_to_bv 64 415480 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. step.
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _ |- _ => release_frame FRM STu (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold realloc1_post.
  split; [exact (fp_le_trans _ _ _ FPLE FPLE3)|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MUB|]. split; [assumption|]. split; [exact STu|].
  split; [exact VEC|].
  split. { replace ncap with (sz + (ncap - sz)) by (clear; lia). apply junk_merge; [| | clear -SZ1; lia| clear -SZW NCL; lia].
           - exists SRC. rewrite <- LSRC. exact POST.
           - eapply fill_is_junk. exact DZ2. }
  split; [exact RCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.
End TwinB.
