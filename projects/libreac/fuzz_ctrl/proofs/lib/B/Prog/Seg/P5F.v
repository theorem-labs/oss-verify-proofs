(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its addresses and numbers changed; 271 of its 321 lines of code are new or changed and 880 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P5.v p5_evt at a working branch 3803efccea0
     (blob 97ba3fa3f27abdcc79e1b448684fbfe645f3e809);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p5_evt_of_F composes p5_pre_F, the caller's asan_memset_contract premise and p5_post_F and
     re-derives the source statement of P5.p5_evt verbatim; p5_evt_same checks that type against P5.p5_evt.
     p5_pre_F re-runs P5.v lines 86-120 (0x81d28 .. 0x81d64, up to the callee entry), p5_post_F lines 138-185
     (the return pc 0x81d68, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twin of P5's run [0x81d28, 0x81d68), split at the call (parent ruling: every call splits):
     the nine frame-variable marks and the code byte, then li a1,0; ld a0,64(s1); li a2,32;
     jal checked_memset -> p5_pre_F, stops AT the callee entry 0x52600 with ra = 0x81d68.
   Regions of the stretch: the 16 frame-shadow bytes [Sh + 370, Sh + 386) (written), the code byte [Y, Y + 1)
   (written) and the scratch pointer [Ab + 64, Ab + 72) (read).  No instrumented check in the stretch; the 32
   bytes at D and the callee window [spv - 2208, spv) are the callee's own footprint and appear only in the
   post facts. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane): p5_pre_F_on is p5_pre_F with the
   universal premise `shadow_rw m` DROPPED and the post conjunct `shadow_rw m1` replaced by the transport
   `forall P, shadow_rw_on P m -> shadow_rw_on P m1` (every region: the stretch writes the 16 frame-shadow bytes
   [Sh + 370, Sh + 386), present in m1, and the code byte Y, which is application memory, not shadow).  Measured
   from the stretch's proof: the marks go through the rw_cells premise (rng (Sh + 370) 16), the code byte through
   the rw_cells premise at Y (rng Y 1) and the scratch pointer load through the ro_cells premise (rng (Ab + 64) 8);
   the post's addressable fact for D comes from the stored marks; the shadow premise was used only to rebuild the
   post's `shadow_rw m1`, so the stretch reads and stores no shadow byte through it.  p5_pre_F keeps its statement,
   as a corollary (the post with P := fun _ => True). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* Tac_bp.bp_fix matches [evt] (3 arguments); the [evtF] goal has 4.  Same hook over evtF. *)
Ltac bp_fixF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      first [rewrite (bp_le1_lit z) by lia | rewrite (bp_le1 (Z_to_bv 64 z))]; mem_after_store
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (bp_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac bp_sbF := step; bp_fixF.

(* Tac_bp.bp_shadow_rw under a region guard P: a munch whose written shadow bytes are present after it keeps every
   shadow_rw_on region. *)
Lemma p5_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- 0x81d28 .. 0x81d64, route (C): no shadow premise; the post transports every shadow_rw_on region ---- *)
Lemma p5_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab Y D lo : Z)
         (xs : list byte) (yb : byte) (junk : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> s8 = Z_to_bv 64 Y ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 80 <= 2 ^ 64 ->
    RT_HI <= Y -> app_mem Y -> Y + 16 <= D -> D + 32 <= Sh \/ Sh + 392 <= Y ->
    D mod 8 = 0 -> shadow_addr D = Sh + 382 -> (forall a, D <= a <= D + 32 -> app_mem a) ->
    (D + 32 <= spv - 2208 \/ spv <= D) -> D + 32 <= Ab ->
    length xs = 16%nat -> rw_cells rsegs m (Sh + 370) (map C1 xs) ->
    rw_cells rsegs m Y (map C1 [yb]) -> rw_cells rsegs m D [CB 32 junk] ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 D)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m ->
    rng RNG (Sh + 370) 16 -> rng RNG Y 1 -> rng RNG (Ab + 64) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81d68) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 Ab)
                       (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 32) a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 Sh) s4 s5 s6 s7 (Z_to_bv 64 Y) s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x52600) fc None m1 (seg_rom rsegs) /\
         munch [(Sh + 370, Sh + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\
         mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1) /\
         rw_cells rsegs m1 D [CB 32 junk] /\ addressable m1 D 32 /\
         bytes_at rsegs m1 (Sh + 380) [Z_to_bv 8 1] /\
         (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 ->
            exists b, mrd rsegs m1 (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d28) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab Y D lo xs yb junk -> -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HYrt HYapp HYD HSD
    HD8 HshD HDapp Hsep HDA Hxs CH CHY RWD RO64 HMI ST HAC GS GY GA.
  do 16 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  cbn [map] in CHY.
  pose proof (rw_cells_bound rsegs m (Sh + 370) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m D _ RWD) as HDb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (HDapp (D + 32) ltac:(lia)) as HD32.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HD32.
  pose proof HYapp as HYa. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HYa.
  assert (EU1 : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  pose proof (munch_refl [(Sh + 370, Sh + 386); (Y, Y + 1)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  step.
  bp_sbF.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  pose proof (proj2 (proj1 CHY)) as HbY. cbn [cells_bytes cbytes app] in HbY.
  assert (HRD1 : forall x, Sh + 370 <= x < Sh + 386 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 (Sh + 370) _ x HbC).
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HRDY : forall x, Y <= x < Y + 1 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 Y _ x HbY). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (p5_srw_on_munch P _ m m1 HP MU1 WM). intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 370) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 386)) as [H2|H2]|].
    - right. exact (HRD1 a ltac:(lia)).
    - left. cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hin. replace a with Y in Ha by lia. exact (app_not_shadow Y HYapp Ha).
    - left. cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hin. replace a with Y in Ha by lia. exact (app_not_shadow Y HYapp Ha). }
  assert (ADR1 : addressable m1 D 32).
  { pose proof (bp_ba_sub _ _ _ 12 4 HbC ltac:(cbn [length]; lia)) as B12.
    cbn [firstn skipn] in B12. replace (Sh + 370 + Z.of_nat 12) with (Sh + 382) in B12 by lia.
    apply (bp_addr_z m1 D 4 32); [reflexivity | lia | exact HD8 | unfold APPMEM_END; lia
      | intros i Hi; apply HDapp; lia |].
    rewrite HshD. exact B12. }
  pose proof (bp_ba_sub _ _ _ 10 1 HbC ltac:(cbn [length]; lia)) as B380.
  cbn [firstn skipn] in B380.
  replace (Sh + 370 + Z.of_nat 10) with (Sh + 380) in B380 by lia.
  apply evtF_done.
  do 12 eexists. exists m1.
  split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM|]. split; [exact HMI|]. split; [exact ST|].
  split; [exact HAC1|]. split; [exact HSW1|]. split; [exact RWD|]. split; [exact ADR1|].
  split; [exact B380|].
  intros x [Hx|Hx]; [exact (HRD1 x Hx) | exact (HRDY x Hx)].
Qed.

(* ---- 0x81d28 .. 0x81d64: the marks, the code byte, the reload and jal checked_memset ---- *)
Lemma p5_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab Y D lo : Z)
         (xs : list byte) (yb : byte) (junk : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> s8 = Z_to_bv 64 Y ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 80 <= 2 ^ 64 ->
    RT_HI <= Y -> app_mem Y -> Y + 16 <= D -> D + 32 <= Sh \/ Sh + 392 <= Y ->
    D mod 8 = 0 -> shadow_addr D = Sh + 382 -> (forall a, D <= a <= D + 32 -> app_mem a) ->
    (D + 32 <= spv - 2208 \/ spv <= D) -> D + 32 <= Ab ->
    length xs = 16%nat -> rw_cells rsegs m (Sh + 370) (map C1 xs) ->
    rw_cells rsegs m Y (map C1 [yb]) -> rw_cells rsegs m D [CB 32 junk] ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 D)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 370) 16 -> rng RNG Y 1 -> rng RNG (Ab + 64) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81d68) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 Ab)
                       (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 32) a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 Sh) s4 s5 s6 s7 (Z_to_bv 64 Y) s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x52600) fc None m1 (seg_rom rsegs) /\
         munch [(Sh + 370, Sh + 386); (Y, Y + 1)] m m1 /\ wmono rsegs m m1 /\
         mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\ shadow_rw m1 /\
         rw_cells rsegs m1 D [CB 32 junk] /\ addressable m1 D 32 /\
         bytes_at rsegs m1 (Sh + 380) [Z_to_bv 8 1] /\
         (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 ->
            exists b, mrd rsegs m1 (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d28) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab Y D lo xs yb junk Hsp Hs3 Hs1 Hs8 HSrt HSlo HHM HLO HAE HSA HA64 HYrt HYapp HYD HSD
    HD8 HshD HDapp Hsep HDA Hxs CH CHY RWD RO64 HMI ST HAC HSW GS GY GA.
  refine (evtF_mono rsegs RNG _ _ _
            (p5_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m spv Sh Ab Y D lo xs yb junk Hsp Hs3 Hs1 Hs8 HSrt HSlo HHM HLO HAE HSA HA64 HYrt
               HYapp HYD HSD HD8 HshD HDapp Hsep HDA Hxs CH CHY RWD RO64 HMI ST HAC GS GY GA) _).
  intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU & WM & MI & ST1 & AC & SW & K).
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m1.
  exact (conj E (conj MU (conj WM (conj MI (conj ST1 (conj AC
           (conj (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))) K))))))).
Qed.

(* ---- the return pc 0x81d68: the premises are the callee post facts and the pre-call facts P5's proof
       uses at that point ---- *)
Lemma p5_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word)
         (spv Sh Y D lo : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 26 = s10 -> getr R 24 = s8 -> getr R 23 = s7 -> getr R 25 = s9 ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    RT_HI <= Y -> Y + 16 <= D -> D + 32 <= Sh \/ Sh + 392 <= Y ->
    0 <= D -> D + 32 <= 2 ^ 64 ->
    munch [(Sh + 370, Sh + 386); (Y, Y + 1)] m m1 -> wmono rsegs m m1 ->
    bytes_at rsegs m1 (Sh + 380) [Z_to_bv 8 1] ->
    (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 ->
       exists b, mrd rsegs m1 (wa x) = Some b) ->
    munch [(D, D + 32); (spv - 2208, spv)] m1 m' -> wmono rsegs m1 m' ->
    stk rsegs m' lo spv -> shadow_rw m' ->
    bytes_at rsegs m' D (repeat (Z_to_bv 8 0) 32) ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81d68) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 26 = s10 /\ getr R' 24 = s8 /\ getr R' 23 = s7 /\ getr R' 25 = s9 /\
         munch [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)] m m'' /\
         wmono rsegs m m'' /\ stk rsegs m'' lo spv /\ shadow_rw m'' /\
         bytes_at rsegs m'' (Sh + 380) [Z_to_bv 8 1] /\
         (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 \/ D <= x < D + 32 \/ spv - 2208 <= x < spv ->
            exists b, mrd rsegs m'' (wa x) = Some b))
      (MS R F (Z_to_bv 64 0x81d68) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m1 m' sp gp tp s0 s1 s3 s7 s8 s9 s10 spv Sh Y D lo
    K2 K3 K4 K8 K9 K19 K26 K24 K23 K25
    HSrt HSlo HHM HLO HAE HYrt HYD HSD HD0 HD64 MU1 WM B380 HRD MU2 WM2 ST2 SW2 HDb'.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (Hsub : sub_fp [(D, D + 32); (spv - 2208, spv)]
                   [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  assert (Hsub1 : sub_fp [(Sh + 370, Sh + 386); (Y, Y + 1)]
                   [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m'
                (munch_weaken _ _ m m1 Hsub1 MU1) (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (KEEP : forall x, (x < D \/ D + 32 <= x) -> (x < spv - 2208 \/ spv <= x) ->
            mrd rsegs m' (wa x) = mrd rsegs m1 (wa x) \/ ~ (0 <= x < 2 ^ 64)).
  { intros x H1 H2. destruct (Z_le_gt_dec 0 x) as [Hx0|Hx0]; [destruct (Z_lt_ge_dec x (2 ^ 64)) as [Hx1|Hx1]|].
    - left. unfold mrd. rewrite (MU2 (wa x)); [reflexivity|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
    - right. lia.
    - right. lia. }
  assert (RDfin : forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 \/ D <= x < D + 32 \/
                            spv - 2208 <= x < spv -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx.
    destruct (Z_le_gt_dec (spv - 2208) x) as [H3|H3]; [destruct (Z_lt_ge_dec x spv) as [H4|H4]|].
    { destruct ST2 as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    all: destruct (Z_le_gt_dec D x) as [H1|H1]; [destruct (Z_lt_ge_dec x (D + 32)) as [H2|H2]|].
    all: try (apply (bp_ba_rd m' D _ x HDb'); rewrite repeat_length; lia).
    all: destruct (KEEP x ltac:(lia) ltac:(lia)) as [Hk|Hk]; [|lia]; rewrite Hk.
    all: apply HRD; lia. }
  pose proof (bytes_at_transport rsegs [(D, D + 32); (spv - 2208, spv)] m1 m' _ _ B380 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from];
          split; [lia | split; [lia | exact I]])) as B380'.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K24|]. split; [exact K23|]. split; [exact K25|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact ST2|]. split; [exact SW2|]. split; [exact B380' | exact RDfin].
Qed.

(* ---- the compare lemma: the source statement of P5.p5_evt ---- *)
Lemma p5_evt_of_F : MSC.asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab Y D lo : Z)
         (xs : list byte) (yb : byte) (junk : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> s8 = Z_to_bv 64 Y ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 80 <= 2 ^ 64 ->
    RT_HI <= Y -> app_mem Y -> Y + 16 <= D -> D + 32 <= Sh \/ Sh + 392 <= Y ->
    D mod 8 = 0 -> shadow_addr D = Sh + 382 -> (forall a, D <= a <= D + 32 -> app_mem a) ->
    (D + 32 <= spv - 2208 \/ spv <= D) -> D + 32 <= Ab ->
    length xs = 16%nat -> rw_cells rsegs m (Sh + 370) (map C1 xs) ->
    rw_cells rsegs m Y (map C1 [yb]) -> rw_cells rsegs m D [CB 32 junk] ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 D)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d68) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = s8 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\ shadow_rw m' /\
         bytes_at rsegs m' (Sh + 380) [Z_to_bv 8 1] /\
         (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 \/ D <= x < D + 32 \/ spv - 2208 <= x < spv ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d28) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab Y D lo xs yb junk -> -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HYrt HYapp HYD HSD
    HD8 HshD HDapp Hsep HDA Hxs CH CHY RWD RO64 HMI ST HAC HSW.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  pose proof (rw_cells_bound rsegs m D _ RWD) as HDb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDb.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p5_pre_F with (spv := spv) (Sh := Sh) (Ab := Ab) (Y := Y) (D := D) (lo := lo)
      (xs := xs) (yb := yb) (junk := junk); try reflexivity; try assumption;
      apply rng_all; unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *; lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MU1 & WM & MI1 & ST1 & AC1 & SW1 & RWD1 & ADR1 & B380 & HRD).
  subst ms'.
  pose proof (HDapp (D + 32) ltac:(lia)) as HD32.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HD32.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (EU1 : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { eapply MSET with (junk := junk) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 32)) with 32.
    - exact RWD1.
    - lia.
    - exact ADR1.
    - unfold end_in_app. right. apply HDapp. lia.
    - right. apply HDapp. lia.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST1.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact AC1.
    - exact SW1.
    - exact MI1. }
  intros ms' PO. unfold MSC.asan_memset_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms'.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 32) with 32%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  assert (HDb' : bytes_at rsegs m' D (repeat (Z_to_bv 8 0) 32)).
  { destruct RW2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  replace (ret_pc (Z_to_bv 64 0x81d68)) with (Z_to_bv 64 0x81d68)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p5_post_F with (m := m) (m1 := m1) (spv := spv) (Sh := Sh) (Y := Y) (D := D) (lo := lo);
    try reflexivity; try assumption; try (unfold RT_HI, HIGHMEM_BEG, APPMEM_END; lia).
Qed.

(* p5_evt_of_F has exactly the statement of the source lemma P5.p5_evt. *)
Definition p5_evt_same : ltac:(let T := type of P5.p5_evt in exact T) := p5_evt_of_F.
