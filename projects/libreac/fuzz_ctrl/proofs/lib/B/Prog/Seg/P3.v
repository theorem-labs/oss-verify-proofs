(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module names, addresses and numbers changed; 387 of its 541 lines of code are new or changed and 776 lines of the source are left out. *)
(* Segment P3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81cb0, 0x81d14], 26
   instructions, cut Inv_B81cb0 (v1.9 pc 0x81cb0) -> cut Inv_B81d18 (v1.9 pc 0x81d18) (plan-asan-ubsan.md section 2,
   row P3; section 4, MSET = checked_memset 0x52600, INIT = reac_identity_init 0x87de8).
   rule 24: no function proved (a slot segment).  With s3 = S(fr) the code marks the init frame variables usable in
   the frame shadow (plan-asan FP.4): the identity record at fr + 2688 (S(fr) + 336 .. 340 = 00 00 00 00 06,
   0x81cb0 .. 0x81cbc and 0x81ce4), the fragment scratch at fr + 2768 (S(fr) + 346 .. 354 = 00 x 9, 0x81cc4 ..
   0x81cd8 and 0x81ce8 .. 0x81cf0) and, new in v1.9.0, the local `first` at fr + 2880 (S(fr) + 360 .. 364 = 00 x 5,
   0x81cdc / 0x81ce0 and 0x81cf4 .. 0x81cfc); then it zeroes `first` (0x81d00 li a2,40; 0x81d04 ld a0,168(s1),
   [A + 168] = fr + 2880 (PRA); 0x81d08 li a1,0; 0x81d0c jal checked_memset), reloads the identity record base
   [A + 176] = fr + 2688 (0x81d10 ld a0,176(s1); spilled at 0x81500) and calls reac_identity_init (0x81d14), which
   zeroes the 38 id bytes.
   The range has no instrumented shadow check and no UBSan trap.  p3_evt is the Lib-level run of the 26
   instructions with both calls taken on their lib/B contracts (Section hypotheses, never their code); seg_P3
   lifts it to the official cuts: the contracts need mem_inv, so the run is stepped on the normalized memory
   (Tac_bp.bp_run) and FRA / ENT move across the write set (the frame-shadow bytes [S(fr) + 336, S(fr) + 365), the
   callees' stack window [sp - 2224, sp), the id bytes [fr + 2688, fr + 2726) and `first`'s bytes
   [fr + 2880, fr + 2920)) by Tac_bp.bp_post.
   The exit cut Inv_B81d18 names the memset destination D = [A + 208] = fr + 2768 (the entry's rw_cells cell): its
   72 bytes are addressable here, from the nine zero shadow bytes S(fr) + 346 .. 354 this segment writes.  The exit
   also carries D = fr + 2768, the spill [A + 64] = fr + 3056 (from the entry), the identity record ID0 at
   fr + 2688 (the zero bytes reac_identity_init leaves) and its 38 bytes addressable (S(fr) + 336 .. 340), CUR g c0
   (s7 / s9, kept by the callees), the kind-name table's addressability (its shadow is in the low shadow, apart from
   the write set), the spill [A + 176] = fr + 2688 (the entry's q64) and PRO (Tac_bp.bp_PRO_keep: the write set
   misses [A, A + 448) and our[]'s shadow byte Sfr fr + 328), and the turn-0 first-fragment state FSj g fr 0 with
   `first`'s 40 bytes addressable (the memset's 40 zero bytes; S(fr) + 360 .. 364 = 0; Tac_bp.bp_fsj0). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_init_c asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
Import ListNotations.
Open Scope Z_scope.

Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.
Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* ---- the run: the 19 shadow stores (li a0,6 among them), li a2,40, ld a0,168(s1), li a1,0, jal checked_memset by
   its contract, ld a0,176(s1), jal reac_identity_init by its contract ---- *)
Lemma p3_evt : MSC.asan_memset_contract -> RII.reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp fp lo : Z)
         (xs idb fpb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 184 <= 2 ^ 64 -> spv <= Ab -> fp + 40 <= Ab ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 336 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    (Sh + 392 <= fp \/ fp + 40 <= Sh) -> RT_HI <= fp -> fp mod 8 = 0 -> shadow_addr fp = Sh + 360 ->
    (forall a, fp <= a <= fp + 40 -> app_mem a) ->
    (fp + 40 <= spv - 2224 \/ spv <= fp) -> (idp + 38 <= fp \/ fp + 40 <= idp) ->
    length xs = 29%nat -> rw_cells rsegs m (Sh + 336) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> rw_cells rsegs m fp [CB 40 fpb] ->
    ro_cells rsegs m (Ab + 168) [C8 (Z_to_bv 64 fp)] -> ro_cells rsegs m (Ab + 176) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d18) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = s8 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
         rw_cells rsegs m' fp [CB 40 (repeat (Z_to_bv 8 0) 40)] /\
         bytes_at rsegs m' (Sh + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m' (Sh + 346) (repeat (Z_to_bv 8 0) 9) /\
         bytes_at rsegs m' (Sh + 360) (repeat (Z_to_bv 8 0) 5))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs)).
Proof.
  intros MSET INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp fp lo xs idb fpb -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HspAb HfpAb HSid Hidrt Hid8
    Hshid Hidapp Hsep
    HSfp Hfprt Hfp8 Hshfp Hfpapp Hsepf Hidfp Hxs CH RWid RWfp RO168 RO176 HMI ST HAC HSW.
  unfold RII.reac_identity_init_contract, RII.REAC_IDENTITY_INIT, RII.REAC_IDENTITY_INIT_K in INIT.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  do 29 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 336) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m idp _ RWid) as Hidb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hidb.
  pose proof (rw_cells_bound rsegs m fp _ RWfp) as Hfpb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hfpb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  pose proof (Hidapp (idp + 38) ltac:(lia)) as Hidhi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hidhi.
  pose proof (Hfpapp (fp + 40) ltac:(lia)) as Hfphi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hfphi.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x81cb0 .. 0x81cfc: sb x4, li a0,6, sb x8 (349 .. 354, 360, 361), sb a0,340, sb x3 (346 .. 348),
     sb x3 (362 .. 364) *)
  bp_sb. bp_sb. bp_sb. bp_sb.
  step.
  bp_sb. bp_sb. bp_sb. bp_sb. bp_sb. bp_sb. bp_sb. bp_sb.
  bp_sb.
  bp_sb. bp_sb. bp_sb.
  bp_sb. bp_sb. bp_sb.
  (* li a2,40; ld a0,168(s1); li a1,0; jal checked_memset *)
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : shadow_rw m1).
  { apply (bp_shadow_rw _ m m1 HSW MU WM). intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 336) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 365)) as [H2|H2]|].
    - right. apply (bp_ba_rd m1 (Sh + 336) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia|]. split; [lia|].
      split; [intros Hin; exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha)|].
      split; [intros Hin; exact (app_not_shadow a (Hfpapp a ltac:(lia)) Ha) | exact I].
    - left. cbn [outside]. split; [lia|]. split; [lia|].
      split; [intros Hin; exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha)|].
      split; [intros Hin; exact (app_not_shadow a (Hfpapp a ltac:(lia)) Ha) | exact I]. }
  pose proof (bp_ba_sub _ _ _ 0 5 HbC ltac:(cbn [length]; lia)) as B0.
  pose proof (bp_ba_sub _ _ _ 10 9 HbC ltac:(cbn [length]; lia)) as B10.
  pose proof (bp_ba_sub _ _ _ 24 5 HbC ltac:(cbn [length]; lia)) as B24.
  cbn [firstn skipn] in B0, B10, B24.
  replace (Sh + 336 + Z.of_nat 0) with (Sh + 336) in B0 by lia.
  replace (Sh + 336 + Z.of_nat 10) with (Sh + 346) in B10 by lia.
  replace (Sh + 336 + Z.of_nat 24) with (Sh + 360) in B24 by lia.
  assert (HA1 : addressable m1 idp 38).
  { apply bp_id_addr; [lia | exact Hid8 | unfold APPMEM_END; lia | intros i Hi; apply Hidapp; lia |].
    rewrite Hshid. exact B0. }
  assert (HAfp : addressable m1 fp 40).
  { apply (bp_addr_z m1 fp 5 40); [reflexivity | lia | exact Hfp8 | unfold APPMEM_END; lia
      | intros i Hi; apply Hfpapp; lia |].
    rewrite Hshfp. exact B24. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 fp) = fp) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { eapply MSET with (junk := fpb) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 40)) with 40.
    - exact RWfp.
    - lia.
    - exact HAfp.
    - unfold end_in_app. right. apply Hfpapp. lia.
    - right. apply Hfpapp. lia.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact HAC1.
    - exact HSW1.
    - exact HMI. }
  intros ms2 PO2. unfold MSC.asan_memset_post in PO2.
  destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                   E2 & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms2.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 40)) with 40 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 40) with 40%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  replace (ret_pc (Z_to_bv 64 0x81d10)) with (Z_to_bv 64 0x81d10)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the cells the rest of the run reads, carried across the memset's write set *)
  assert (Hdj2 : forall a n, (a + n <= fp \/ fp + 40 <= a) -> (a + n <= spv - 2208 \/ spv <= a) ->
            disjoint_from [(fp, fp + 40); (spv - 2208, spv)] a n).
  { intros a n Ha1 Ha2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  pose proof (ro_cells_transport rsegs _ m1 m2 _ _ RO176 MU2
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as RO176'.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ RWid MU2 WM2
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as RWid2.
  assert (HA2 : addressable m2 idp 38).
  { apply (bp_addr_keep _ m1 m2 idp 38 HA1 MU2). intros i Hi.
    rewrite (bp_sh_add idp i Hid8 ltac:(lia)), Hshid.
    assert (Hq : 0 <= i / 8 < 5) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B0 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B0m.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B10 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B10m.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B24 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B24m.
  (* ld a0,176(s1); jal reac_identity_init *)
  step. step.
  eapply evt_cut.
  { eapply INIT with (lo := lo) (id := idp) (idb := idb).
    - reflexivity.
    - lia.
    - intros _. split; [Z.div_mod_to_equations; lia | exact RWid2].
    - exact MI2.
    - rewrite MState.unsigned_lit by lia. exact ST2.
    - rewrite MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite MState.unsigned_lit by lia. unfold APPMEM_END. lia.
    - exact AC2.
    - exact SW2.
    - intros _. split; [exact HA2 | right; apply Hidapp; lia].
    - intros _. right. unfold RT_HI. lia.
    - intros _. rewrite MState.unsigned_lit by lia. exact Hsep. }
  intros ms' PO.
  unfold RII.reac_identity_init_post, RII.reac_identity_init_W, RII.REAC_IDENTITY_INIT_K,
    RII.REAC_IDENTITY_INIT_FRAME in PO.
  destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                  m' & E & MU3 & WM3 & MI3 & ST3 & AC3 & SW3 & _ & HZ).
  subst ms'.
  specialize (HZ ltac:(lia)).
  rewrite MState.unsigned_lit in MU3, ST3 by lia.
  assert (Hdj3 : forall a n, (a + n <= spv - 2224 \/ spv <= a) -> (a + n <= idp \/ idp + 38 <= a) ->
            disjoint_from [(spv - 2224, spv); (idp, idp + 38)] a n).
  { intros a n Ha1 Ha2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (Hsub2 : sub_fp [(fp, fp + 40); (spv - 2208, spv)]
                    [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. lia. }
  assert (Hsub3 : sub_fp [(spv - 2224, spv); (idp, idp + 38)]
                    [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m2 MU (munch_weaken _ _ m1 m2 Hsub2 MU2)) as MU12.
  pose proof (munch_trans _ m m2 m' MU12 (munch_weaken _ _ m2 m' Hsub3 MU3)) as MUf.
  pose proof (rw_cells_transport rsegs _ m2 m' _ _ RW2 MU3 WM3
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as RWfpf.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B0m MU3
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B0'.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B10m MU3
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B10'.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B24m MU3
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B24'.
  replace (ret_pc (Z_to_bv 64 0x81d18)) with (Z_to_bv 64 0x81d18)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m2 m' (wmono_trans rsegs m m1 m2 WM WM2) WM3)|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact AC3|]. split; [exact SW3|].
  split; [exact HZ|]. split; [exact RWfpf|]. split; [exact B0'|]. split; [exact B10' | exact B24'].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

Section P3.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The two callees checked_memset (MSET@0x81d0c) and reac_identity_init (INIT@0x81d14), taken on their lib/B
   contracts, never on their code. *)
Hypothesis MSET : MSC.asan_memset_contract.
Hypothesis INIT : RII.reac_identity_init_contract.

Lemma seg_P3 : Hcut B APIf ra (Inv_B81d18 B APIf ra) -> Hcut B APIf ra (Inv_B81cb0 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & H24 & HPRO & H64 & HCUR & HKN &
                    spv & Ac & idb0 & junk & HB).
  destruct HB as (Hr2s & Hr9s & HAc & Hspvr & Hq176 & H208 & HRWid & HRWfg & _).
  subst c.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  pose proof (Hplace 2208 ltac:(lia)) as Hsep8. rewrite Haspz in Hsep8.
  assert (HMK : asan_memset_c.ASAN_MEMSET_K = 2208) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hsp64 : 0 <= sp < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAeq : Ac = A) by (apply (bp_rg_inj regs 9 Ac A Hr9s Hr9 HAc HA64)).
  subst Ac.
  assert (Hspveq : spv = sp) by (apply (bp_rg_inj regs 2 spv sp Hr2s Hr2 Hspvr Hsp64)).
  subst spv.
  destruct H64 as (A4 & HA4 & Hq64).
  assert (HA4e : A4 = A)
    by (apply (bp_spill_A regs mem 64 (fr + 3056) A A4 HA4 Hq64 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  (* PRA's [A + 168] = fr + 2880, the local `first`, which the memset zeroes *)
  pose proof HPRO as (HPRA0 & _).
  destruct HPRA0 as (_ & _ & H168 & _).
  destruct H168 as (A5 & HA5 & Hq168).
  assert (HA5e : A5 = A)
    by (apply (bp_spill_A regs mem 168 (fr + 2880) A A5 HA5 Hq168 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A5.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  (* the 29 frame-shadow cells [S(fr) + 336, S(fr) + 365) the stores hit, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite FRAME_SHADOW_val in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (bp_ba_sub mem (Sfr fr) sh 336 29 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 336) with (Sfr fr + 336) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 29 (skipn 336 sh)) = 29%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 336) (map C1 (firstn 29 (skipn 336 sh)))).
  { apply bp_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 29) with 29.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 336 + i)).
    { replace (Sfr fr + 336 + i) with (Sfr fr + (336 + i)) by lia. apply bp_fsh; [exact Happ' | lia]. }
    exact (proj1 (HSW0 _ Hin)). }
  (* the id record's 38 bytes and `first`'s 40 bytes (read + writable, from the frame window) and the [A + 168] /
     [A + 176] spills, on the normalized memory *)
  pose proof (bp_frame_stk B APIf ra g fr [] regs mem md HFRA) as Hfstk.
  pose proof (bp_stk_rel mem (normalize rsegs mem) fr (fr + 3136) HR0 ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 2688) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs _ (fr + 2688) (fr + 2726) (fr + 3136) Hfs2 ltac:(lia)) as (Hids & Hfs3).
  destruct (stk_split rsegs _ (fr + 2726) (fr + 2880) (fr + 3136) Hfs3 ltac:(lia)) as (_ & Hfs4).
  destruct (stk_split rsegs _ (fr + 2880) (fr + 2920) (fr + 3136) Hfs4 ltac:(lia)) as (Hfps & _).
  destruct (bp_stk_rw _ _ _ Hids ltac:(lia)) as (idb & RWid0).
  destruct (bp_stk_rw _ _ _ Hfps ltac:(lia)) as (fpb & RWfp0).
  replace (Z.to_nat (fr + 2726 - (fr + 2688))) with 38%nat in RWid0 by lia.
  replace (Z.to_nat (fr + 2920 - (fr + 2880))) with 40%nat in RWfp0 by lia.
  assert (RO176 : ro_cells rsegs (normalize rsegs mem) (A + 176) [C8 (Z_to_bv 64 (fr + 2688))]).
  { apply bp_ro8. unfold q64 in Hq176. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq176). }
  assert (RO168 : ro_cells rsegs (normalize rsegs mem) (A + 168) [C8 (Z_to_bv 64 (fr + 2880))]).
  { apply bp_ro8. unfold q64 in Hq168. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq168). }
  (* p3_evt's arithmetic premises *)
  assert (P1 : RT_HI <= Sfr fr) by (unfold RT_HI; lia).
  assert (P2 : Sfr fr + 392 <= sp - FN_STACK) by lia.
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2224 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P5b : A + 184 <= 2 ^ 64) by lia.
  assert (P6 : Sfr fr + 392 <= fr + 2688 \/ fr + 2688 + 38 <= Sfr fr) by lia.
  assert (P7 : RT_HI <= fr + 2688) by (unfold RT_HI; lia).
  assert (P8 : (fr + 2688) mod 8 = 0) by (replace (fr + 2688) with (fr + 8 * 336) by lia; apply bp_m8; exact Hfrm).
  assert (P9 : shadow_addr (fr + 2688) = Sfr fr + 336)
    by (replace (fr + 2688) with (fr + 8 * 336) by lia; apply bp_sh8).
  assert (P10 : forall a, fr + 2688 <= a <= fr + 2688 + 38 -> app_mem a) by (intros a Ha; apply Happ'; lia).
  assert (P11 : fr + 2688 + 38 <= sp - 2224 \/ sp <= fr + 2688) by lia.
  assert (Q6 : Sfr fr + 392 <= fr + 2880 \/ fr + 2880 + 40 <= Sfr fr) by lia.
  assert (Q7 : RT_HI <= fr + 2880) by (unfold RT_HI; lia).
  assert (Q8 : (fr + 2880) mod 8 = 0) by (replace (fr + 2880) with (fr + 8 * 360) by lia; apply bp_m8; exact Hfrm).
  assert (Q9 : shadow_addr (fr + 2880) = Sfr fr + 360)
    by (replace (fr + 2880) with (fr + 8 * 360) by lia; apply bp_sh8).
  assert (Q10 : forall a, fr + 2880 <= a <= fr + 2880 + 40 -> app_mem a) by (intros a Ha; apply Happ'; lia).
  assert (Q11 : fr + 2880 + 40 <= sp - 2224 \/ sp <= fr + 2880) by lia.
  assert (Q12 : fr + 2688 + 38 <= fr + 2880 \/ fr + 2880 + 40 <= fr + 2688) by lia.
  assert (Q13 : fr + 2880 + 40 <= A) by lia.
  unfold rg in Hr19, Hr9, Hr2, H24.
  rewrite SEGS.
  apply (bp_run regs (Z_to_bv 64 0x81cb0) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81d18 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 24 = getr regs 24 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       LF.munch [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                 (fr + 2880, fr + 2880 + 40)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       rw_cells rsegs m0' (fr + 2688) [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
       rw_cells rsegs m0' (fr + 2880) [CB 40 (repeat (Z_to_bv 8 0) 40)] /\
       bytes_at rsegs m0' (Sfr fr + 336)
         [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
       bytes_at rsegs m0' (Sfr fr + 346) (repeat (Z_to_bv 8 0) 9) /\
       bytes_at rsegs m0' (Sfr fr + 360) (repeat (Z_to_bv 8 0) 5))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p3_evt MSET INIT) with (spv := sp) (Sh := Sfr fr) (Ab := A) (idp := fr + 2688) (fp := fr + 2880)
        (lo := sp - FN_STACK) (xs := firstn 29 (skipn 336 sh)) (idb := idb) (fpb := fpb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P26' & P24' & P23' & P25' &
                  MUq & WMq & MIq & STq & ACq & SWq & RWq & RWfq & Bq0 & Bq10 & Bq24).
      exists R, (Z_to_bv 64 0x81d18), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact P24'|]. split; [exact P23'|]. split; [exact P25'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq|]. split; [exact RWq|]. split; [exact RWfq|].
      split; [exact Bq0|]. split; [exact Bq10 | exact Bq24].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K24 & K23 & K25 & MU0 & WM0 & ST0' & SW0' & RW0' & RWf0' &
       B0q & B10q & B24q)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (bp_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) ST0') as ST'.
    pose proof (bp_srw_back mem' m0' HRel SW0') as SW'.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B10q) as B10.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B24q) as B24.
    assert (HidZ : bytes_at rsegs mem' (fr + 2688) (repeat (Z_to_bv 8 0) 38)).
    { destruct RW0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    assert (HfpZ : bytes_at rsegs mem' (fr + 2880) (repeat (Z_to_bv 8 0) 40)).
    { destruct RWf0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* every written byte is readable after the run *)
    assert (RDW : forall x,
              ~ LF.outside [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                            (fr + 2880, fr + 2880 + 40)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. cbn [LF.outside] in Hx.
      destruct (Z_le_gt_dec (Sfr fr + 336) x) as [X1|X1];
        [destruct (Z_lt_ge_dec x (Sfr fr + 365)) as [X2|X2]|].
      - assert (Hin : in_shadow x).
        { replace x with (Sfr fr + (x - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia]. }
        exact (proj2 (SW' x Hin)).
      - destruct (Z_le_gt_dec (sp - 2224) x) as [Y1|Y1]; [destruct (Z_lt_ge_dec x sp) as [Y2|Y2]|].
        + destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
        + destruct (Z_le_gt_dec (fr + 2688) x) as [Z1|Z1]; [destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [Z2|Z2]|].
          * apply (bp_ba_rd mem' (fr + 2688) _ x HidZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
        + destruct (Z_le_gt_dec (fr + 2688) x) as [Z1|Z1]; [destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [Z2|Z2]|].
          * apply (bp_ba_rd mem' (fr + 2688) _ x HidZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
      - destruct (Z_le_gt_dec (sp - 2224) x) as [Y1|Y1]; [destruct (Z_lt_ge_dec x sp) as [Y2|Y2]|].
        + destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
        + destruct (Z_le_gt_dec (fr + 2688) x) as [Z1|Z1]; [destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [Z2|Z2]|].
          * apply (bp_ba_rd mem' (fr + 2688) _ x HidZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
        + destruct (Z_le_gt_dec (fr + 2688) x) as [Z1|Z1]; [destruct (Z_lt_ge_dec x (fr + 2688 + 38)) as [Z2|Z2]|].
          * apply (bp_ba_rd mem' (fr + 2688) _ x HidZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia.
          * apply (bp_ba_rd mem' (fr + 2880) _ x HfpZ). rewrite repeat_length. lia. }
    assert (HCOV : bp_cover fr (AC.aspZ regs - 2224) (AC.aspZ regs)
                     [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                      (fr + 2880, fr + 2880 + 40)]).
    { intros x Hx. cbn [LF.outside] in Hx. rewrite Haspz. lia. }
    assert (HDJ : rt_disjoint [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                               (fr + 2880, fr + 2880 + 40)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    destruct (bp_post B APIf ra empty FF g fr regs regs'' mem mem' md md'
                [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                 (fr + 2880, fr + 2880 + 40)] 2224
                HFRA HENT ltac:(lia) MU WM Hsame HDJ HCOV RDW E2 E3 E4 E8 E9 E19 E26 Hmat) as (HFRA' & HENT').
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split; [unfold rg; rewrite E24; exact H24|].
    (* the save area [A, A + 448) is apart from the write set *)
    assert (KSP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A0 & HA0 & Hq).
      assert (HA0e : A0 = A)
        by (apply (bp_spill_A regs mem off v A A0 HA0 Hq Hr9); unfold APPMEM_END in *; lia).
      subst A0. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { (* PRO: our[]'s shadow byte Sfr fr + 328 is below the stores' Sfr fr + 336 .. 364 *)
      apply (bp_PRO_keep fr regs regs'' mem mem' KSP); [|exact HPRO].
      intros HOA. apply (bp_addr_keep _ mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
      rewrite (bp_our_sh fr i Hfrm Hi). cbn [LF.outside].
      split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
      unfold rg. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
    split.
    { (* the kind-name table's shadow bytes lie in the low shadow, apart from the write set *)
      apply (bp_addr_keep _ mem mem' KNC.KIND_NAME 112 HKN MU). intros i Hi.
      pose proof (bp_sa_lo (KNC.KIND_NAME + i) ltac:(unfold KNC.KIND_NAME; lia)) as Hk. unfold ASAN_K in Hk.
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split; [unfold IDBe; exact HidZ|].
    split.
    { (* the 38 identity-record bytes are addressable: their shadow bytes S(fr) + 336 .. 340 are 00 00 00 00 06 *)
      pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B0q) as B0.
      apply bp_id_addr; [lia | exact P8 | unfold APPMEM_END; lia | intros i Hi; apply Happ'; lia |].
      rewrite P9. exact B0. }
    split; [exact (KSP 176 (fr + 2688) ltac:(lia) (ex_intro _ A (conj Hr9 Hq176)))|].
    (* `first`'s 40 bytes are addressable: their five shadow bytes S(fr) + 360 .. 364 are 0 *)
    assert (HAfp : addressable mem' (fr + 2880) 40).
    { apply (bp_addr_z mem' (fr + 2880) 5 40); [reflexivity | lia | exact Q8 | lia
        | intros i Hi; apply Happ'; lia |].
      rewrite Q9. exact B24. }
    exists (fr + 2768), sp, A, junk. cbv zeta.
    split; [rewrite E2; exact Hr2|].
    split; [rewrite E9; exact Hr9|].
    split; [exact HA64|]. split; [lia|]. split; [exact Hsp64|].
    split.
    { eapply (rw_cells_transport rsegs
                [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                 (fr + 2880, fr + 2880 + 40)]);
        [exact H208 | exact MU | exact WM |].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from].
      split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { eapply (rw_cells_transport rsegs
                [(Sfr fr + 336, Sfr fr + 365); (sp - 2224, sp); (fr + 2688, fr + 2688 + 38);
                 (fr + 2880, fr + 2880 + 40)]);
        [exact HRWfg | exact MU | exact WM |].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from].
      split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { (* the 72 bytes at fr + 2768 are addressable: their nine shadow bytes S(fr) + 346 .. 354 are 0 *)
      apply (bp_addr_z mem' (fr + 2768) 9 72); [reflexivity | lia
        | replace (fr + 2768) with (fr + 8 * 346) by lia; apply bp_m8; exact Hfrm | lia
        | intros i Hi; apply Happ'; lia |].
      replace (fr + 2768) with (fr + 8 * 346) by lia. rewrite bp_sh8. exact B10. }
    split; [unfold end_in_app; right; apply Happ'; lia|].
    split; [apply Happ'; lia|].
    split; [right; unfold RT_HI; lia|].
    split; [unfold asan_memset_c.ASAN_MEMSET_K; lia|].
    split; [intros x Hx; cbn [LF.outside]; split; [lia | split; [lia | exact I]]|].
    split; [intros x Hx; cbn [LF.outside]; split; [lia | split; [lia | exact I]]|].
    split.
    { intros A0 HA0 HA0r x Hx.
      assert (A0 = A) by (apply (bp_rg_inj regs'' 9 A0 A HA0 ltac:(rewrite E9; exact Hr9) HA0r HA64)). subst A0.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { intros A0 HA0 HA0r x Hx.
      assert (A0 = A) by (apply (bp_rg_inj regs'' 9 A0 A HA0 ltac:(rewrite E9; exact Hr9) HA0r HA64)). subst A0.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [intros x Hx; cbn [LF.outside]; split; [lia | split; [lia | exact I]]|].
    split; [intros x Hx; cbn [LF.outside]; split; [lia | split; [lia | exact I]]|].
    split.
    { intros x Hx. rewrite OUR_length in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { cbn [all_app]. split; [|split; [|exact I]].
      - intros a Ha. apply Happ'. lia.
      - intros a Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
        right. unfold asan_memset_c.ASAN_MEMSET_K in Ha. lia. }
    split.
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, asan_memset_c.ASAN_MEMSET_K.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    split; [reflexivity|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hq64 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split; [exact (bp_fsj0 g fr regs'' mem' HfpZ HAfp) | exact HAfp].
Qed.

End P3.
