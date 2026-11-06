(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 866 of its 1005 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R3.v; 104 of its 253 lines of code are new or changed and 856 lines of the source are left out. *)
(* lib/A/Prog/Seg/R3Fon.v -- route (C) twin of Seg/R3F.v's run r3_evt_F (a Theorem Labs lane's file, not edited here; not in this delivery).
   Writer: a Theorem Labs lane's stage lane (Seg *F.v twin rule, a Theorem Labs lane 12:52Z: an ADDITIVE beside-file; R3F.v (not in this delivery) stays
   unedited; its later version differs from the base below only in MState's module qualification).  proves no function (kind: segment lemma; the footprint run of stage R3, 0x8152c-0x81578).

   BASED ON R3F.v (an earlier version, blob 4f46d6492cf, not in this delivery): the same blob on a Theorem Labs lane's fold (from a working branch 4bae33fdf54) and
   on a working branch 1502cba0417 (diff empty), so either is the source.

   WHAT CHANGES against r3_evt_F, and why (measured on R3F.v's proof):
   - the callee premise is reac_identity_init_contract_F_on (a Theorem Labs lane's reac_identity_init_c.v 6efe5449c39, LANDED
     row 11:01Z), whose shadow premise is shadow_rw_on (reac_identity_init_shadow_R id) = (id <> 0 /\ sh_word_on id 38);
   - the universal premise `shadow_rw m` is REMOVED: the run reads no shadow byte, and its fifteen shadow stores take
     their writability from the run's own `rw_cells rsegs m (Sh + 254) (map C1 xs)` premise.  R3F.v used shadow_rw m
     only to hand the callee a universal shadow_rw (r3_shadow_rw at m1, then r3_sw_norm), and the callee's region
     (the 8-aligned shadow-word cover of [idp, idp + 38), inside [Sh + 265, Sh + 284)) lies inside the 37 bytes
     [Sh + 254, Sh + 291) the run has just stored, so it is present and writable at m1 without any shadow premise
     (r3on_cover_stored below);
   - the post's `shadow_rw m'` becomes the wave's transport `forall P, shadow_rw_on P m -> shadow_rw_on P m'`: across
     the stores by r3on_shadow_rw_on (r3_shadow_rw's argument for one region), into the normalized call by
     ShadowRwOnT.shadow_rw_on_normalize, through the callee's own forall-P post, and back by
     ShadowRwOnT.shadow_rw_on_of_rel.
   Every other premise, binder, conjunct and footprint premise is r3_evt_F's, in the same order.  No pin back to
   r3_evt_F (it takes the old contract, so it is not a corollary). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Tac.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRTFacts.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.rng_asan.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R3.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals), as in R3F.v. *)
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Import ListNotations.
Local Open Scope Z_scope.

Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.

(* R3F.v's store tactic (over evtF goals), restated Local. *)
Local Ltac r3on_fix :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (r3_le1_lit z) by lia; mem_after_store
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (r3_le1 v); mem_after_store
  | _ => idtac
  end.
Local Ltac r3on_sb := step; r3on_fix.

(* r3_shadow_rw (Seg/R3.v) for one region P: a byte of P the run did not write keeps its view and value; a byte it
   wrote is read from the new memory. *)
Lemma r3on_shadow_rw_on : forall (P : Z -> Prop) W m m', SRO.shadow_rw_on P m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> SRO.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The callee's region is inside the 37 bytes [Sh + 254, Sh + 291) the run stores: shadow_addr idp = Sh + 272 and
   idp mod 8 = 0 put the 8-aligned shadow-word cover of [idp, idp + 38) in [Sh + 265, Sh + 284). *)
Lemma r3on_cover_in : forall Sh idp a, idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
  RII.reac_identity_init_shadow_R idp a -> Sh + 254 <= a < Sh + 291.
Proof.
  intros Sh idp a H8 Hs (_ & _ & Hlo & Hhi).
  unfold sh_al8_lo, sh_al8_hi, shadow_addr in *. Z.div_mod_to_equations. lia.
Qed.

(* So the callee's region is writable and present once the stores are done: writable at m by the run's own rw_cells
   premise on [Sh + 254, Sh + 291) (wmono carries it to m'), present at m' by the stored bytes. *)
Lemma r3on_cover_stored : forall Sh idp m m' cs, idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
  rw_cells rsegs m (Sh + 254) cs -> Z.of_nat (cells_size cs) = 37 -> wmono rsegs m m' ->
  (forall a, Sh + 254 <= a < Sh + 291 -> exists b, mrd rsegs m' (wa a) = Some b) ->
  SRO.shadow_rw_on (RII.reac_identity_init_shadow_R idp) m'.
Proof.
  intros Sh idp m m' cs H8 Hs (_ & _ & _ & HW) Hn WM HB a HR _.
  pose proof (r3on_cover_in Sh idp a H8 Hs HR) as Ha.
  split; [|exact (HB a Ha)].
  apply WM. replace a with (Sh + 254 + (a - (Sh + 254))) by lia. apply HW. lia.
Qed.

Lemma r3_evt_F_on : RII.reac_identity_init_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh idp lo : Z) (xs idb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s5 = Z_to_bv 64 idp ->
    RT_HI <= Sh -> 6283264 <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv ->
    spv <= APPMEM_END ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> 6283264 <= idp ->
    idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    length xs = 37%nat -> rw_cells rsegs m (Sh + 254) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] ->
    ro_agree rsegs m -> stk rsegs m lo spv -> asan_cells m ->
    ExecF.rng RNG (Sh + 254) 37 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - RII.REAC_IDENTITY_INIT_K) RII.REAC_IDENTITY_INIT_K ->
    sh_word_rng RNG (spv - RII.REAC_IDENTITY_INIT_K) RII.REAC_IDENTITY_INIT_K ->
    ExecF.rng RNG ((spv - RII.REAC_IDENTITY_INIT_K) / 8 + ASAN_K)
                  ((spv - 1) / 8 - (spv - RII.REAC_IDENTITY_INIT_K) / 8 + 1) ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    ExecF.rng RNG idp 38 ->
    ExecF.rng RNG ((idp / 8 + ASAN_K) / 8 * 8)
                  (((idp + 37) / 8 + ASAN_K) / 8 * 8 + 8 - (idp / 8 + ASAN_K) / 8 * 8) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81578) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = s2 /\ getr R 21 = s5 /\
         munch [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\
         (forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m') /\
         rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
         bytes_at rsegs m' (Sh + 254) [Z_to_bv 8 4] /\
         bytes_at rsegs m' (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m' (Sh + 282) (repeat (Z_to_bv 8 0) 9))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8152c) fc None m (seg_rom rsegs)).
Proof.
  intros INIT RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh idp lo xs idb -> -> -> HSrt HShGT HSlo HHM HLO HAE HSid Hidrt HidGT Hid8 Hshid Hidapp Hsep
    Hxs CH RWid HRO ST HAC Rsh Rby Rimg Rwin Rwinw Rwsh Rrt Rid Ridsh.
  unfold RII.reac_identity_init_contract_F_on, RII.REAC_IDENTITY_INIT, RII.REAC_IDENTITY_INIT_K in INIT.
  unfold RII.REAC_IDENTITY_INIT_K in Rwin, Rwinw, Rwsh.
  do 37 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 254) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m idp _ RWid) as Hidb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hidb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  pose proof (Hidapp (idp + 38) ltac:(lia)) as Hidhi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hidhi.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  r3on_sb. r3on_sb. r3on_sb. r3on_sb. r3on_sb.
  r3on_sb. r3on_sb. r3on_sb. r3on_sb. r3on_sb.
  r3on_sb. r3on_sb. r3on_sb. r3on_sb. r3on_sb.
  step. step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  (* every shadow byte the run touches is a stored one: the stored bytes or outside the write set *)
  assert (HST1 : forall a, in_shadow a ->
            outside [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] a \/
            exists b, mrd rsegs m1 (wa a) = Some b).
  { intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 254) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 291)) as [H2|H2]|].
    - right. apply (r3_ba_rd m1 (Sh + 254) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hin. exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha).
    - left. cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hin. exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha). }
  (* the callee's region at m1, with no shadow premise: inside the 37 stored bytes (the store steps carry the run's
     rw_cells premise CH to m1, with the stored values) *)
  assert (HSW1 : SRO.shadow_rw_on (RII.reac_identity_init_shadow_R idp) m1).
  { apply (r3on_cover_stored Sh idp m1 m1 _ Hid8 Hshid CH); [reflexivity | exact (wmono_refl rsegs m1) |].
    intros a Ha. apply (r3_ba_rd m1 (Sh + 254) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HA1a : addressable m1 idp 32).
  { apply (r3_addr_z m1 idp 4 32); [reflexivity | lia | exact Hid8 | unfold APPMEM_END; lia
      | intros i Hi; apply Hidapp; lia |].
    rewrite Hshid. pose proof (r3_ba_sub _ _ _ 18 4 HbC ltac:(cbn [length]; lia)) as H4.
    cbn [firstn skipn] in H4. replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in H4 by lia. exact H4. }
  assert (HA1b : addressable m1 (idp + 32) 6).
  { apply (r3_addr_r m1 (idp + 32) 6 (Z_to_bv 8 6)); [lia | Z.div_mod_to_equations; lia | lia | reflexivity
      | unfold APPMEM_END; lia | intros i Hi; apply Hidapp; lia |].
    rewrite r3_sh_add by lia. rewrite Hshid. change (32 / 8) with 4.
    pose proof (r3_ba_sub _ _ _ 22 1 HbC ltac:(cbn [length]; lia)) as H1.
    cbn [firstn skipn] in H1. replace (Sh + 254 + Z.of_nat 22) with (Sh + 272 + 4) in H1 by lia. exact H1. }
  pose proof (r3_addr_cat m1 idp 32 6 HA1a HA1b) as HA1.
  (* the 15 shadow stores keep ro_agree; the call needs mem_inv, so it runs on the normalized memory *)
  assert (RO1 : ro_agree rsegs m1).
  { apply (r3_ro_munch _ m m1 HRO MU). intros x Hx. apply r3_not_out in Hx.
    apply r3_notro_w. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in *. lia. }
  pose proof (mem_rel_normalize rsegs m1 RO1) as REL1.
  assert (RWidn : rw_cells rsegs (normalize rsegs m1) idp [CB 38 idb]).
  { apply (r3_rw_norm m1 _ idp _ REL1); [|exact RWid].
    intros i Hi. cbn [cells_size csize] in Hi. apply r3_notro. lia. }
  assert (STn : stk rsegs (normalize rsegs m1) lo spv).
  { apply (r3_stk_norm m1 _ lo spv REL1); [|exact ST]. intros x Hx. apply r3_notro. lia. }
  pose proof (r3_ac_norm m1 _ REL1 HAC1) as ACn.
  pose proof (SROT.shadow_rw_on_normalize _ m1 RO1 HSW1) as SWn.
  pose proof (r3_addr_rel m1 _ idp 38 REL1 HA1) as HA1n.
  eapply ExecF.evtF_cut.
  { eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m1 (seg_rom rsegs) RO1).
    eapply INIT with (lo := lo) (id := idp) (idb := idb) (RNG := RNG).
    - reflexivity.
    - lia.
    - intros _. split; [Z.div_mod_to_equations; lia | exact RWidn].
    - apply mem_inv_normalize.
    - rewrite lib.Lib.MState.unsigned_lit by lia. exact STn.
    - rewrite lib.Lib.MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite lib.Lib.MState.unsigned_lit by lia. unfold APPMEM_END. lia.
    - exact ACn.
    - exact SWn.
    - intros _. split; [exact HA1n | right; apply Hidapp; lia].
    - intros _. right. unfold RT_HI. lia.
    - intros _. rewrite lib.Lib.MState.unsigned_lit by lia. exact Hsep.
    - exact Rby.
    - exact Rimg.
    - rewrite lib.Lib.MState.unsigned_lit by lia. exact Rwin.
    - rewrite lib.Lib.MState.unsigned_lit by lia. exact Rwinw.
    - rewrite lib.Lib.MState.unsigned_lit by lia. exact Rwsh.
    - exact Rrt.
    - intros _. split; [exact Rid | exact Ridsh]. }
  intros ms' (s0' & PO & MR & RS).
  unfold RII.reac_identity_init_post_on, RII.reac_identity_init_W, RII.REAC_IDENTITY_INIT_K,
    RII.REAC_IDENTITY_INIT_FRAME in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & HZ).
  subst s0'.
  specialize (HZ ltac:(lia)).
  rewrite lib.Lib.MState.unsigned_lit in MU2, ST2 by lia.
  (* back to the real memory: ms_rel relates it to the normalized run's, ro_same keeps the image bytes *)
  replace (ret_pc (Z_to_bv 64 0x81578)) with (Z_to_bv 64 0x81578) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' m' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  pose proof (ro_agree_same rsegs m1 m' RO1 RS) as RO2.
  pose proof (munch_rel rsegs _ m1 (normalize rsegs m1) m' m0' REL1 Hmem RS MU2) as MU2r.
  pose proof (wmono_rel rsegs m1 (normalize rsegs m1) m' m0' REL1 Hmem RS WM2) as WM2r.
  pose proof (r3_stk_back m' m0' lo spv Hmem ST2) as ST2r.
  pose proof (r3_ac_back m' m0' Hmem AC2) as AC2r.
  pose proof (r3_rw_back m' m0' idp _ Hmem HZ) as HZr.
  (* the region transport, end to end: stores, normalization, the callee's forall-P post, back *)
  assert (SW2r : forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m').
  { intros P HP.
    pose proof (r3on_shadow_rw_on P _ m m1 HP MU WM HST1) as HP1.
    exact (SROT.shadow_rw_on_of_rel P m' m0' Hmem (SW2 P (SROT.shadow_rw_on_normalize P m1 RO1 HP1))). }
  clear MU2 WM2 MI2 ST2 AC2 SW2 HZ.
  rename MU2r into MU2. rename WM2r into WM2. rename ST2r into ST2. rename AC2r into AC2.
  rename HZr into HZ.
  assert (Hsub : sub_fp [(spv - 2224, spv); (idp, idp + 38)]
                   [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (Hdj : forall k n, 0 <= k -> k + n <= 37 ->
            disjoint_from [(spv - 2224, spv); (idp, idp + 38)] (Sh + 254 + k) n).
  { intros k n Hk Hkn. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  pose proof (r3_ba_sub _ _ _ 0 1 HbC ltac:(cbn [length]; lia)) as B0.
  pose proof (r3_ba_sub _ _ _ 18 5 HbC ltac:(cbn [length]; lia)) as B18.
  pose proof (r3_ba_sub _ _ _ 28 9 HbC ltac:(cbn [length]; lia)) as B28.
  cbn [firstn skipn] in B0, B18, B28.
  replace (Sh + 254 + Z.of_nat 0) with (Sh + 254) in B0 by lia.
  replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in B18 by lia.
  replace (Sh + 254 + Z.of_nat 28) with (Sh + 282) in B28 by lia.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B0 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 254) with (Sh + 254 + 0) by lia; apply Hdj; lia)) as B0'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B18 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 272) with (Sh + 254 + 18) by lia; apply Hdj; lia)) as B18'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B28 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 282) with (Sh + 254 + 28) by lia; apply Hdj; lia)) as B28'.
  subst R'.
  apply ExecF.evtF_done. do 2 eexists. split; [unfold MS; subst; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact RO2|]. split; [exact ST2|]. split; [exact AC2|]. split; [exact SW2r|].
  split; [exact HZ|]. split; [exact B0'|]. split; [exact B18' | exact B28'].
Qed.
