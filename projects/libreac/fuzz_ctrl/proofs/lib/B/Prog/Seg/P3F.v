(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module paths, module names, addresses and numbers changed; 357 of its 406 lines of code are new or changed and 881 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P3.v p3_evt at a working branch 3803efccea0
     (blob a5b65d45f85c073e03ca358c6b19b3eee607c3b6);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p3_evt_of_F composes p3_pre_F, the caller's asan_memset_contract premise, p3_pre2_F, the caller's
     reac_identity_init_contract premise and p3_post2_F, and re-derives the source statement of P3.p3_evt
     verbatim; p3_evt_same checks that type against P3.p3_evt.  p3_pre_F re-runs P3.v lines 98-105
     (0x81cb0 .. 0x81d0c, up to the first callee entry), p3_pre2_F line 188 (the first return pc 0x81d10 up to
     the second callee entry), p3_post2_F lines 204-239 (the second return pc 0x81d18, no instruction left). *)
(* rule 24: no function proved. *)
(* The footprint twin of P3's run [0x81cb0, 0x81d18), split at BOTH calls (parent ruling: every call splits):
     the 19 frame-shadow stores, li a2,40, ld a0,168(s1), li a1,0, jal checked_memset
       -> p3_pre_F, stops AT the first callee entry 0x52600 with ra = 0x81d10;
     ld a0,176(s1), jal reac_identity_init
       -> p3_pre2_F, stops AT the second callee entry 0x87de8 with ra = 0x81d18;
     the return pc 0x81d18 -> p3_post2_F, no step left.
   Regions of the two stretches: the 29 frame-shadow bytes [Sh + 336, Sh + 365) (written), the `first`
   pointer [Ab + 168, Ab + 176) (read) and the identity-record pointer [Ab + 176, Ab + 184) (read).  No
   instrumented check in either stretch; the id bytes, `first`'s bytes and the callees' stack window are the
   callees' own footprints and appear only in the post facts. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane): p3_pre_F_on is p3_pre_F with the
   universal premise `shadow_rw m` DROPPED and the post conjunct `shadow_rw m1` replaced by the transport
   `forall P, shadow_rw_on P m -> shadow_rw_on P m1` (every region: the stretch writes only the 29 frame-shadow bytes
   [Sh + 336, Sh + 365), and those are present in m1).  Measured from the stretch's proof: the 19 frame-shadow stores
   go through the rw_cells premise (rng (Sh + 336) 29) and the `first` pointer load through the ro_cells premise
   (rng (Ab + 168) 8); the post's addressable facts for idp / fp come from the stored bytes; the shadow premise was
   used only to rebuild the post's `shadow_rw m1`, so the stretch reads and stores no shadow byte through it.
   p3_pre_F keeps its statement, as a corollary (the post with P := fun _ => True). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_init_c asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.
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
Lemma p3_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- 0x81cb0 .. 0x81d0c, route (C): no shadow premise; the post transports every shadow_rw_on region ---- *)
Lemma p3_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp fp lo : Z)
         (xs idb fpb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 184 <= 2 ^ 64 -> spv <= Ab -> fp + 40 <= Ab ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 336 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (Sh + 392 <= fp \/ fp + 40 <= Sh) -> RT_HI <= fp -> fp mod 8 = 0 -> shadow_addr fp = Sh + 360 ->
    (forall a, fp <= a <= fp + 40 -> app_mem a) ->
    length xs = 29%nat -> rw_cells rsegs m (Sh + 336) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> rw_cells rsegs m fp [CB 40 fpb] ->
    ro_cells rsegs m (Ab + 168) [C8 (Z_to_bv 64 fp)] -> ro_cells rsegs m (Ab + 176) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m ->
    rng RNG (Sh + 336) 29 -> rng RNG (Ab + 168) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81d10) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 Ab)
                       (Z_to_bv 64 fp) (Z_to_bv 64 0) (Z_to_bv 64 40) a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 Sh) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x52600) fc None m1 (seg_rom rsegs) /\
         munch [(Sh + 336, Sh + 365)] m m1 /\ wmono rsegs m m1 /\
         mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1) /\
         rw_cells rsegs m1 fp [CB 40 fpb] /\ addressable m1 fp 40 /\
         rw_cells rsegs m1 idp [CB 38 idb] /\ addressable m1 idp 38 /\
         ro_cells rsegs m1 (Ab + 176) [C8 (Z_to_bv 64 idp)] /\
         bytes_at rsegs m1 (Sh + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m1 (Sh + 346) (repeat (Z_to_bv 8 0) 9) /\
         bytes_at rsegs m1 (Sh + 360) (repeat (Z_to_bv 8 0) 5))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp fp lo xs idb fpb -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HspAb HfpAb HSid Hidrt Hid8
    Hshid Hidapp HSfp Hfprt Hfp8 Hshfp Hfpapp Hxs CH RWid RWfp RO168 RO176 HMI ST HAC GS GA.
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
  pose proof (munch_refl [(Sh + 336, Sh + 365)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  step.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  bp_sbF.
  bp_sbF. bp_sbF. bp_sbF.
  bp_sbF. bp_sbF. bp_sbF.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (p3_srw_on_munch P _ m m1 HP MU WM). intros a Ha.
    destruct (Z_le_gt_dec (Sh + 336) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 365)) as [H2|H2]|].
    - right. apply (bp_ba_rd m1 (Sh + 336) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
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
  apply evtF_done.
  do 12 eexists. exists m1.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|]. split; [exact ST|].
  split; [exact HAC1|]. split; [exact HSW1|]. split; [exact RWfp|]. split; [exact HAfp|].
  split; [exact RWid|]. split; [exact HA1|]. split; [exact RO176|].
  split; [exact B0|]. split; [exact B10 | exact B24].
Qed.

(* ---- 0x81cb0 .. 0x81d0c: the 19 shadow stores; li a2,40; ld a0,168(s1); li a1,0; jal checked_memset ---- *)
Lemma p3_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp fp lo : Z)
         (xs idb fpb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 184 <= 2 ^ 64 -> spv <= Ab -> fp + 40 <= Ab ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 336 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (Sh + 392 <= fp \/ fp + 40 <= Sh) -> RT_HI <= fp -> fp mod 8 = 0 -> shadow_addr fp = Sh + 360 ->
    (forall a, fp <= a <= fp + 40 -> app_mem a) ->
    length xs = 29%nat -> rw_cells rsegs m (Sh + 336) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> rw_cells rsegs m fp [CB 40 fpb] ->
    ro_cells rsegs m (Ab + 168) [C8 (Z_to_bv 64 fp)] -> ro_cells rsegs m (Ab + 176) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 336) 29 -> rng RNG (Ab + 168) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81d10) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 Ab)
                       (Z_to_bv 64 fp) (Z_to_bv 64 0) (Z_to_bv 64 40) a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 Sh) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x52600) fc None m1 (seg_rom rsegs) /\
         munch [(Sh + 336, Sh + 365)] m m1 /\ wmono rsegs m m1 /\
         mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\ shadow_rw m1 /\
         rw_cells rsegs m1 fp [CB 40 fpb] /\ addressable m1 fp 40 /\
         rw_cells rsegs m1 idp [CB 38 idb] /\ addressable m1 idp 38 /\
         ro_cells rsegs m1 (Ab + 176) [C8 (Z_to_bv 64 idp)] /\
         bytes_at rsegs m1 (Sh + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m1 (Sh + 346) (repeat (Z_to_bv 8 0) 9) /\
         bytes_at rsegs m1 (Sh + 360) (repeat (Z_to_bv 8 0) 5))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81cb0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp fp lo xs idb fpb Hsp Hs3 Hs1 HSrt HSlo HHM HLO HAE HSA HA64 HspAb HfpAb HSid Hidrt Hid8
    Hshid Hidapp HSfp Hfprt Hfp8 Hshfp Hfpapp Hxs CH RWid RWfp RO168 RO176 HMI ST HAC HSW GS GA.
  refine (evtF_mono rsegs RNG _ _ _
            (p3_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m spv Sh Ab idp fp lo xs idb fpb Hsp Hs3 Hs1 HSrt HSlo HHM HLO HAE HSA HA64 HspAb
               HfpAb HSid Hidrt Hid8 Hshid Hidapp HSfp Hfprt Hfp8 Hshfp Hfpapp Hxs CH RWid RWfp RO168 RO176 HMI ST
               HAC GS GA) _).
  intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU & WM & MI & ST1 & AC & SW & K).
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m1.
  exact (conj E (conj MU (conj WM (conj MI (conj ST1 (conj AC
           (conj (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))) K))))))).
Qed.

(* ---- the first return pc 0x81d10 .. 0x81d14: ld a0,176(s1); jal reac_identity_init ---- *)
Lemma p3_pre2_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m2 : word -> option byte) (Ab idp : Z),
    s1 = Z_to_bv 64 Ab ->
    0 <= Ab -> Ab + 184 <= 2 ^ 64 -> 0 <= idp < 2 ^ 64 ->
    ro_cells rsegs m2 (Ab + 176) [C8 (Z_to_bv 64 idp)] ->
    rng RNG (Ab + 176) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81d18) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                                (Z_to_bv 64 idp) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x87de8) fc None m2 (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d10) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m2 Ab idp -> HA0 HA64 Hid RO176 GA.
  step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the second return pc 0x81d18: the premises are the two callees' post facts and the facts the run's
       own stretches left ---- *)
Lemma p3_post2_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 m2 m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s8 s9 s10 : word)
         (spv Sh idp fp lo : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 26 = s10 -> getr R 24 = s8 -> getr R 23 = s7 -> getr R 25 = s9 ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    (Sh + 392 <= fp \/ fp + 40 <= Sh) -> RT_HI <= fp ->
    (fp + 40 <= spv - 2224 \/ spv <= fp) -> (idp + 38 <= fp \/ fp + 40 <= idp) ->
    munch [(Sh + 336, Sh + 365)] m m1 -> wmono rsegs m m1 ->
    munch [(fp, fp + 40); (spv - 2208, spv)] m1 m2 -> wmono rsegs m1 m2 ->
    rw_cells rsegs m2 fp [CB 40 (repeat (Z_to_bv 8 0) 40)] ->
    bytes_at rsegs m2 (Sh + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
    bytes_at rsegs m2 (Sh + 346) (repeat (Z_to_bv 8 0) 9) ->
    bytes_at rsegs m2 (Sh + 360) (repeat (Z_to_bv 8 0) 5) ->
    munch [(spv - 2224, spv); (idp, idp + 38)] m2 m' -> wmono rsegs m2 m' ->
    mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' -> shadow_rw m' ->
    rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81d18) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 26 = s10 /\ getr R' 24 = s8 /\ getr R' 23 = s7 /\ getr R' 25 = s9 /\
         munch [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)] m m'' /\
         wmono rsegs m m'' /\
         mem_inv rsegs m'' /\ stk rsegs m'' lo spv /\ asan_cells m'' /\ shadow_rw m'' /\
         rw_cells rsegs m'' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
         rw_cells rsegs m'' fp [CB 40 (repeat (Z_to_bv 8 0) 40)] /\
         bytes_at rsegs m'' (Sh + 336) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m'' (Sh + 346) (repeat (Z_to_bv 8 0) 9) /\
         bytes_at rsegs m'' (Sh + 360) (repeat (Z_to_bv 8 0) 5))
      (MS R F (Z_to_bv 64 0x81d18) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m1 m2 m' sp gp tp s0 s1 s3 s7 s8 s9 s10 spv Sh idp fp lo
    K2 K3 K4 K8 K9 K19 K26 K24 K23 K25
    HSrt HSlo HHM HLO HAE HSid Hidrt Hsep HSfp Hfprt Hsepf Hidfp
    MU1 WM MU2 WM2 RW2 B0m B10m B24m MU3 WM3 MI3 ST3 AC3 SW3 HZ.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (Hdj3 : forall a n, (a + n <= spv - 2224 \/ spv <= a) -> (a + n <= idp \/ idp + 38 <= a) ->
            disjoint_from [(spv - 2224, spv); (idp, idp + 38)] a n).
  { intros a n Ha1 Ha2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (Hsub1 : sub_fp [(Sh + 336, Sh + 365)]
                    [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  assert (Hsub2 : sub_fp [(fp, fp + 40); (spv - 2208, spv)]
                    [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. lia. }
  assert (Hsub3 : sub_fp [(spv - 2224, spv); (idp, idp + 38)]
                    [(Sh + 336, Sh + 365); (spv - 2224, spv); (idp, idp + 38); (fp, fp + 40)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m2 (munch_weaken _ _ m m1 Hsub1 MU1)
                (munch_weaken _ _ m1 m2 Hsub2 MU2)) as MU12.
  pose proof (munch_trans _ m m2 m' MU12 (munch_weaken _ _ m2 m' Hsub3 MU3)) as MUf.
  pose proof (rw_cells_transport rsegs _ m2 m' _ _ RW2 MU3 WM3
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as RWfpf.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B0m MU3
    ltac:(rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B0'.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B10m MU3
    ltac:(rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B10'.
  pose proof (bytes_at_transport rsegs _ m2 m' _ _ B24m MU3
    ltac:(rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj3; lia)) as B24'.
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K24|]. split; [exact K23|]. split; [exact K25|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m2 m' (wmono_trans rsegs m m1 m2 WM WM2) WM3)|].
  split; [exact MI3|]. split; [exact ST3|]. split; [exact AC3|]. split; [exact SW3|].
  split; [exact HZ|]. split; [exact RWfpf|]. split; [exact B0'|]. split; [exact B10' | exact B24'].
Qed.

(* ---- the compare lemma: the source statement of P3.p3_evt ---- *)
Lemma p3_evt_of_F : MSC.asan_memset_contract -> RII.reac_identity_init_contract ->
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
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p3_pre_F with (spv := spv) (Sh := Sh) (Ab := Ab) (idp := idp) (fp := fp) (lo := lo)
      (xs := xs) (idb := idb) (fpb := fpb); try reflexivity; try assumption;
      apply rng_all; unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *; lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MU1 & WM & MI1 & ST1 & AC1 & SW1 & RWfp1 & HAfp & RWid1 & HA1 & RO176' & B0 & B10 & B24).
  subst ms'.
  pose proof (Hidapp (idp + 38) ltac:(lia)) as Hidhi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hidhi.
  pose proof (Hfpapp (fp + 40) ltac:(lia)) as Hfphi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hfphi.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (EU1 : bv_unsigned (Z_to_bv 64 fp) = fp) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  eapply evt_cut.
  { eapply MSET with (junk := fpb) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 40)) with 40.
    - exact RWfp1.
    - lia.
    - exact HAfp.
    - unfold end_in_app. right. apply Hfpapp. lia.
    - right. apply Hfpapp. lia.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST1.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact AC1.
    - exact SW1.
    - exact MI1. }
  intros ms2 PO2. unfold MSC.asan_memset_post in PO2.
  destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2 &
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
  assert (Hdj2 : forall a n, (a + n <= fp \/ fp + 40 <= a) -> (a + n <= spv - 2208 \/ spv <= a) ->
            disjoint_from [(fp, fp + 40); (spv - 2208, spv)] a n).
  { intros a n Ha1 Ha2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  pose proof (ro_cells_transport rsegs _ m1 m2 _ _ RO176' MU2
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as RO176m.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ RWid1 MU2 WM2
    ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as RWid2.
  assert (HA2 : addressable m2 idp 38).
  { apply (bp_addr_keep _ m1 m2 idp 38 HA1 MU2). intros i Hi.
    rewrite (bp_sh_add idp i Hid8 ltac:(lia)), Hshid.
    assert (Hq : 0 <= i / 8 < 5) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B0 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B0m.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B10 MU2
    ltac:(rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B10m.
  pose proof (bytes_at_transport rsegs _ m1 m2 _ _ B24 MU2
    ltac:(rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; apply Hdj2; lia)) as B24m.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p3_pre2_F with (Ab := Ab) (idp := idp); try reflexivity; try assumption; try lia.
    apply rng_all; lia. }
  intros ms' ->.
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
  destruct PO as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 &
                  m' & E & MU3 & WM3 & MI3 & ST3 & AC3 & SW3 & _ & HZ).
  subst ms'.
  specialize (HZ ltac:(lia)).
  rewrite MState.unsigned_lit in MU3, ST3 by lia.
  replace (ret_pc (Z_to_bv 64 0x81d18)) with (Z_to_bv 64 0x81d18)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p3_post2_F with (m := m) (m1 := m1) (m2 := m2) (spv := spv) (Sh := Sh) (idp := idp) (fp := fp)
    (lo := lo); try reflexivity; try assumption;
    try (unfold RT_HI, HIGHMEM_BEG, APPMEM_END; lia).
Qed.

(* p3_evt_of_F has exactly the statement of the source lemma P3.p3_evt. *)
Definition p3_evt_same : ltac:(let T := type of P3.p3_evt in exact T) := p3_evt_of_F.
