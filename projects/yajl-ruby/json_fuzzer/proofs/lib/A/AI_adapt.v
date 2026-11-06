(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AI_globals2 A_iface AI_iface A_iface5x AI_region_is_poisoned AI_memcpy_icp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> StdioBase.stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Variable aalloc_same : APS -> APS -> Prop.
Notation C := ACONSTS.

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt asegs APS AHK.
Hypothesis Hblocks : AHK_blocks_stmt C APS AHK.
Hypothesis Hframe : AHK_frame_stmt asegs C APS AHK.
Hypothesis Hglob : AHK_icp_globals_stmt asegs APS AHK.
Hypothesis Hbsh : AHK_icp_block_shadow_stmt asegs APS AHK.
Hypothesis Hreg : AHK_icp_regions_stmt APS AHK aS.
Hypothesis Hsame_refl : forall s, aalloc_same s s.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

Lemma amemcpy_icp_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (dst src n lo : Z) (bs junk : list byte) (bd bsr : ablock) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In bd LB -> ab_addr bd <= dst -> dst + n <= ab_addr bd + ab_size bd ->
  In bsr LB -> ab_addr bsr <= src -> src + n <= ab_addr bsr + ab_size bsr ->
  (dst + n <= src \/ src + n <= dst) -> 0 < n < 2^26 ->
  bytes_at asegs m src bs -> Z.of_nat (length bs) = n -> rw_cells asegs m dst [CB (Z.to_nat n) junk] ->
  stk asegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz dst -> a1 = wz src -> a2 = wz n ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk asegs m' lo (usp sp) -> rw_cells asegs m' dst [CB (Z.to_nat n) bs] ->
     munch [(lo, usp sp); (dst, dst + n)] m m' -> wmono asegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_memcpy C)) fc None m (seg_rom asegs)) mo) K.
Proof. aceil.
  intros until K. intros HK0 HA Ibd Hd1 Hd2 Ibs Hs1 Hs2 SEP HN SRC LEN DST ST LOC LO HTP FRM -> -> -> HK.
  cbv beta. unfold AICP_STACK in LO.
  (* [comment removed for export] *)
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Hblocks _ _ _ _ _ HA) as (RNG & DISJ & _).
  pose proof (RNG _ Ibd) as Rd. pose proof (RNG _ Ibs) as Rs. unfold ablock_range in Rd, Rs. cbn [c_img_hi ACONSTS] in Rd, Rs.
  pose proof (Hglob _ _ _ _ _ HA) as G.
  assert (SBR : 2^24 <= C_SB < 2^32) by (unfold C_SB; lia).
  destruct (Hbsh _ _ _ _ _ bd dst n HA Ibd ltac:(lia) ltac:(lia) ltac:(lia)) as (wsD & SWD & RCD & AMD).
  destruct (Hbsh _ _ _ _ _ bsr src n HA Ibs ltac:(lia) ltac:(lia) ltac:(lia)) as (wsS & SWS & RCS & AMS).
  (* [comment removed for export] *)
  pose proof (app_mem_shadow_facts _ _ dst n AMD Hd1 ltac:(lia) Hd2) as (RIMD & SLOD & SHID & _ & SEPD & D47 & Dpos).
  pose proof (app_mem_shadow_facts _ _ src n AMS Hs1 ltac:(lia) Hs2) as (RIMS & SLOS & SHIS & _ & SEPS & S47 & Spos).
  pose proof (SEPS (ab_addr bd) (ab_size bd) AMD ltac:(lia)) as SEP_SD.
  pose proof (SEPD (ab_addr bd) (ab_size bd) AMD ltac:(lia)) as SEP_DD.
  clear SEPS SEPD AMD AMS.
  destruct (Hreg _ _ _ _ _ HA) as (_ & _ & _ & PB).
  aceil.
  unfold C_SB in *.
  eapply (srzA_evt asegs (aS s) (aN s) (aEB s) (m_vm_lazy mo)).
  - (* [comment removed for export] *)
    stepA.
    eapply (memcpy_icp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dst src n 0x7fff8000 bs wsS wsD junk lo).
    all: try reflexivity.
    + exact ST.
    + aceil. lia.
    + lia.
    + exact MI.
    + lia.
    + exact RIMS.
    + exact RIMD.
    + lia. + lia. + lia. + lia. + lia. + lia.
    + exact DST.
    + exact SRC.
    + lia.
    + exact G.
    + exact SWS. + exact RCS. + lia.
    + exact SWD. + exact RCD. + lia.
    + (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    + (* [comment removed for export] *)
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    + intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. right; right. exists bsr. split; [exact Ibs| lia].
    + intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. right; right. exists bd. split; [exact Ibd| lia].
    + pose proof (shw_geom 0x7fff8000 src n ltac:(lia) ltac:(lia) ltac:(lia)) as GS; cbv zeta in GS.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact (PB bsr src n Ibs Hs1 ltac:(lia) Hs2) | lia | lia | lia | lia].
    + pose proof (shw_geom 0x7fff8000 dst n ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact (PB bd dst n Ibd Hd1 ltac:(lia) Hd2) | lia | lia | lia | lia].
  - exact Hh.
  - exact HLI.
  - reflexivity.
  - (* [comment removed for export] *)
    intros ms' mo' Q Hag HLI' Hh'.
    destruct Q as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & DST' & SRC' & G' & SW1 & SW2).
    assert (HA' : AHK s LB LF m' mo).
    { eapply Hframe; [exact HA | exact MU | exact WM |].
      constructor. { unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { unfold aclient_write_ok. cbn [fst snd]. right; left. exists bd. split; [exact Ibd| lia]. }
      constructor. }
    destruct (Hkip _ _ _ _ _ HA') as (_ & _ & _ & _ & MAG').
    pose proof (MAG' mo' Hag HLI') as HA''.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' mo' s).
    + exact ST'.
    + exact DST'.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
    + exact WM.
    + exact FRM.
    + exact HA''.
    + apply Hsame_refl.
    + reflexivity.
    + exact Efs.
    + exact Efds.
    + exact Hag.
Qed.

Lemma amemcpy_icp_ok : amemcpy_icp_stmt asegs C APS AHK SO aalloc_same.
Proof. aceil.
  unfold amemcpy_icp_stmt. intros.
  eapply (amemcpy_icp_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo s LB LF dst src n lo bs junk bd bsr K); eauto.
Qed.

(* [comment removed for export] *)
Hypothesis Hmss : AHK_icp_musl_statics_shadow_stmt asegs APS AHK aS.

Lemma amemcpy_static_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (dst src n lo : Z) (bs junk : list byte) (bd : ablock) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In bd LB -> ab_addr bd <= dst -> dst + n <= ab_addr bd + ab_size bd ->
  A_RSTAGE <= src -> src + n <= A_RSTAGE + A_RSTAGE_LEN -> 0 < n < 2^26 ->
  bytes_at asegs m src bs -> Z.of_nat (length bs) = n -> rw_cells asegs m dst [CB (Z.to_nat n) junk] ->
  stk asegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz dst -> a1 = wz src -> a2 = wz n ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk asegs m' lo (usp sp) -> rw_cells asegs m' dst [CB (Z.to_nat n) bs] ->
     munch [(lo, usp sp); (dst, dst + n)] m m' -> wmono asegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_memcpy C)) fc None m (seg_rom asegs)) mo) K.
Proof. aceil.
  intros until K. intros HK0 HA Ibd Hd1 Hd2 Hs1 Hs2 HN SRC LEN DST ST LOC LO HTP FRM -> -> -> HK.
  cbv beta. unfold AICP_STACK in LO. unfold A_RSTAGE, A_RSTAGE_LEN in Hs1, Hs2.
  (* [comment removed for export] *)
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Hblocks _ _ _ _ _ HA) as (RNG & DISJ & _).
  pose proof (RNG _ Ibd) as Rd. unfold ablock_range in Rd. cbn [c_img_hi ACONSTS] in Rd.
  pose proof (Hglob _ _ _ _ _ HA) as G.
  assert (SBR : 2^24 <= C_SB < 2^32) by (unfold C_SB; lia).
  destruct (Hbsh _ _ _ _ _ bd dst n HA Ibd ltac:(lia) ltac:(lia) ltac:(lia)) as (wsD & SWD & RCD & AMD).
  destruct (Hmss _ _ _ _ _ src n HA ltac:(lia) ltac:(lia) ltac:(lia)) as (wsS & SWS & RCS & PBS).
  pose proof (app_mem_shadow_facts _ _ dst n AMD Hd1 ltac:(lia) Hd2) as (RIMD & SLOD & SHID & _ & SEPD & D47 & Dpos).
  pose proof (img_shadow_facts src n ltac:(lia) ltac:(lia) ltac:(lia)) as (RIMS & SLOS & SHIS & SEPS & S47 & Spos).
  pose proof (SEPS (ab_addr bd) (ab_size bd) AMD ltac:(lia) ltac:(lia)) as SEP_SD.
  pose proof (SEPD (ab_addr bd) (ab_size bd) AMD ltac:(lia)) as SEP_DD.
  clear SEPS SEPD AMD.
  destruct (Hreg _ _ _ _ _ HA) as (_ & _ & _ & PB).
  aceil.
  unfold C_SB in *.
  eapply (srzA_evt asegs (aS s) (aN s) (aEB s) (m_vm_lazy mo)).
  - stepA.
    eapply (memcpy_icp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dst src n 0x7fff8000 bs wsS wsD junk lo).
    all: try reflexivity.
    + exact ST.
    + aceil. lia.
    + lia.
    + exact MI.
    + lia.
    + exact RIMS.
    + exact RIMD.
    + lia. + lia. + lia. + lia. + lia. + lia.
    + exact DST.
    + exact SRC.
    + lia.
    + exact G.
    + exact SWS. + exact RCS. + lia.
    + exact SWD. + exact RCD. + lia.
    + (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    + (* [comment removed for export] *)
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    + (* [comment removed for export] *)
      intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    + intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. right; right. exists bd. split; [exact Ibd| lia].
    + pose proof (shw_geom 0x7fff8000 src n ltac:(lia) ltac:(lia) ltac:(lia)) as GS; cbv zeta in GS.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact PBS | lia | lia | lia | lia].
    + pose proof (shw_geom 0x7fff8000 dst n ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
      intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact (PB bd dst n Ibd Hd1 ltac:(lia) Hd2) | lia | lia | lia | lia].
  - exact Hh.
  - exact HLI.
  - reflexivity.
  - (* [comment removed for export] *)
    intros ms' mo' Q Hag HLI' Hh'.
    destruct Q as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & DST' & SRC' & G' & SW1 & SW2).
    assert (HA' : AHK s LB LF m' mo).
    { eapply Hframe; [exact HA | exact MU | exact WM |].
      constructor. { unfold aclient_write_ok. cbn [fst snd]. left. aceil. lia. }
      constructor. { unfold aclient_write_ok. cbn [fst snd]. right; left. exists bd. split; [exact Ibd| lia]. }
      constructor. }
    destruct (Hkip _ _ _ _ _ HA') as (_ & _ & _ & _ & MAG').
    pose proof (MAG' mo' Hag HLI') as HA''.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' mo' s).
    + exact ST'.
    + exact DST'.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
    + exact WM.
    + exact FRM.
    + exact HA''.
    + apply Hsame_refl.
    + reflexivity.
    + exact Efs.
    + exact Efds.
    + exact Hag.
Qed.

Lemma amemcpy_static_ok : amemcpy_static_rz_stmt asegs C APS AHK SO aalloc_same.
Proof. aceil.
  unfold amemcpy_static_rz_stmt. intros.
  eapply (amemcpy_static_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo s LB LF dst src n lo bs junk bd K); eauto.
Qed.
End Adapt.
End RC__1.
