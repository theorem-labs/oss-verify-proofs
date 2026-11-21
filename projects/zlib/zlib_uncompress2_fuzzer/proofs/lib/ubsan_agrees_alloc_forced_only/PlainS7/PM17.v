(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM03.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require PM21.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RF_am_K.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. Import MM07.F_am_K.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Lemma rbytes_at_zeros_sub m A n off k :
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m (A + off) (zeros k).
Proof.
  intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

Lemma rrw_cells_of_zeros m A n off cs :
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m A (zeros n) -> wr_at (run_segments psegs rc_inp rc_sp rc_mb) m A (Z.of_nat n) ->
  cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (A + off) cs.
Proof.
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.


Lemma rmrep_set_area_next : forall st m m' a ar p,
  rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
  munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (conc st a) [C8 (wz SECRET); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
  rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof.
  intros st m m' a ar p MR Ha Hp MU WM CH.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  assert (AG : forall A cs, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' A cs).
  { intros A cs H HD. pose proof (rw_cells_bound (run_segments psegs rc_inp rc_sp rc_mb) m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
    intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    unfold rmrep_ctx. change (rctx_head_cells st') with (rctx_head_cells st). change (actives st') with (actives st).
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    change (ctx_tail_cells st') with (ctx_tail_cells st).
    split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
    split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    apply AG; [exact C6| cbn; unfold RCTX; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
    split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia].
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
    destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
      split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
      * apply AG; [exact A3| cbn; lia].
    + rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
      destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
      assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
        - rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
          assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
          Z.div_mod_to_equations. lia.
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
      change (pw st' (a_next ar')) with (pw st (a_next ar')).
      split; [apply AG; [exact A1| cbn; lia]|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
      * apply AG; [exact A3| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
    rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
    cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
    + eapply wr_at_transport; [exact HWr| exact WM].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
      eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); atop_facts; pose proof (round_up_pg_ge (r_len r)); lia).
      assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.


Lemma rmrep_new_area : forall st m (p : aptr) r chk,
  rmrep st m -> (s_areas st) !! p = None ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p) [C8 (wz SECRET); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
  (forall k, 0 <= k < NSLOTS -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (conc st p + 4064) [CB 32 (zeros 32)] ->
  rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof.
  intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
    + exists r. repeat split; assumption.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - exact CX.
  - exact GL.
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
    destruct (decide (a' = p)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
      split; [exact HDR|]. split; [| exact PAD].
      intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
  - exact GR.
  - exact SH.
Qed.


Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
  rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
  0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None ->
  conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof.
  intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). atop_facts.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
    destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
    + rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
      assert (NEo : snd ak <> snd p).
      { intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
      Z.div_mod_to_equations. lia.
    + pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
  - destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
    assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
    pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
    assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
    pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

End CANSEC1.
End RF_am_K.

Module RF_free_C.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM03. Import MM03. Import MM03.F_free_C.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS7 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM21. Import PM21.RF_get_meta. Import PM21.RF_mm_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}. Context {rc : runConstT}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch W m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19594) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP in *. atop_facts. subst tp.
  rewrite (unsigned_lit 470912) in ERR by lia. change (470912 + -164) with 470748 in ERR.
  st1. st1. st1. st1.
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x195a8)) with (Z_to_bv 64 0x195a8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 470912) by lia. change (470912 + -164) with 470748. exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x195c4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -48)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> 0 < len < 2^64 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19594) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP in *. atop_facts. subst tp.
  rewrite (unsigned_lit 470912) in ERR by lia. change (470912 + -164) with 470748 in ERR.
  st1. st1. st1. st1.
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x195a8)) with (Z_to_bv 64 0x195a8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x195b0)) with (Z_to_bv 64 0x195b0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 470912) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 470912) by lia; change (470912 + -164) with 470748; exact ERR| exact MR2].
Qed.

Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 470748 <= a < 470752 -> ~ rrepfoot st a.
Proof.
  intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct C as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (470748, 470752)]%Z m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' -> ATOP <= sp - 48 -> rmrep st m'.
Proof.
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). atop_facts. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). atop_facts. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 e'] ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (470748, 470752)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x195c4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (470748, 470752)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  unfold RATP in *. atop_facts. subst tp.
  rewrite (unsigned_lit 470912) in ERR by lia. change (470912 + -164) with 470748 in ERR.
  rewrite (unsigned_lit 470912) by lia. change (470912 + -164) with 470748.
  st1.
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | atop_facts; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 470912) by lia. change (470912 + -164) with 470748.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End CANSEC1.
End RF_free_C.
