(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8t.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gctH_keep_P : forall segs t (mem M' : word -> option byte) (sp tp tsdp tctx thr : word) (P : Z -> Prop),
  gctH segs t mem sp tp tsdp tctx thr ->
  (forall x : word, P (U x) -> M' x = mem x) -> mem_grows mem M' ->
  (forall z, U (gt_tsd t) <= z < U (gt_tsd t) + 8 -> P z) ->
  (forall z, U tp - 88 <= z < U tp - 80 -> P z) ->
  (forall z, U tsdp <= z < U tsdp + 8 -> P z) ->
  (forall z, U tctx + 152 <= z < U tctx + 160 -> P z) ->
  gctH segs t M' sp tp tsdp tctx thr.
Proof.
  intros segs t mem M' sp tp tsdp tctx thr P [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] HM GR O1 O2 O3 O4.
  pose proof (u64_range tp). pose proof (u64_range tsdp). pose proof (u64_range tctx). pose proof (u64_range (gt_tsd t)). pose proof (u64_range sp).
  split; try assumption.
  - rewrite <- Rf. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM, O1; cbn in Hx; lia].
  - rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM, O1; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rt. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM, O2; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - rewrite <- Rc. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; apply HM, O3; cbn in Hx; lia].
  - rewrite <- Rth. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM, O4; rewrite at_u in Hx by lia; cbn in Hx; lia].
  - eapply store_ok_mono; [exact GR | exact SOK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition psfill (M : word -> option byte) (fsp ra s0 s1 s2 s3 s4 s5 : word) (slot : Z) : word -> option byte :=
  wbytes (ps_frame M fsp ra s0 s1 s2 s3 s4 s5)
         (Z_to_bv 64 (shad (Z_to_bv 64 slot))) (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (2 ^ 18))))).

Lemma psfill_shad : forall slot, 0 <= slot < 2 ^ 63 ->
  shad (Z_to_bv 64 slot) = slot / 8 + 0x7fff8000 /\ shlen (Z_to_bv 64 (2 ^ 18)) = 2 ^ 15
  /\ U (Z_to_bv 64 (shad (Z_to_bv 64 slot))) = slot / 8 + 0x7fff8000.
Proof.
  intros slot Hs. (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia.
  assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split; [reflexivity|]. split; [reflexivity|]. rewrite u_Z2bv by lia. reflexivity.
Qed.

Lemma psfill_outside : forall M (fsp ra s0 s1 s2 s3 s4 s5 : word) slot (x : word), 64 <= U fsp -> 0 <= slot < 2 ^ 63 ->
  (U x < U fsp - 64 \/ U fsp <= U x) -> (U x < slot / 8 + 0x7fff8000 \/ slot / 8 + 0x7fff8000 + 2 ^ 15 <= U x) ->
  psfill M fsp ra s0 s1 s2 s3 s4 s5 slot x = M x.
Proof.
  intros M fsp ra s0 s1 s2 s3 s4 s5 slot x Hsp Hs Hx Hx2. pose proof (u64_range fsp) as Hspr.
  destruct (psfill_shad slot Hs) as (E1 & E2 & E3).
  assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (lazymatch goal with |- ?G => let G' := eval unfold psfill in G in change_no_check G' end). rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite repeat_length, E2, E3; lia | rewrite repeat_length, E2, E3; lia].
  (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.

Lemma psfill_grows : forall M (fsp ra s0 s1 s2 s3 s4 s5 : word) slot, mem_grows M (psfill M fsp ra s0 s1 s2 s3 s4 s5 slot).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold psfill, ps_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

Lemma psfill_mrestrict : forall (Hd : word -> bool) M (fsp ra s0 s1 s2 s3 s4 s5 : word) slot, 64 <= U fsp -> 0 <= slot < 2 ^ 63 ->
  hid_off Hd (U fsp - 64) 64 -> hid_off Hd (slot / 8 + 0x7fff8000) (2 ^ 15) ->
  psfill (mrestrict Hd M) fsp ra s0 s1 s2 s3 s4 s5 slot = mrestrict Hd (psfill M fsp ra s0 s1 s2 s3 s4 s5 slot).
Proof.
  intros Hd M fsp ra s0 s1 s2 s3 s4 s5 slot Hsp Hs HOFF HOFF2. pose proof (u64_range fsp).
  destruct (psfill_shad slot Hs) as (E1 & E2 & E3).
  assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (lazymatch goal with |- ?G => let G' := eval unfold psfill in G in change_no_check G' end).
  assert (L : Z.of_nat (length (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (2 ^ 18)))))) = 2 ^ 15) by (rewrite repeat_length, E2; lia).
  set (bs := repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (2 ^ 18))))) in *.
  rewrite (ps_frame_mrestrict Hd M fsp ra s0 s1 s2 s3 s4 s5) by (first [lia | exact HOFF]).
  apply wbytes_mrestrict; rewrite L, E3; [lia | intros x Hx; apply HOFF2; lia].
Qed.

(* [comment removed for export] *)
Definition gts2 (M : word -> option byte) (fsp v1 v2 : word) : word -> option byte :=
  wbytes (wbytes M (at_ fsp (-8)) (LE8 v1)) (at_ fsp (-24)) (LE8 v2).
Lemma gts2_outside : forall M (fsp v1 v2 x : word), 64 <= U fsp -> (U x < U fsp - 24 \/ U fsp <= U x) -> gts2 M fsp v1 v2 x = M x.
Proof.
  intros M fsp v1 v2 x Hsp Hx. pose proof (u64_range fsp). (lazymatch goal with |- ?G => let G' := eval unfold gts2 in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.
Lemma gts2_grows : forall M (fsp v1 v2 : word), mem_grows M (gts2 M fsp v1 v2).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold gts2 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma gts2_mrestrict : forall (Hd : word -> bool) M (fsp v1 v2 : word), 64 <= U fsp -> hid_off Hd (U fsp - 64) 64 ->
  gts2 (mrestrict Hd M) fsp v1 v2 = mrestrict Hd (gts2 M fsp v1 v2).
Proof.
  intros Hd M fsp v1 v2 Hsp HOFF. pose proof (u64_range fsp). (lazymatch goal with |- ?G => let G' := eval unfold gts2 in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | intros x Hx; apply HOFF; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pf_ms_outside : forall M (thr : word) RIz mu (v72 v80 vst x : word), U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  (U x < U thr + 2792 \/ U thr + 2800 <= U x) -> (U x < U thr + 2872 \/ U thr + 2888 <= U x) -> (U x < RIz + 48 \/ RIz + 56 <= U x) ->
  pf_ms M thr RIz mu v72 v80 vst x = M x.
Proof.
  intros M thr RIz mu v72 v80 vst x HT HR0 HR1 X1 X2 X3. pose proof (u64_range thr). (lazymatch goal with |- ?G => let G' := eval unfold pf_ms in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.
Lemma pf_ms_grows : forall M (thr : word) RIz mu (v72 v80 vst : word), mem_grows M (pf_ms M thr RIz mu v72 v80 vst).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold pf_ms in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma pf_ms_mrestrict : forall (Hd : word -> bool) M (thr : word) RIz mu (v72 v80 vst : word), U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  hid_off Hd (U thr) 4096 -> hid_off Hd RIz 128 ->
  pf_ms (mrestrict Hd M) thr RIz mu v72 v80 vst = mrestrict Hd (pf_ms M thr RIz mu v72 v80 vst).
Proof.
  intros Hd M thr RIz mu v72 v80 vst HT HR0 HR1 HO1 HO2. pose proof (u64_range thr). (lazymatch goal with |- ?G => let G' := eval unfold pf_ms in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
    first [lia | intros x Hx; apply HO1; lia | intros x Hx; apply HO2; lia].
Qed.

Lemma efs_ms_outside : forall M (thr : word) RIz mfa (v72 v80 x : word), U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  (U x < U thr + 2872 \/ U thr + 2888 <= U x) -> (U x < RIz + 24 \/ RIz + 32 <= U x) ->
  efs_ms M thr RIz mfa v72 v80 x = M x.
Proof.
  intros M thr RIz mfa v72 v80 x HT HR0 HR1 X2 X3. pose proof (u64_range thr). (lazymatch goal with |- ?G => let G' := eval unfold efs_ms in G in change_no_check G' end).
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
  reflexivity.
Qed.
Lemma efs_ms_grows : forall M (thr : word) RIz mfa (v72 v80 : word), mem_grows M (efs_ms M thr RIz mfa v72 v80).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold efs_ms in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma efs_ms_mrestrict : forall (Hd : word -> bool) M (thr : word) RIz mfa (v72 v80 : word), U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  hid_off Hd (U thr) 4096 -> hid_off Hd RIz 128 ->
  efs_ms (mrestrict Hd M) thr RIz mfa v72 v80 = mrestrict Hd (efs_ms M thr RIz mfa v72 v80).
Proof.
  intros Hd M thr RIz mfa v72 v80 HT HR0 HR1 HO1 HO2. pose proof (u64_range thr). (lazymatch goal with |- ?G => let G' := eval unfold efs_ms in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
    first [lia | intros x Hx; apply HO1; lia | intros x Hx; apply HO2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pam_1_eq : forall M sp stats RIz SPB c slot,
  pam_1 M sp stats RIz SPB c slot
  = psfill M (at_ sp (-64)) (Z_to_bv 64 0x50f10) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
           (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) slot.
Proof. reflexivity. Qed.
Lemma pam_2_eq : forall M sp stats RIz SPB c slot,
  pam_2 M sp stats RIz SPB c slot = gts2 (pam_1 M sp stats RIz SPB c slot) (at_ sp (-64)) (at_ ARB 0x50f14) (at_ ARB 0x77594).
Proof. reflexivity. Qed.
Lemma eam_1_eq : forall M sp s4x s5x RIz slot mfa,
  eam_1 M sp s4x s5x RIz slot mfa
  = psfill M (at_ sp (-48)) (Z_to_bv 64 0x4eb54) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4x s5x slot.
Proof. reflexivity. Qed.
Lemma eam_2_eq : forall M sp s4x s5x RIz slot mfa,
  eam_2 M sp s4x s5x RIz slot mfa = gts2 (eam_1 M sp s4x s5x RIz slot mfa) (at_ sp (-48)) (at_ ARB 0x4eb58) (at_ ARB 0x77594).
Proof. reflexivity. Qed.

Section PAM.
  Variables (M : word -> option byte) (sp thr v72 v80 vst : word) (RIz SPB c slot mu : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  #[local] Abbreviation stats := (at_ thr 2768).
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma pam_1_outside : forall x : word, (U x < U sp - 128 \/ U sp - 64 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    pam_1 M sp stats RIz SPB c slot x = M x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp). rewrite pam_1_eq. apply psfill_outside; rewrite ?at_u by lia; first [lia | exact X2].
  Qed.
  Lemma pam_2_outside : forall x : word, (U x < U sp - 128 \/ U sp - 64 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    pam_2 M sp stats RIz SPB c slot x = M x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp). rewrite pam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). apply pam_1_outside; assumption.
  Qed.
  Lemma pam_3_outside : forall x : word, U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
    (U x < U sp - 128 \/ U sp - 64 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    (U x < U thr + 2792 \/ U thr + 2800 <= U x) -> (U x < U thr + 2872 \/ U thr + 2888 <= U x) -> (U x < RIz + 48 \/ RIz + 56 <= U x) ->
    pam_3 M sp thr v72 v80 vst RIz SPB c slot mu x = M x.
  Proof using Hslot Hsp.
    intros x HT HR0 HR1 X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold pam_3 in G in change_no_check G' end). rewrite pf_ms_outside by assumption. apply pam_2_outside; assumption.
  Qed.
  Lemma pam_1_grows : mem_grows M (pam_1 M sp stats RIz SPB c slot).
  Proof using. rewrite pam_1_eq. apply psfill_grows. Qed.
  Lemma pam_2_grows : mem_grows M (pam_2 M sp stats RIz SPB c slot).
  Proof using. rewrite pam_2_eq. eapply mem_grows_trans; [apply pam_1_grows | apply gts2_grows]. Qed.
  Lemma pam_3_grows : mem_grows M (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold pam_3 in G in change_no_check G' end). eapply mem_grows_trans; [apply pam_2_grows | apply pf_ms_grows]. Qed.

  Lemma pam_3_mrestrict : forall Hd : word -> bool, U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
    hid_off Hd (U sp - 128) 64 -> hid_off Hd SH (2 ^ 15) -> hid_off Hd (U thr) 4096 -> hid_off Hd RIz 128 ->
    pam_3 (mrestrict Hd M) sp thr v72 v80 vst RIz SPB c slot mu = mrestrict Hd (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu).
  Proof using Hslot Hsp.
    intros Hd HT HR0 HR1 O1 O2 O3 O4. pose proof (u64_range sp).
    assert (E1' : pam_1 (mrestrict Hd M) sp stats RIz SPB c slot = mrestrict Hd (pam_1 M sp stats RIz SPB c slot)).
    { rewrite !pam_1_eq. apply psfill_mrestrict; rewrite ?at_u by lia; first [lia | exact O2 | intros x Hx; apply O1; lia]. }
    assert (E2' : pam_2 (mrestrict Hd M) sp stats RIz SPB c slot = mrestrict Hd (pam_2 M sp stats RIz SPB c slot)).
    { (lazymatch goal with |- ?G => let G' := eval unfold pam_2 in G in change_no_check G' end). rewrite E1'. apply gts2_mrestrict; rewrite ?at_u by lia; first [lia | intros x Hx; apply O1; lia]. }
    (lazymatch goal with |- ?G => let G' := eval unfold pam_3 in G in change_no_check G' end). rewrite E2'. apply pf_ms_mrestrict; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma pam_1_gctH : forall segs t (tp tsdp tctx thr' : word),
    gctH segs t M (at_ (at_ sp (-64)) (-16)) tp tsdp tctx thr' ->
    (U (gt_tsd t) + 8 <= U sp - 128 /\ U tp - 80 <= U sp - 128 /\ U tsdp + 8 <= U sp - 128 /\ U tctx + 160 <= U sp - 128) ->
    (U (gt_tsd t) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd t)) ->
    (U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88) ->
    (U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp) ->
    (U tctx + 160 <= SH \/ SH + 2 ^ 15 <= U tctx + 152) ->
    gctH segs t (pam_1 M sp stats RIz SPB c slot) (at_ (at_ sp (-64)) (-16)) tp tsdp tctx thr'.
  Proof using Hslot Hsp.
    intros segs t tp tsdp tctx thr' GH (B1 & B2 & B3 & B4) O1 O2 O3 O4. pose proof (u64_range sp).
    apply (gctH_keep_P segs t M _ _ tp tsdp tctx thr' (fun z => z < U sp - 128 /\ (z < SH \/ SH + 2 ^ 15 <= z)) GH);
      [ intros x [Hx Hx2]; apply pam_1_outside; [left; exact Hx | exact Hx2] | apply pam_1_grows | intros z Hz; cbv beta; lia ..].
  Qed.
End PAM.

Section EAM.
  Variables (M : word -> option byte) (sp s4x s5x thr v72 v80 : word) (RIz slot mfa : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma eam_1_outside : forall x : word, (U x < U sp - 112 \/ U sp - 48 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    eam_1 M sp s4x s5x RIz slot mfa x = M x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp). rewrite eam_1_eq. apply psfill_outside; rewrite ?at_u by lia; first [lia | exact X2].
  Qed.
  Lemma eam_2_outside : forall x : word, (U x < U sp - 112 \/ U sp - 48 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    eam_2 M sp s4x s5x RIz slot mfa x = M x.
  Proof using Hslot Hsp.
    intros x X1 X2. pose proof (u64_range sp). rewrite eam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). apply eam_1_outside; assumption.
  Qed.
  Lemma eam_3_outside : forall x : word, U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
    (U x < U sp - 112 \/ U sp - 48 <= U x) -> (U x < SH \/ SH + 2 ^ 15 <= U x) ->
    (U x < U thr + 2872 \/ U thr + 2888 <= U x) -> (U x < RIz + 24 \/ RIz + 32 <= U x) ->
    eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa x = M x.
  Proof using Hslot Hsp.
    intros x HT HR0 HR1 X1 X2 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold eam_3 in G in change_no_check G' end). rewrite efs_ms_outside by assumption. apply eam_2_outside; assumption.
  Qed.
  Lemma eam_1_grows : mem_grows M (eam_1 M sp s4x s5x RIz slot mfa).
  Proof using. rewrite eam_1_eq. apply psfill_grows. Qed.
  Lemma eam_2_grows : mem_grows M (eam_2 M sp s4x s5x RIz slot mfa).
  Proof using. rewrite eam_2_eq. eapply mem_grows_trans; [apply eam_1_grows | apply gts2_grows]. Qed.
  Lemma eam_3_grows : mem_grows M (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold eam_3 in G in change_no_check G' end). eapply mem_grows_trans; [apply eam_2_grows | apply efs_ms_grows]. Qed.

  Lemma eam_3_mrestrict : forall Hd : word -> bool, U thr + 4096 <= 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
    hid_off Hd (U sp - 112) 64 -> hid_off Hd SH (2 ^ 15) -> hid_off Hd (U thr) 4096 -> hid_off Hd RIz 128 ->
    eam_3 (mrestrict Hd M) sp s4x s5x thr v72 v80 RIz slot mfa = mrestrict Hd (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  Proof using Hslot Hsp.
    intros Hd HT HR0 HR1 O1 O2 O3 O4. pose proof (u64_range sp).
    assert (E1' : eam_1 (mrestrict Hd M) sp s4x s5x RIz slot mfa = mrestrict Hd (eam_1 M sp s4x s5x RIz slot mfa)).
    { rewrite !eam_1_eq. apply psfill_mrestrict; rewrite ?at_u by lia; first [lia | exact O2 | intros x Hx; apply O1; lia]. }
    assert (E2' : eam_2 (mrestrict Hd M) sp s4x s5x RIz slot mfa = mrestrict Hd (eam_2 M sp s4x s5x RIz slot mfa)).
    { (lazymatch goal with |- ?G => let G' := eval unfold eam_2 in G in change_no_check G' end). rewrite E1'. apply gts2_mrestrict; rewrite ?at_u by lia; first [lia | intros x Hx; apply O1; lia]. }
    (lazymatch goal with |- ?G => let G' := eval unfold eam_3 in G in change_no_check G' end). rewrite E2'. apply efs_ms_mrestrict; assumption.
  Qed.

  Lemma eam_1_gctH : forall segs t (tp tsdp tctx thr' : word),
    gctH segs t M (at_ (at_ sp (-48)) (-16)) tp tsdp tctx thr' ->
    (U (gt_tsd t) + 8 <= U sp - 112 /\ U tp - 80 <= U sp - 112 /\ U tsdp + 8 <= U sp - 112 /\ U tctx + 160 <= U sp - 112) ->
    (U (gt_tsd t) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd t)) ->
    (U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88) ->
    (U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp) ->
    (U tctx + 160 <= SH \/ SH + 2 ^ 15 <= U tctx + 152) ->
    gctH segs t (eam_1 M sp s4x s5x RIz slot mfa) (at_ (at_ sp (-48)) (-16)) tp tsdp tctx thr'.
  Proof using Hslot Hsp.
    intros segs t tp tsdp tctx thr' GH (B1 & B2 & B3 & B4) O1 O2 O3 O4. pose proof (u64_range sp).
    apply (gctH_keep_P segs t M _ _ tp tsdp tctx thr' (fun z => z < U sp - 112 /\ (z < SH \/ SH + 2 ^ 15 <= z)) GH);
      [ intros x [Hx Hx2]; apply eam_1_outside; [left; exact Hx | exact Hx2] | apply eam_1_grows | intros z Hz; cbv beta; lia ..].
  Qed.
End EAM.
End AsAllocM8t.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s AsAllocM8t.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma hid_true_off : forall (Hd : word -> bool) (a : word) lo n, Hd a = true -> hid_off Hd lo n -> (U a < lo \/ lo + n <= U a).
Proof.
  intros Hd a lo n Ha Hh. destruct (Z_lt_le_dec (U a) lo) as [C1|C1]; [left; exact C1|].
  destruct (Z_lt_le_dec (U a) (lo + n)) as [C2|C2]; [| right; exact C2].
  exfalso. rewrite (Hh a) in Ha by lia. discriminate Ha.
Qed.

Ltac fc H n := (apply Forall_cons_iff in H; destruct H as [n H]).
Ltac rrm := rewrite rdn_mrestrict;
  [ assumption | wd_ulia_c
  | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
    first [ assumption | match goal with Hh : hid_off _ ?c 8 |- hid_off _ ?c _ => eapply hid_off_sub; [exact Hh | lia | lia] end ] ].

(* [comment removed for export] *)
Lemma poisonH_mrestrict : forall segs t mem (addr size value ra sp : word) cpm midend thr (H : word -> bool),
  poisonH segs t mem addr size value ra sp cpm midend thr ->
  Forall (fun c => hid_off H c 8) (poison_cells t) ->
  hid_off H (U sp - 64) 64 -> hid_off H (shad addr) (shlen size) ->
  poisonH segs t (mrestrict H mem) addr size value ra sp cpm midend thr.
Proof.
  intros segs t mem addr size value ra sp cpm midend thr H PH Hc Hf Hs.
  destruct PH as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P21 P22 P23 P24].
  pose proof (u64_range sp) as Hsp. pose proof (u64_range addr) as Ha. pose proof (u64_range size) as Hz.
  assert (Hsl : 0 <= shlen size) by ((lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end); apply Z.div_pos; lia).
  assert (Hsh : 0 <= shad addr /\ shad addr + shlen size < 2 ^ 64).
  { (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia|lia]|].
    pose proof (Z.div_le_upper_bound (U addr) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (U size) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  pose proof P15 as CB. unfold poison_cells in Hc, CB.
  fc Hc h1. fc Hc h2. fc Hc h3. fc Hc h4. fc Hc h5. fc Hc h6. fc Hc h7. fc Hc h8. fc Hc h9. fc Hc h10. fc Hc h11. fc Hc h12. fc Hc h13. fc Hc h14.
  fc CB b1. fc CB b2. fc CB b3. fc CB b4. fc CB b5. fc CB b6. fc CB b7. fc CB b8. fc CB b9. fc CB b10. fc CB b11. fc CB b12. fc CB b13. fc CB b14.
  cbv beta in *.
  split; try assumption.
  - rrm. - rrm. - rrm. - rrm. - rrm. - rrm. - rrm. - rrm. - rrm. - rrm.
  - intros Hv. destruct (P13 Hv) as [R C]. split; [|exact C]. rrm.
  - intros Hv. destruct (P14 Hv) as (R1 & R2 & L & T1 & T2). repeat split; try assumption. + rrm. + rrm.
  - rewrite store_ok_mrestrict; [exact P22 | rewrite at_u; lia | rewrite at_u by lia].
    replace (U sp + -64) with (U sp - 64) by lia. exact Hf.
  - rewrite store_ok_mrestrict; [exact P23 | wd_ulia | unorm; rewrite Z2Nat.id by lia; exact Hs].
Qed.

(* [comment removed for export] *)
Lemma gctH_mrestrict : forall segs t (mem : word -> option byte) (sp tp tsdp tctx thr : word) (H : word -> bool),
  gctH segs t mem sp tp tsdp tctx thr ->
  hid_off H (U (gt_tsd t)) 8 -> hid_off H (U tp - 88) 8 -> hid_off H (U tsdp) 8 -> hid_off H (U tctx + 152) 8 -> hid_off H (U sp - 8) 8 ->
  gctH segs t (mrestrict H mem) sp tp tsdp tctx thr.
Proof.
  intros segs t mem sp tp tsdp tctx thr H [Rf Rk Rt Rc Rth NZ SOK Gsp G1 G2 G3 G4] O1 O2 O3 O4 O5.
  pose proof (u64_range tp). pose proof (u64_range tsdp). pose proof (u64_range tctx). pose proof (u64_range (gt_tsd t)). pose proof (u64_range sp).
  split; try assumption.
  - rewrite rdn_mrestrict; [exact Rf | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply O1; lia].
  - rewrite rdn_mrestrict; [exact Rk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply O1; lia].
  - rewrite rdn_mrestrict; [exact Rt | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply O2; lia].
  - rewrite rdn_mrestrict; [exact Rc | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact O3].
  - rewrite rdn_mrestrict; [exact Rth | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact O4].
  - rewrite store_ok_mrestrict; [exact SOK | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros x Hx; apply O5; lia].
Qed.

Section FPGen.
Context {fx : FPState}.

Section LIFTS.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem pf_after_map_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model)
           (sp thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte) (RIz SPB c au mu nf T thr0 : Z) (Qok Qf : config -> Prop),
    let slot := SPB + c * 2 ^ 32 + mu in
    let SH := slot / 8 + 0x7fff8000 in
    pf_regs sp RIz SPB c regs -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 9 = at_ thr 2768 -> getr regs 10 = Z_to_bv 64 slot ->
    getr regs 19 = Z_to_bv 64 (2 ^ 18) -> getr regs 20 = Z_to_bv 64 slot -> getr regs 22 = Z_to_bv 64 0x103f18 ->
    (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> 0 <= nf <= 2 ^ 27 ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63) -> (AIMGHI <= RIz /\ RIz + 128 <= U sp - 128) ->
    (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 128 /\ T mod 8 = 0) -> (T + 4096 <= RIz \/ RIz + 128 <= T) ->
    (* [comment removed for export] *)
    (T + 4096 <= SH \/ SH + 2 ^ 15 <= T) -> (RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz) ->
    (* [comment removed for export] *)
    poisonH ASEGS asan_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0 ->
    gctH ASEGS asan_gct_tab M (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr ->
    (U (gt_tsd asan_gct_tab) + 8 <= U sp - 128 /\ U tp - 80 <= U sp - 128 /\ U tsdp + 8 <= U sp - 128 /\ U ctxw + 160 <= U sp - 128) ->
    (U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab)) ->
    (U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88) -> (U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp) ->
    (U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152) ->
    rdn ASEGS M (at_ thr 2872) 8 = Some (LE8 v72) -> rdn ASEGS M (at_ thr 2880) 8 = Some (LE8 v80) -> rdn ASEGS M (at_ thr 2792) 8 = Some (LE8 vst) ->
    rdn ASEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) -> rdn ASEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)) ->
    store_ok ASEGS M thr 4096 = true -> store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true ->
    (* [comment removed for export] *)
    Forall (fun c => hid_off Hd c 8) (poison_cells asan_poison_tab) ->
    hid_off Hd (U sp - 128) 64 -> hid_off Hd SH (2 ^ 15) ->
    hid_off Hd (U (gt_tsd asan_gct_tab)) 8 -> hid_off Hd (U tp - 88) 8 -> hid_off Hd (U tsdp) 8 -> hid_off Hd (U ctxw + 152) 8 ->
    hid_off Hd T 4096 -> hid_off Hd RIz 128 ->
    (* [comment removed for export] *)
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (* [comment removed for export] *)
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x50f68 ->
        getr r 10 = Z_to_bv 64 0x103f18 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
        getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
        getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) ->
        getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r 4 = tp -> getr r 3 = gp ->
        katwD ASEGS (mkCfg (mkst r (0x4ea98 : word) (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu) rom) mdlm) Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50ef4 : word) M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 Qok Qf slot SH
           HR H4 H3 H9 H10 H19 H20 H22 Hsp Hc Hau Hnf HSPB HRI HT HTRI HTSH HRSH PH GH GB G1 G2 G3 G4 R72 R80 Rst Rau Rmu Rnf SOKT SOKRI
           HDc HDf HDsh HD1 HD2 HD3 HD4 HDT HDRI HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HSPB as [S1 S2]. destruct Hau as [AU1 AU2].
    destruct HT as (UT & T1 & T2 & T3). destruct HRI as [RI1 RI2]. pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot < 2 ^ 63) by ((lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end); lia).
    subst SH.
    set (Mr := mrestrict Hd M).
    assert (Ufsp : U (at_ sp (-64)) = U sp - 64) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    (* [comment removed for export] *)
    assert (PHr : poisonH ASEGS asan_poison_tab Mr (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0).
    { apply poisonH_mrestrict; [exact PH | exact HDc | rewrite Ufsp; replace (U sp - 64 - 64) with (U sp - 128) by lia; exact HDf |].
      destruct (psfill_shad slot SL) as (E1 & E2 & _). rewrite E1, E2. exact HDsh. }
    assert (GHr0 : gctH ASEGS asan_gct_tab Mr (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr).
    { apply gctH_mrestrict; [exact GH | exact HD1 | exact HD2 | exact HD3 | exact HD4 |].
      rewrite at_u by (rewrite Ufsp; lia). rewrite Ufsp. eapply hid_off_sub; [exact HDf | lia | lia]. }
    assert (GHr : gctH ASEGS asan_gct_tab (pam_1 Mr sp (at_ thr 2768) RIz SPB c slot) (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr).
    { apply pam_1_gctH; [lia | exact SL | exact GHr0 | exact GB | exact G1 | exact G2 | exact G3 | exact G4]. }
    assert (OUT2 : forall (a : word) (k : nat), U a + Z.of_nat k <= U sp - 128 -> (U a + Z.of_nat k <= slot / 8 + 0x7fff8000 \/ slot / 8 + 0x7fff8000 + 2 ^ 15 <= U a) -> hid_off Hd (U a) (Z.of_nat k) ->
               rdn ASEGS (pam_2 Mr sp (at_ thr 2768) RIz SPB c slot) a k = rdn ASEGS M a k).
    { intros a k B1 B2 Hh. pose proof (u64_range a). rewrite <- (rdn_mrestrict ASEGS Hd M a k) by (first [lia | exact Hh]).
      apply rdn_ext; [lia|]. intros x Hx. apply pam_2_outside; [lia | exact SL | lia | lia]. }
    assert (SOKr : forall (a : word) (k : nat), U a + Z.of_nat k <= 2 ^ 64 -> hid_off Hd (U a) (Z.of_nat k) -> store_ok ASEGS M a k = true ->
               store_ok ASEGS (pam_2 Mr sp (at_ thr 2768) RIz SPB c slot) a k = true).
    { intros a k B1 Hh SOK. eapply store_ok_mono; [apply pam_2_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict by (first [lia | exact Hh]). exact SOK. }
    assert (Ut : forall k, 0 <= k < 4096 -> U (at_ thr k) = T + k) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    unfold slot in *.
    destruct (pf_after_map Mr rom sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 regs
                HR H4 H3 H9 H10 H19 H20 H22 (conj SP1 SP2) Hc (conj AU1 AU2) Hnf (conj S1 S2) ltac:(lia) ltac:(lia) HTRI PHr GHr)
      as (r & RUN & PR & C1 & C10 & C11 & C12 & C13 & C9 & C19 & C20 & C4 & C3).
    - (* [comment removed for export] *)
      eapply store_ok_mono; [apply pam_1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
      destruct PH as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P22 _ _].
      eapply (store_ok_sub ASEGS M (at_ (at_ sp (-64)) (-64)) _ 64); [rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P22 | rewrite !at_u by (rewrite ?Ufsp; lia); lia | rewrite !at_u by (rewrite ?Ufsp; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - rewrite OUT2; [exact R72 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - rewrite OUT2; [exact R80 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - rewrite OUT2; [exact Rst | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - rewrite OUT2; [exact Rau | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]].
    - rewrite OUT2; [exact Rmu | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]].
    - apply SOKr; [lia | rewrite UT; exact HDT | exact SOKT].
    - apply SOKr; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; exact HDRI | exact SOKRI].
    - (* [comment removed for export] *)
      rewrite <- Rnf. rewrite <- (rdn_mrestrict ASEGS Hd M (Z_to_bv 64 (RIz + 16)) 8) by (rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact HDRI | lia | lia]]).
      apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      apply pam_3_outside; [lia | exact SL | lia | lia | lia | lia | lia | lia | lia | lia].
    - (* [comment removed for export] *)
      assert (HIDSAME : forall a : word, Hd a = true -> pam_3 M sp thr v72 v80 vst RIz SPB c slot mu a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold slot in G in change_no_check G' end).
        pose proof (hid_true_off Hd a _ _ Ha HDf) as Z1. pose proof (hid_true_off Hd a _ _ Ha HDsh) as Z2.
        pose proof (hid_true_off Hd a _ _ Ha HDT) as Z3. pose proof (hid_true_off Hd a _ _ Ha HDRI) as Z4.
        apply pam_3_outside; [clear - SP1; lia | exact SL | clear - UT T2 SP2 Hspr; lia | clear - RI1; lia | clear - RI2 SP2 Hspr; lia
                             | clear - Z1; lia | exact Z2 | clear - Z3 UT; lia | clear - Z3 UT; lia | clear - Z4; lia]. }
      apply (katwD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x50ef4 : word) M rom)
               (mkst r (0x4ea98 : word) (mrestrict Hd (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu)) rom) model Qok Qf LC AWF MI HALT).
      { rewrite mk_restrict_mkst. fold Mr.
        rewrite <- (pam_3_mrestrict M sp thr v72 v80 vst RIz SPB c slot mu ltac:(lia) SL Hd ltac:(lia) ltac:(lia) ltac:(lia) HDf HDsh ltac:(rewrite UT; exact HDT) HDRI).
        exact RUN. }
      intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (0x50ef4 : word) M rom)) with M by reflexivity.
      rewrite (mk_munrestrict_same Hd M _ HIDSAME).
      apply (CONT r mdlm SBMm MIm PR C1 C10 C11 C12 C13 C9 C19 C20 C4 C3).
  Qed.
  Theorem efs_after_map_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte) (RIz slot mfa T thr0 : Z) (Qok Qf : config -> Prop),
    let SH := slot / 8 + 0x7fff8000 in
    getr regs 2 = at_ sp (-48) -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18) -> getr regs 9 = Z_to_bv 64 slot ->
    getr regs 10 = Z_to_bv 64 slot -> getr regs 18 = Z_to_bv 64 (2 ^ 18) -> getr regs 19 = Z_to_bv 64 RIz -> getr regs 20 = s4x -> getr regs 21 = s5x ->
    (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> 0 < slot < 2 ^ 63 -> 0 <= mfa <= 2 ^ 29 ->
    (AIMGHI <= RIz /\ RIz + 128 <= U sp - 112) ->
    (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 112 /\ T mod 8 = 0) -> (T + 4096 <= RIz \/ RIz + 128 <= T) ->
    (T + 4096 <= SH \/ SH + 2 ^ 15 <= T) -> (RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz) -> (U sp <= SH \/ SH + 2 ^ 15 <= U sp - 112) ->
    poisonH ASEGS asan_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0 ->
    gctH ASEGS asan_gct_tab M (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr ->
    (U (gt_tsd asan_gct_tab) + 8 <= U sp - 112 /\ U tp - 80 <= U sp - 112 /\ U tsdp + 8 <= U sp - 112 /\ U ctxw + 160 <= U sp - 112) ->
    (U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab)) ->
    (U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88) -> (U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp) ->
    (U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152) ->
    rdn ASEGS M (at_ thr 2872) 8 = Some (LE8 v72) -> rdn ASEGS M (at_ thr 2880) 8 = Some (LE8 v80) ->
    store_ok ASEGS M thr 4096 = true -> store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true ->
    rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) ->
    Forall (fun c => hid_off Hd c 8) (poison_cells asan_poison_tab) ->
    hid_off Hd (U sp - 112) 112 -> hid_off Hd SH (2 ^ 15) ->
    hid_off Hd (U (gt_tsd asan_gct_tab)) 8 -> hid_off Hd (U tp - 88) 8 -> hid_off Hd (U tsdp) 8 -> hid_off Hd (U ctxw + 152) 8 ->
    hid_off Hd T 4096 -> hid_off Hd RIz 128 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
        getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4x -> getr r 21 = s5x -> getr r 4 = tp -> getr r 3 = gp ->
        katwD ASEGS (mkCfg (mkst r ra (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa) rom) mdlm) Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x4eb38 : word) M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf SH
           H2 H4 H3 H8 H9 H10 H18 H19 H20 H21 Hsp Hret Hslot Hmfa HRI HT HTRI HTSH HRSH HSSH PH GH GB G1 G2 G3 G4 R72 R80 SOKT SOKRI
           Sra Ss0 Ss1 Ss2 Ss3 HDc HDf HDsh HD1 HD2 HD3 HD4 HDT HDRI HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2].
    destruct HT as (UT & T1 & T2 & T3). destruct HRI as [RI1 RI2]. pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot < 2 ^ 63) by lia.
    subst SH.
    set (Mr := mrestrict Hd M).
    assert (Ufsp : U (at_ sp (-48)) = U sp - 48) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (HDf1 : hid_off Hd (U sp - 112) 64) by (eapply hid_off_sub; [exact HDf | lia | lia]).
    assert (PHr : poisonH ASEGS asan_poison_tab Mr (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0).
    { apply poisonH_mrestrict; [exact PH | exact HDc | rewrite Ufsp; replace (U sp - 48 - 64) with (U sp - 112) by lia; exact HDf1 |].
      destruct (psfill_shad slot SL) as (E1 & E2 & _). rewrite E1, E2. exact HDsh. }
    assert (GHr0 : gctH ASEGS asan_gct_tab Mr (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr).
    { apply gctH_mrestrict; [exact GH | exact HD1 | exact HD2 | exact HD3 | exact HD4 |].
      rewrite at_u by (rewrite Ufsp; lia). rewrite Ufsp. eapply hid_off_sub; [exact HDf | lia | lia]. }
    assert (GHr : gctH ASEGS asan_gct_tab (eam_1 Mr sp s4x s5x RIz slot mfa) (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr).
    { apply eam_1_gctH; [lia | exact SL | exact GHr0 | exact GB | exact G1 | exact G2 | exact G3 | exact G4]. }
    assert (OUT2 : forall (a : word) (k : nat), (U a + Z.of_nat k <= U sp - 112 \/ U sp - 48 <= U a) -> U a + Z.of_nat k <= 2 ^ 64 ->
               (U a + Z.of_nat k <= slot / 8 + 0x7fff8000 \/ slot / 8 + 0x7fff8000 + 2 ^ 15 <= U a) -> hid_off Hd (U a) (Z.of_nat k) ->
               rdn ASEGS (eam_2 Mr sp s4x s5x RIz slot mfa) a k = rdn ASEGS M a k).
    { intros a k B1 B0 B2 Hh. pose proof (u64_range a). rewrite <- (rdn_mrestrict ASEGS Hd M a k) by (first [lia | exact Hh]).
      apply rdn_ext; [lia|]. intros x Hx. apply eam_2_outside; [lia | exact SL | lia | lia]. }
    assert (SOKr : forall (a : word) (k : nat), U a + Z.of_nat k <= 2 ^ 64 -> hid_off Hd (U a) (Z.of_nat k) -> store_ok ASEGS M a k = true ->
               store_ok ASEGS (eam_2 Mr sp s4x s5x RIz slot mfa) a k = true).
    { intros a k B1 Hh SOK. eapply store_ok_mono; [apply eam_2_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict by (first [lia | exact Hh]). exact SOK. }
    assert (Ut : forall k, 0 <= k < 4096 -> U (at_ thr k) = T + k) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Us : forall k, -48 <= k < 0 -> U (at_ sp k) = U sp + k) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct (efs_after_map Mr rom sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 regs
                H2 H4 H3 H8 H9 H10 H18 H19 H20 H21 (conj SP1 SP2) Hret ltac:(lia) Hmfa ltac:(lia) ltac:(lia) HTRI PHr GHr)
      as (r & RUN & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C4 & C3).
    - (* [comment removed for export] *)
      eapply store_ok_mono; [apply eam_1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
      destruct PH as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P22 _ _].
      eapply (store_ok_sub ASEGS M (at_ (at_ sp (-48)) (-64)) _ 64); [rewrite at_u by (rewrite Ufsp; lia); rewrite Ufsp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P22 | rewrite !at_u by (rewrite ?Ufsp; lia); lia | rewrite !at_u by (rewrite ?Ufsp; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - rewrite OUT2; [exact R72 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - rewrite OUT2; [exact R80 | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ut by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDT | lia | lia]].
    - apply SOKr; [lia | rewrite UT; exact HDT | exact SOKT].
    - apply SOKr; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; exact HDRI | exact SOKRI].
    - rewrite OUT2; [exact Sra | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss0 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss1 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss2 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - rewrite OUT2; [exact Ss3 | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Us by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]].
    - assert (HIDSAME : forall a : word, Hd a = true -> eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa a = M a).
      { intros a Ha.
        pose proof (hid_true_off Hd a _ _ Ha HDf1) as Z1. pose proof (hid_true_off Hd a _ _ Ha HDsh) as Z2.
        pose proof (hid_true_off Hd a _ _ Ha HDT) as Z3. pose proof (hid_true_off Hd a _ _ Ha HDRI) as Z4.
        apply eam_3_outside; [clear - SP1; lia | exact SL | clear - UT T2 SP2 Hspr; lia | clear - RI1; lia | clear - RI2 SP2 Hspr; lia
                             | clear - Z1; lia | exact Z2 | clear - Z3 UT; lia | clear - Z4; lia]. }
      apply (katwD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x4eb38 : word) M rom)
               (mkst r ra (mrestrict Hd (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa)) rom) model Qok Qf LC AWF MI HALT).
      { rewrite mk_restrict_mkst. fold Mr.
        rewrite <- (eam_3_mrestrict M sp s4x s5x thr v72 v80 RIz slot mfa ltac:(lia) SL Hd ltac:(lia) ltac:(lia) ltac:(lia) HDf1 HDsh ltac:(rewrite UT; exact HDT) HDRI).
        exact RUN. }
      intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (0x4eb38 : word) M rom)) with M by reflexivity.
      rewrite (mk_munrestrict_same Hd M _ HIDSAME).
      apply (CONT r mdlm SBMm MIm C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3).
  Qed.
End LIFTS.
End FPGen.
