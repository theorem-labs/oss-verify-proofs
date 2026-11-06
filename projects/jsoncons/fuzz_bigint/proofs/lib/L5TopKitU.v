(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecsU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState Mem Cells Step Frame Exec Tac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Tgt Require Import F_syscalls RMallocRep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module TKU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
Section S.
Context {fx : FPState}.

Lemma srz_evt_canon : forall (Q : machine_state -> Prop) (R : bvmap 5 word) pc M mo K,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  evt rsegs Q (MS (canon_regs R) fp_regs pc fp_csr None M (seg_rom rsegs)) ->
  (forall ms' ms'', Q ms' -> ms_eqv ms' ms'' -> srealizes rsegs SCFG (mkCfg ms'' mo) K) ->
  srealizes rsegs SCFG (mkCfg (mkst R pc M (seg_rom rsegs)) mo) K.
Proof.
  intros Q R pc M mo K Hh Hl EV CONT.
  destruct (evt_eqv_transfer rsegs Q _ _ (mkst_eqv_canon R pc M (seg_rom rsegs)) EV) as (ms1 & ms1' & HQ & EQV & MS').
  eapply srz_msteps; [exact Hh| exact Hl| exact MS'|]. exact (CONT ms1 ms1' HQ EQV).
Qed.

(* [comment removed for export] *)
Lemma srz_evt_canonMS : forall (Q : machine_state -> Prop) (R : bvmap 5 word) pc M mo K,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  evt rsegs Q (MS (canon_regs R) fp_regs pc fp_csr None M (seg_rom rsegs)) ->
  (forall R1 pc1 M1 (R'' : bvmap 5 word), Q (MS R1 fp_regs pc1 fp_csr None M1 (seg_rom rsegs)) -> regs_eqv R1 R'' ->
        srealizes rsegs SCFG (mkCfg (mkst R'' pc1 M1 (seg_rom rsegs)) mo) K) ->
  (forall ms', Q ms' -> exists R1 pc1 M1, ms' = MS R1 fp_regs pc1 fp_csr None M1 (seg_rom rsegs)) ->
  srealizes rsegs SCFG (mkCfg (mkst R pc M (seg_rom rsegs)) mo) K.
Proof.
  intros Q R pc M mo K Hh Hl EV CONT SHAPE.
  eapply srz_evt_canon; [exact Hh| exact Hl| exact EV|].
  intros ms' ms'' HQ EQV. destruct (SHAPE ms' HQ) as (R1 & pc1 & M1 & ->).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [-> REQ]. apply (CONT R1 pc1 M1 (ms_regs ms'') HQ REQ).
Qed.
End S.

(* [comment removed for export] *)
Lemma getr_of_eqv : forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 R'' k,
  regs_eqv (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) R'' ->
  0 < k < 32 ->
  getr R'' (Z_to_bv 5 k) = nth (Z.to_nat k) [Z_to_bv 64 0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; v28; v29; v30; v31] (Z_to_bv 64 0).
Proof.
  intros until k. intros REQ Hk. rewrite <- (getr_eqv _ _ _ REQ).
  assert (C : exists n, k = Z.of_nat n /\ (0 < n < 32)%nat) by (exists (Z.to_nat k); lia).
  destruct C as (n & -> & Hn). rewrite Nat2Z.id.
  do 32 (destruct n as [|n]; [first [lia | (unfold getr; cbn; reflexivity)] |]). lia.
Qed.

(* [comment removed for export] *)
Lemma bv5_lit : forall k, 0 <= k < 32 -> forall H, Z_to_bv 5 k = @BV 5 k H.
Proof. intros k Hk H. apply bv_eq. rewrite Z_to_bv_unsigned. cbn [bv_unsigned]. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia. Qed.

Lemma getr_of_eqv_lit : forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 R'' k (H : BvWf 5 k),
  regs_eqv (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) R'' ->
  0 < k < 32 ->
  getr R'' (@BV 5 k H) = nth (Z.to_nat k) [Z_to_bv 64 0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; v28; v29; v30; v31] (Z_to_bv 64 0).
Proof. intros. rewrite <- (bv5_lit k ltac:(lia)). apply getr_of_eqv; assumption. Qed.

(* [comment removed for export] *)
Lemma canon_of_eqv : forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 R'',
  regs_eqv (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) R'' ->
  canon_regs R'' = mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31.
Proof.
  intros until R''. intros REQ. unfold canon_regs.
  pose proof (fun k H Hk => getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R'' k H REQ Hk) as E.
  rewrite (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7), (E 8), (E 9), (E 10), (E 11), (E 12), (E 13), (E 14), (E 15), (E 16),
          (E 17), (E 18), (E 19), (E 20), (E 21), (E 22), (E 23), (E 24), (E 25), (E 26), (E 27), (E 28), (E 29), (E 30), (E 31) by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma canon_after : forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 R1 R2,
  regs_eqv (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) R1 ->
  regs_preserved R1 R2 ->
  canon_regs R2 = mkR (getr R2 1%bv) v2 v3 v4 (getr R2 5%bv) (getr R2 6%bv) (getr R2 7%bv) v8 v9 (getr R2 10%bv) (getr R2 11%bv)
                      (getr R2 12%bv) (getr R2 13%bv) (getr R2 14%bv) (getr R2 15%bv) (getr R2 16%bv) (getr R2 17%bv)
                      v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 (getr R2 28%bv) (getr R2 29%bv) (getr R2 30%bv) (getr R2 31%bv).
Proof.
  intros until R2. intros REQ RP. unfold canon_regs.
  assert (E : forall k (H : BvWf 5 k), In k callee_saved_idx -> 0 < k < 32 ->
            getr R2 (@BV 5 k H) = nth (Z.to_nat k) [Z_to_bv 64 0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; v28; v29; v30; v31] (Z_to_bv 64 0)).
  { intros k H Hin Hk. rewrite (RP (@BV 5 k H)) by exact Hin. apply (getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 k H REQ Hk). }
  rewrite (E 2), (E 3), (E 4), (E 8), (E 9), (E 18), (E 19), (E 20), (E 21), (E 22), (E 23), (E 24), (E 25), (E 26), (E 27) by (cbn; first [tauto | lia]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma regs_preserved_intro : forall v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 (R R6 : bvmap 5 word),
  regs_eqv (mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) R6 ->
  getr R 2%bv = v2 -> getr R 3%bv = v3 -> getr R 4%bv = v4 -> getr R 8%bv = v8 -> getr R 9%bv = v9 ->
  getr R 18%bv = v18 -> getr R 19%bv = v19 -> getr R 20%bv = v20 -> getr R 21%bv = v21 -> getr R 22%bv = v22 ->
  getr R 23%bv = v23 -> getr R 24%bv = v24 -> getr R 25%bv = v25 -> getr R 26%bv = v26 -> getr R 27%bv = v27 ->
  regs_preserved R R6.
Proof.
  intros until R6. intros REQ E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 r Hr.
  rewrite <- (bv5_lit 2 ltac:(lia)) in E2. rewrite <- (bv5_lit 3 ltac:(lia)) in E3. rewrite <- (bv5_lit 4 ltac:(lia)) in E4.
  rewrite <- (bv5_lit 8 ltac:(lia)) in E8. rewrite <- (bv5_lit 9 ltac:(lia)) in E9. rewrite <- (bv5_lit 18 ltac:(lia)) in E18.
  rewrite <- (bv5_lit 19 ltac:(lia)) in E19. rewrite <- (bv5_lit 20 ltac:(lia)) in E20. rewrite <- (bv5_lit 21 ltac:(lia)) in E21.
  rewrite <- (bv5_lit 22 ltac:(lia)) in E22. rewrite <- (bv5_lit 23 ltac:(lia)) in E23. rewrite <- (bv5_lit 24 ltac:(lia)) in E24.
  rewrite <- (bv5_lit 25 ltac:(lia)) in E25. rewrite <- (bv5_lit 26 ltac:(lia)) in E26. rewrite <- (bv5_lit 27 ltac:(lia)) in E27.
  assert (C : forall k, 0 < k < 32 -> getr R6 (Z_to_bv 5 k) = nth (Z.to_nat k) [Z_to_bv 64 0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27; v28; v29; v30; v31] (Z_to_bv 64 0)).
  { intros k Hk. apply (getr_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R6 k REQ Hk). }
  assert (RK : forall k, k = bv_unsigned r -> r = Z_to_bv 5 k) by (intros k ->; symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  unfold callee_saved_idx in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [Hr|Hr]; [rewrite (RK _ Hr); lazymatch type of Hr with ?k = _ => rewrite (C k) by lia end;
          cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; symmetry; assumption|]).
  destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma rdn_mrd : forall M n a i, (i < n)%nat -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  forall bs, rdn rsegs M (Z_to_bv 64 a) n = Some bs -> mrd rsegs M (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros M n. induction n as [|n IH]; intros a i Hi Ha Hn bs H; [lia|].
  rewrite rdn_unfold in H. destruct (mrd rsegs M (Z_to_bv 64 a)) as [b|] eqn:E; [|discriminate].
  destruct (rdn rsegs M (Z_to_bv 64 a + 1)%bv n) as [bs'|] eqn:E2; [|discriminate]. inversion H; subst bs. clear H.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E.
  - cbn. rewrite <- (IH (a + 1) i ltac:(lia) ltac:(lia) ltac:(lia) bs'); [f_equal; unfold wa; f_equal; lia|].
    rewrite <- E2. f_equal. unfold wa. rewrite wa_succ. reflexivity.
Qed.

Lemma bytes_at_of_rdn : forall M n a bs, rdn rsegs M (Z_to_bv 64 a) n = Some bs -> length bs = n ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> bytes_at rsegs M a bs.
Proof.
  intros M n a bs H L Ha Hn. split; [exact Ha|]. split; [rewrite L; exact Hn|].
  intros i Hi. rewrite L in Hi. apply (rdn_mrd M n a i Hi Ha Hn bs H).
Qed.

Lemma rdn_length : forall M n (a : word) bs, rdn rsegs M a n = Some bs -> length bs = n.
Proof.
  intros M n. induction n as [|n IH]; intros a bs H.
  - cbn in H. inversion H. reflexivity.
  - rewrite rdn_unfold in H. destruct (mrd rsegs M a); [|discriminate]. destruct (rdn rsegs M (a + 1)%bv n) eqn:E; [|discriminate].
    inversion H; subst. cbn. f_equal. eapply IH. exact E.
Qed.

Lemma ro_cells_u64 : forall M a v, L5.u64_at rsegs M a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  ro_cells rsegs M a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v H Ha H8. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  unfold L5.u64_at in H. apply (bytes_at_of_rdn M 8 a _ H); [| exact Ha| exact H8].
  apply (rdn_length _ _ _ _ H).
Qed.

Lemma ro_cells_u8 : forall M a b, L5.u8_at rsegs M a b -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  ro_cells rsegs M a [C1 (Z_to_bv 8 b)].
Proof.
  intros M a b H Ha H1. split; [exact (conj I I)|]. cbn [cells_bytes cbytes app].
  unfold L5.u8_at in H. apply (bytes_at_of_rdn M 1 a _ H); [reflexivity| exact Ha| exact H1].
Qed.

(* [comment removed for export] *)
Lemma hull_lo_eq : L5.hull_lo rsegs = 0x10000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_hi_eq : L5.hull_hi rsegs = 0x92000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_of : forall a n, (a + n <= 0x10000 \/ 0x92000 <= a) -> L5.hull_apart rsegs a n.
Proof. intros a n H. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. exact H. Qed.
Lemma hull_apart_lit : forall a n, L5.hull_apart rsegs a n -> (a + n <= 0x10000 \/ 0x92000 <= a).
Proof. intros a n H. unfold L5.hull_apart in H. rewrite hull_lo_eq, hull_hi_eq in H. exact H. Qed.

(* [comment removed for export] *)
Lemma stk_of_defined : forall M lo hi, L5.defined M lo (hi - lo) -> 0 <= lo -> hi <= 2 ^ 64 -> (hi <= 0x10000 \/ 0x92000 <= lo) ->
  stk rsegs M lo hi.
Proof.
  intros M lo hi D Hlo Hhi OUT. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  specialize (D (a - lo) ltac:(lia)). replace (lo + (a - lo)) with a in D by lia.
  assert (Hwa : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  split.
  - rewrite ref_wview_overlay by (rewrite Hwa; lia). unfold wa. exact D.
  - rewrite ref_mrd_overlay by (rewrite Hwa; lia). unfold wa. destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity| congruence].
Qed.


(* [comment removed for export] *)
Lemma cells_at_agree : forall m m' A cs,
  cells_at rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) -> cells_at rsegs m' A cs.
Proof.
  intros m m' A cs [Hwf (H0 & H1 & HB)] K. pose proof (cells_bytes_length cs Hwf) as LEN.
  split; [exact Hwf|]. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (K (A + Z.of_nat i)) by (rewrite LEN in Hi; lia). apply HB. exact Hi.
Qed.

Lemma ro_cells_agree : forall m m' A cs,
  ro_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) -> ro_cells rsegs m' A cs.
Proof. intros m m' A cs H K. exact (cells_at_agree m m' A cs H K). Qed.

Lemma rw_cells_agree : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) <> None) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [HC (W0 & W1 & HW)] K D. split; [exact (cells_at_agree m m' A cs HC K)|].
  split; [exact W0|]. split; [exact W1|]. intros i Hi. unfold wview. specialize (D (A + i) ltac:(lia)). destruct (m' (wa (A + i))); congruence.
Qed.

Lemma ro_of_rw : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma cells_at_app_r : forall m A cs1 cs2, cells_at rsegs m A (cs1 ++ cs2) -> cells_at rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [Hwf HB]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in HB. apply bytes_at_app in HB as [_ HB]. rewrite (cells_bytes_length cs1 W1) in HB.
  split; [exact W2| exact HB].
Qed.

Lemma ro_cells_skip1 : forall m A c cs, ro_cells rsegs m A (c :: cs) -> ro_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. pose proof (cells_at_app_r m A [c] cs H) as H'. cbn [cells_size] in H'. rewrite Nat.add_0_r in H'. exact H'.
Qed.

(* [comment removed for export] *)
Lemma u8_of_u64 : forall M a v, L5.u64_at rsegs M a v -> 0 <= v < 2 ^ 64 -> L5.u8_at rsegs M a (v mod 256).
Proof.
  intros M a v H Hv. unfold L5.u64_at in H. unfold L5.u8_at.
  rewrite rdn_unfold in H. rewrite rdn_unfold. cbn [Nat.sub] in *.
  destruct (mrd rsegs M (Z_to_bv 64 a)) as [b|]; [|discriminate].
  destruct (rdn rsegs M (Z_to_bv 64 a + 1)%bv 7); [|discriminate].
  cbn in H. inversion H. cbn. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small v) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma defined_of_rdn : forall M a n bs, rdn rsegs M (Z_to_bv 64 a) n = Some bs ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= 0x10000 \/ 0x92000 <= a) -> L5.defined M a (Z.of_nat n).
Proof.
  intros M a n bs H Ha Hn OUT i Hi.
  pose proof (rdn_mrd M n a (Z.to_nat i) ltac:(lia) Ha Hn bs H) as R. rewrite Z2Nat.id in R by lia.
  rewrite ref_mrd_overlay in R by (rewrite wa_unsigned by lia; lia). unfold wa in R.
  intros E. rewrite E in R. symmetry in R. apply nth_error_None in R. pose proof (rdn_length _ _ _ _ H). lia.
Qed.

Lemma defined_at : forall M b n a, L5.defined M b n -> b <= a < b + n -> M (Z_to_bv 64 a) <> None.
Proof. intros M b n a D Ha. replace a with (b + (a - b)) by lia. apply D. lia. Qed.

(* [comment removed for export] *)
Lemma land_le_r : forall x y, 0 <= x -> 0 <= y -> Z.land x y <= y.
Proof.
  intros x y Hx Hy.
  assert (E : Z.lor (Z.land x y) (Z.ldiff y x) = y).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec. destruct (Z.testbit x i), (Z.testbit y i); reflexivity. }
  assert (D : Z.land (Z.land x y) (Z.ldiff y x) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0. destruct (Z.testbit x i), (Z.testbit y i); reflexivity. }
  pose proof (Z.add_lor_land (Z.land x y) (Z.ldiff y x)) as A. rewrite E, D in A.
  pose proof (proj2 (Z.ldiff_nonneg y x) (or_introl Hy)). lia.
Qed.
Lemma lor_le_add : forall x y, 0 <= x -> 0 <= y -> x <= Z.lor x y <= x + y.
Proof.
  intros x y Hx Hy. pose proof (Z.add_lor_land x y). pose proof (proj2 (Z.land_nonneg x y) (or_introl Hx)).
  pose proof (land_le_r x y Hx Hy). lia.
Qed.
Lemma str_cap_bound : forall n, 0 <= n -> n + 1 <= L5CSU.str_cap n <= n + 10.
Proof.
  intros n Hn. unfold L5CSU.str_cap. pose proof (lor_le_add n 7 Hn ltac:(lia)).
  destruct (Z.eqb_spec (Z.lor n 7) 23); lia.
Qed.

(* [comment removed for export] *)
Lemma ret_pc_lit : forall r, L5.ra_ok r -> ret_pc (Z_to_bv 64 r) = Z_to_bv 64 r.
Proof.
  intros r [Hr He]. apply bv_eq. unfold ret_pc. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z.
  rewrite Z_land_m2_wrap. rewrite Hoare.land_m2_even by exact He. reflexivity.
Qed.
End SCFG_1.

End TKU.
