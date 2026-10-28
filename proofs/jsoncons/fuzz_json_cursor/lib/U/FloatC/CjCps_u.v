(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim ShapeAlg SpinAlg L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pad_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation CSEGS := Ubsan.M.loaded_segments.

Section Bridge.
Context {SCFG_P : ScfgP}.

Lemma cj_evt_srz : forall (fx : FPState) (R : bvmap 5 word) (pc : word) (M : word -> option byte) (rom : word -> option byte)
    (model : Model) (K : TSet) (Q : machine_state -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  evt CSEGS Q (MS (canon_regs R) (@fp_regs fx) pc (@fp_csr fx) None M rom) ->
  (forall ms1 ms1', Q ms1 -> ms_eqv ms1 ms1' -> srealizes CSEGS SCFG (mkCfg ms1' model) K) ->
  srealizes CSEGS SCFG (mkCfg (@mkst fx R pc M rom) model) K.
Proof.
  intros fx R pc M rom model K Q Hh Hl E C.
  destruct (evt_eqv_transfer CSEGS _ _ _ (mkst_eqv_canon (fx := fx) R pc M rom) E) as (ms1 & ms1' & HQ & Heqv1 & Hms).
  eapply srz_msteps; [exact Hh | exact Hl | exact Hms | ]. exact (C ms1 ms1' HQ Heqv1).
Qed.

End Bridge.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s0 segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - injection H as <-. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. split; assumption.
  - destruct (IH a n seg H) as (Hin & B1 & B2). split; [right; exact Hin|]. split; assumption.
Qed.

Lemma ro_addr_range : forall a, ro_addr CSEGS a = true -> (0x10000 <= bv_unsigned a < 0xbd000)%Z.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment CSEGS (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  destruct (find_segment_in _ _ _ _ E) as (Hin & B1 & B2).
  unfold CSEGS, Ubsan.M.loaded_segments, Ubsan_loaded_segments in Hin.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold Ubsan_segment_000, Ubsan_segment_001,
           Ubsan_segment_002, Ubsan_segment_003 in *;
    cbn [seg_base seg_size seg_perms] in *.
  - lia.
  - lia.
  - vm_compute in H. discriminate.
  - vm_compute in H. discriminate.
Qed.

Lemma mem_inv_of_clear : forall M, L5.img_clear M 0x10000 0xbd000 -> mem_inv CSEGS M.
Proof.
  intros M C a b E. destruct (ro_addr CSEGS a) eqn:R; [|reflexivity]. exfalso.
  apply ro_addr_range in R. specialize (C (bv_unsigned a) R). rewrite Z_to_bv_bv_unsigned in C. congruence.
Qed.

Definition ovl_bytes (M : word -> option byte) (a : Z) (n : nat) : list byte :=
  map (fun i => match M (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n).
Lemma ovl_bytes_length : forall M a n, length (ovl_bytes M a n) = n.
Proof. intros. unfold ovl_bytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma ovl_bytes_nth : forall M a n i, (i < n)%nat -> M (wa (a + Z.of_nat i)) <> None ->
  M (wa (a + Z.of_nat i)) = nth_error (ovl_bytes M a n) i.
Proof.
  intros M a n i Hi HD. unfold ovl_bytes. rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map].
  rewrite Nat.add_0_l. destruct (M (wa (a + Z.of_nat i))) eqn:E; [reflexivity| contradiction].
Qed.

Lemma defined_rw_cells : forall M a n, L5.defined M a (Z.of_nat n) -> (0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
  rw_cells CSEGS M a [CB n (ovl_bytes M a n)].
Proof.
  intros M a n HD H0 H1. split; [split|].
  - cbn. rewrite ovl_bytes_length. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. split; [rewrite ovl_bytes_length; exact H1|].
    intros i Hi. rewrite ovl_bytes_length in Hi. unfold mrd.
    assert (ND : M (wa (a + Z.of_nat i)) <> None) by (apply HD; lia).
    rewrite <- (ovl_bytes_nth M a n i Hi ND). destruct (M (wa (a + Z.of_nat i))); [reflexivity| contradiction].
  - split; [exact H0|]. split; [cbn; lia|]. intros i Hi. unfold wview.
    assert (ND : M (wa (a + i)) <> None) by (apply HD; cbn in Hi; lia).
    destruct (M (wa (a + i))); [discriminate| contradiction].
Qed.

Lemma stk_of_defined : forall M lo hi, L5.defined M lo (hi - lo) -> (0 <= lo)%Z -> (lo <= hi <= 2^64)%Z -> stk CSEGS M lo hi.
Proof.
  intros M lo hi HD H0 H1. split; [exact H0|]. split; [lia|]. intros a Ha.
  assert (ND : M (wa a) <> None) by (replace a with (lo + (a - lo))%Z by lia; apply HD; lia).
  unfold wview, mrd. destruct (M (wa a)) as [b|]; [| contradiction]. split; [discriminate| exists b; reflexivity].
Qed.

Lemma got_slot_rom : forall i, (i < 8)%nat -> seg_rom CSEGS (wa (0xc3a48 + Z.of_nat i)) = nth_error (le8 (Z_to_bv 64 0xf6a70)) i.
Proof. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; f_equal; apply bv_eq; reflexivity|]). lia. Qed.
Lemma got_slot_wview : forall M i, (i < 8)%nat -> M (wa (0xc3a48 + Z.of_nat i)) = None -> wview CSEGS M (wa (0xc3a48 + Z.of_nat i)) <> None.
Proof. intros M i Hi E. unfold wview. rewrite E. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma guard_rom : forall i, (i < 8)%nat -> seg_rom CSEGS (wa (0xf6a70 + Z.of_nat i)) <> None.
Proof. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma guard_wview : forall M i, (i < 8)%nat -> wview CSEGS M (wa (0xf6a70 + Z.of_nat i)) <> None.
Proof.
  intros M i Hi. unfold wview. destruct (M (wa (0xf6a70 + Z.of_nat i))); [discriminate|].
  do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia.
Qed.

Definition guard_bytes (M : word -> option byte) : list byte :=
  map (fun i => match mrd CSEGS M (wa (0xf6a70 + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 8).
Lemma guard_bytes_length : forall M, length (guard_bytes M) = 8%nat.
Proof. intros. reflexivity. Qed.

Lemma le8_of_bytes_c : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as HR. rewrite HL in HR. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma ssp_cells_c : forall M, L5.img_clear M 0x10000 0xc3a78 -> ssp_cells M (le_bytes_to_word (guard_bytes M)).
Proof.
  intros M C. unfold ssp_cells, got_ssp, ssp_guard. split.
  - split; [split|].
    + cbn. tauto.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_le8; lia|].
      intros i Hi. rewrite length_le8 in Hi. unfold mrd.
      pose proof (C (0xc3a48 + Z.of_nat i)%Z ltac:(lia)) as Ci. change (Z_to_bv 64 (0xc3a48 + Z.of_nat i)) with (wa (0xc3a48 + Z.of_nat i)) in Ci.
      rewrite Ci. apply got_slot_rom. exact Hi.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. apply got_slot_wview; [lia|].
      pose proof (C (0xc3a48 + Z.of_nat (Z.to_nat i))%Z ltac:(lia)) as Ci. exact Ci.
  - split; [split|].
    + cbn. tauto.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite le8_of_bytes_c by apply guard_bytes_length.
      split; [lia|]. split; [rewrite guard_bytes_length; lia|].
      intros i Hi. rewrite guard_bytes_length in Hi. unfold guard_bytes. rewrite nth_error_map.
      rewrite (nth_error_nth' (seq 0 8) 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map]. rewrite Nat.add_0_l.
      destruct (mrd CSEGS M (wa (0xf6a70 + Z.of_nat i))) eqn:E; [exact E|].
      exfalso. unfold mrd in E. destruct (M (wa (0xf6a70 + Z.of_nat i))); [discriminate|]. exact (guard_rom i Hi E).
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      replace i with (Z.of_nat (Z.to_nat i)) by lia. apply guard_wview. lia.
Qed.

Lemma wview_off_image : forall m a, (0xf8000 <= bv_unsigned a)%Z -> wview CSEGS m a = m a.
Proof.
  intros m a H. unfold wview. destruct (m a); [reflexivity|].
  destruct (find_segment CSEGS (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. destruct (find_segment_in _ _ _ _ E) as (Hin & B1 & B2).
  unfold CSEGS, Ubsan.M.loaded_segments, Ubsan_loaded_segments in Hin.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold Ubsan_segment_000, Ubsan_segment_001,
           Ubsan_segment_002, Ubsan_segment_003 in *;
    cbn [seg_base seg_size] in *; lia.
Qed.

Lemma bytes_at_L5 : forall m a (o : list Z) rest, bytes_at CSEGS m a (map (Z_to_bv 8) o ++ rest) -> L5.bytes_at CSEGS m a o.
Proof.
  intros m a o rest (H0 & H1 & HB) i Hi. unfold L5.u8_at.
  assert (Hi' : (i < length (map (Z_to_bv 8) o ++ rest))%nat) by (rewrite length_app, length_map; lia).
  pose proof (HB i Hi') as E. rewrite nth_error_app1 in E by (rewrite length_map; lia).
  rewrite nth_error_map in E. rewrite (nth_error_nth' o 0%Z Hi) in E. cbn [option_map] in E.
  rewrite rdn_unfold. change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)). rewrite E.
  rewrite rdn_unfold. reflexivity.
Qed.

Lemma munch2_frame_but : forall lo1 hi1 lo2 hi2 m m',
  munch [(lo1, hi1); (lo2, hi2)]%Z m m' -> L5.frame_but [(lo1, hi1 - lo1); (lo2, hi2 - lo2)]%Z m m'.
Proof.
  intros lo1 hi1 lo2 hi2 m m' MU x Hx. apply MU. cbn [outside].
  unfold L5.outside, L5.in_rng in Hx. cbn [fst snd] in Hx.
  split; [intros C; apply (Hx (lo1, hi1 - lo1)%Z); [left; reflexivity| cbn; lia]|].
  split; [intros C; apply (Hx (lo2, hi2 - lo2)%Z); [right; left; reflexivity| cbn; lia]| exact I].
Qed.
