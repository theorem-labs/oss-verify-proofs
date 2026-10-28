(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TWB.
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

Lemma fs_off_image : forall a n, 0xf8000 <= a -> 1 <= n -> find_segment CSEGS a n = None.
Proof.
  intros a n Ha Hn. destruct (find_segment CSEGS a n) as [seg|] eqn:E; [|reflexivity].
  exfalso. destruct (find_segment_in _ _ _ _ E) as (Hin & B1 & B2).
  unfold CSEGS, Ubsan.M.loaded_segments, Ubsan_loaded_segments in Hin.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    unfold Ubsan_segment_000, Ubsan_segment_001,
           Ubsan_segment_002, Ubsan_segment_003 in *;
    cbn [seg_base seg_size] in *; lia.
Qed.
Lemma rom_off_image : forall a, 0xf8000 <= bv_unsigned a -> seg_rom CSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite (fs_off_image _ _ Ha) by (cbn; lia). reflexivity.
Qed.

Lemma bytes_defined : forall m A bs, bytes_at CSEGS m A bs -> 0xf8000 <= A -> L5.defined m A (Z.of_nat (length bs)).
Proof.
  intros m A bs (H0 & H1 & HB) HA i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  unfold mrd in HB. destruct (m (wa (A + i))) eqn:E; [unfold wa in E; rewrite E; discriminate|].
  rewrite rom_off_image in HB by (unfold wa; rewrite unsigned_lit by lia; lia).
  symmetry in HB. apply nth_error_None in HB. lia.
Qed.
Lemma rw_defined : forall m A cs, rw_cells CSEGS m A cs -> 0xf8000 <= A -> L5.defined m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs [[Hwf HB] _] HA. rewrite <- (cells_bytes_length cs Hwf). exact (bytes_defined m A _ HB HA).
Qed.
Lemma u8arr_defined : forall m A bs, u8arr CSEGS m A bs -> 0xf8000 <= A -> L5.defined m A (Z.of_nat (length bs)).
Proof. intros m A bs [HB _] HA. exact (bytes_defined m A bs HB HA). Qed.
Lemma stk_defined : forall m lo hi, stk CSEGS m lo hi -> 0xf8000 <= lo -> lo <= hi -> L5.defined m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & HS) Hlo Hle i Hi. destruct (HS (lo + i) ltac:(lia)) as [_ [b Hb]].
  unfold mrd in Hb. destruct (m (wa (lo + i))) eqn:E; [unfold wa in E; rewrite E; discriminate|].
  rewrite rom_off_image in Hb by (unfold wa; rewrite unsigned_lit by lia; lia). discriminate Hb.
Qed.

Lemma u8_of_u8arr : forall m A bs i b, u8arr CSEGS m A bs -> nth_error bs i = Some b -> L5.u8_at CSEGS m (A + Z.of_nat i) (bv_unsigned b).
Proof.
  intros m A bs i b [(H0 & H1 & HB) _] Hb. unfold L5.u8_at. cbn [rdn].
  pose proof (HB i ltac:(apply nth_error_Some; rewrite Hb; discriminate)) as E. rewrite Hb in E. unfold mrd in E.
  change (Z_to_bv 64 (A + Z.of_nat i)) with (wa (A + Z.of_nat i)). rewrite E. rewrite (definitions.Z_to_bv_bv_unsigned 8 b). reflexivity.
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

Lemma rdn_bytes_at : forall m n a bs, rdn CSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> bytes_at CSEGS m a bs.
Proof.
  intros m n. induction n as [|n IH]; intros a bs H H0 H1.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [rdn] in H. destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom CSEGS (Z_to_bv 64 a) end) as [b|] eqn:Eb; [|discriminate].
    rewrite (L5C.add1_lit a) in H. destruct (rdn CSEGS m (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) rest Er ltac:(lia) ltac:(lia)) as (_ & Hl & HB).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth_error]. rewrite Z.add_0_r. unfold mrd, wa. exact Eb.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply HB. cbn [length] in Hi. lia.
Qed.

Lemma kw8_of_cell : forall E M A cs k w a v, rw_cells CSEGS M A cs -> cell_at cs k = Some (C8 w) ->
  estart E a = A + Z.of_nat k -> 0 <= A + Z.of_nat k -> A + Z.of_nat k + 8 <= 2 ^ 64 -> edenot E v = w -> kentry_ok CSEGS E M (KWord a 8 v).
Proof.
  intros E M A cs k w a v [HC _] Hc Ha H0 H8 Hv. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 8)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. rewrite <- ov_rdn.
  exact (cells_at_read CSEGS M A cs k (C8 w) HC Hc).
Qed.
Lemma kw4_of_cell : forall E M A cs k w a v, rw_cells CSEGS M A cs -> cell_at cs k = Some (C4 w) ->
  estart E a = A + Z.of_nat k -> 0 <= A + Z.of_nat k -> A + Z.of_nat k + 4 <= 2 ^ 64 -> edenot E v = w -> kentry_ok CSEGS E M (KWord a 4 v).
Proof.
  intros E M A cs k w a v [HC _] Hc Ha H0 H8 Hv. cbn [kentry_ok].
  assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. rewrite <- ov_rdn.
  exact (cells_at_read CSEGS M A cs k (C4 w) HC Hc).
Qed.
End TWB.
