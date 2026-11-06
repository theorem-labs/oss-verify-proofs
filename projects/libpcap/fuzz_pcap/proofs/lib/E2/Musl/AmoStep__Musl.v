(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr Bytes Mem PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From Stdlib Require Uint63.
From Corelib Require PrimString PrimStringAxioms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AmoStep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      (* [comment removed for export] *)
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.
End AmoStep.

(* [comment removed for export] *)
Module CellsExtra.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_split2 : forall segs m A c1 c2,
  rw_cells segs m A [c1; c2] -> rw_cells segs m A [c1] /\ rw_cells segs m (A + Z.of_nat (csize c1)) [c2].
Proof.
  intros segs m A c1 c2 H. apply (proj1 (rw_cells_app segs m A [c1] [c2])) in H.
  cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_join2 : forall segs m A c1 c2,
  rw_cells segs m A [c1] -> rw_cells segs m (A + Z.of_nat (csize c1)) [c2] -> rw_cells segs m A [c1; c2].
Proof.
  intros segs m A c1 c2 H1 H2. apply (proj2 (rw_cells_app segs m A [c1] [c2])).
  cbn [cells_size]. rewrite Nat.add_0_r. split; assumption.
Qed.
End CellsExtra.

(* [comment removed for export] *)
Module EntryRnd.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Mem PropExec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition at_random_lo (rnd : EntryDraw) : list byte := firstn 8 (at_random_bytes (ed_random rnd)).
Definition at_random_hi (rnd : EntryDraw) : list byte := skipn 8 (at_random_bytes (ed_random rnd)).

(* [comment removed for export] *)
Definition ssp_canary_bytes (rnd : EntryDraw) : list byte := upd (at_random_lo rnd) 1 (Z_to_bv 8 0).
Definition ssp_canary (rnd : EntryDraw) : word := le_bytes_to_word (ssp_canary_bytes rnd).
Definition malloc_secret (rnd : EntryDraw) : word := le_bytes_to_word (at_random_hi rnd).

Lemma at_random_split : forall rnd, at_random_bytes (ed_random rnd) = at_random_lo rnd ++ at_random_hi rnd.
Proof. intros rnd. symmetry. apply firstn_skipn. Qed.
Lemma length_at_random_lo : forall rnd, length (at_random_lo rnd) = 8%nat.
Proof. intros rnd. unfold at_random_lo. rewrite length_firstn, length_at_random_bytes. reflexivity. Qed.
Lemma length_at_random_hi : forall rnd, length (at_random_hi rnd) = 8%nat.
Proof. intros rnd. unfold at_random_hi. rewrite length_skipn, length_at_random_bytes. reflexivity. Qed.
Lemma length_ssp_canary_bytes : forall rnd, length (ssp_canary_bytes rnd) = 8%nat.
Proof. intros rnd. unfold ssp_canary_bytes. rewrite upd_length. apply length_at_random_lo. Qed.

(* [comment removed for export] *)
Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned.
  assert (Hr : (0 <= bytes_le_to_Z bs < 2^64)%Z).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R.
    rewrite length_map, Hl in R. change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in R. exact R. }
  rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le8_ssp_canary : forall rnd, le8 (ssp_canary rnd) = ssp_canary_bytes rnd.
Proof. intros rnd. apply le8_le_bytes_to_word, length_ssp_canary_bytes. Qed.
Lemma le8_malloc_secret : forall rnd, le8 (malloc_secret rnd) = at_random_hi rnd.
Proof. intros rnd. apply le8_le_bytes_to_word, length_at_random_hi. Qed.
(* [comment removed for export] *)
Lemma load_ssp_canary : forall rnd, bv_extract 0 64 (le_bytes_to_word (ssp_canary_bytes rnd)) = ssp_canary rnd.
Proof. intros rnd. rewrite <- le8_ssp_canary. apply load_u64. Qed.
Lemma load_malloc_secret : forall rnd, bv_extract 0 64 (le_bytes_to_word (at_random_hi rnd)) = malloc_secret rnd.
Proof. intros rnd. rewrite <- le8_malloc_secret. apply load_u64. Qed.

(* [comment removed for export] *)
Definition msec_of_rnd (rnd : EntryDraw) : MSEC := msec_of_words (malloc_secret rnd) (ssp_canary rnd).
Lemma msecret_of_rnd : forall rnd, @msecret (msec_of_rnd rnd) = bv_unsigned (malloc_secret rnd).
Proof. reflexivity. Qed.
Lemma mcanary_of_rnd : forall rnd, @mcanary (msec_of_rnd rnd) = ssp_canary rnd.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma wz_msecret_of_rnd : forall rnd, Z_to_bv 64 (@msecret (msec_of_rnd rnd)) = malloc_secret rnd.
Proof. intros rnd. rewrite msecret_of_rnd. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EntryImage.
  Variable segs : list Segment.
  Variables (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation bsb := (build_stack_bytes ph sp argv envp uid hw rnd).
  Notation esi := (entry_stack_image ph sp argv envp uid hw rnd).

  #[using="Type"] Lemma esi_app : esi = bsb ++ entry_slack sp bsb (ed_slack rnd).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma bsb_le_esi : (length bsb <= length esi)%nat.
  Proof. rewrite esi_app, length_app. lia. Qed.

  #[using="Type"] Lemma init_block_bytes :
    (stack_max_size <= bv_unsigned sp)%Z -> (bv_unsigned sp + Z.of_nat (length esi) <= 2^64)%Z ->
    bytes_at segs (wrap_mem ph sp argv envp uid hw rnd) (bv_unsigned sp) bsb.
  Proof.
    intros SPLO IMGHI. pose proof (init_stack_bytes segs ph sp argv envp uid hw rnd SPLO IMGHI) as B.
    rewrite esi_app in B. apply bytes_at_app in B. exact (proj1 B).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma entry_bounds : valid_sp sp -> entry_stack_fits sp argv envp ->
    (stack_max_size <= bv_unsigned sp)%Z /\ (bv_unsigned sp + Z.of_nat (length esi) <= sp_window_hi)%Z.
  Proof.
    intros (L & H & _) F. rewrite entry_stack_image_top. split.
    - unfold sp_window_lo, stack_max_size in *. lia.
    - apply entry_page_top_within_window. exact F.
  Qed.
End EntryImage.
End EntryRnd.

(* [comment removed for export] *)
Module ImgAny.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rw_any_pt : forall bs0 A (m : word -> option byte),
  rw_bytes_b segs A bs0 = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs0) <= 2^64)%Z ->
  exists bs, length bs = length bs0 /\
    forall i b, nth_error bs i = Some b ->
      mrd segs m (wa (A + Z.of_nat i)) = Some b /\ wview segs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs0 as [|b0 bs0 IH]; intros A m Hb HA Hl.
  - exists []. split; [reflexivity|]. intros [|i] b Hn; discriminate.
  - cbn [rw_bytes_b] in Hb.
    destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
    destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
    apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl.
    destruct (IH (A + 1)%Z m Hb ltac:(lia) ltac:(lia)) as (bs & Hlen & Hbs).
    exists ((match m (wa A) with Some b => b | None => b' end) :: bs). split; [cbn [length]; lia|].
    intros [|i] b Hn.
    + cbn in Hn. injection Hn as <-. rewrite Z.add_0_r. unfold mrd, wview in *.
      destruct (m (wa A)) as [bm|] eqn:Em.
      * split; [reflexivity| discriminate].
      * split; [exact Er|]. intros C. rewrite C in Ew. discriminate.
    + cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. exact (Hbs i b Hn).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_any : forall (m : word -> option byte) A bs0,
  rw_bytes_b segs A bs0 = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs0) <= 2^64)%Z ->
  exists bs, length bs = length bs0 /\ rw_cells segs m A [CB (length bs0) bs].
Proof.
  intros m A bs0 Hb HA Hl. destruct (rw_any_pt bs0 A m Hb HA Hl) as (bs & Hlen & G).
  exists bs. split; [exact Hlen|]. rewrite <- Hlen.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. { apply (proj1 (G i b E)). } apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E. { apply (proj2 (G _ b E)). } apply nth_error_None in E. lia.
Qed.
End WithSegs.
End ImgAny.

(* [comment removed for export] *)
Module RwZero.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From Corelib Require Import PrimString PrimStringAxioms.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Mem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition rz_c0 : char63 := 48%uint63.

Definition zwin (s : PrimString.string) (off len : int) : bool :=
  match PrimString.compare (PrimString.sub s off len) (PrimString.make len rz_c0) with Eq => true | _ => false end.

Lemma rz_int_compare_eq : forall x y : int, PrimInt63.compare x y = Eq -> x = y.
Proof. intros x y H. apply to_Z_inj. apply Z.compare_eq. rewrite <- Uint63.compare_spec. exact H. Qed.

Lemma rz_list_compare_eq : forall l1 l2 : list int, ListDef.list_compare PrimInt63.compare l1 l2 = Eq -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  destruct (PrimInt63.compare x y) eqn:E; try discriminate.
  apply rz_int_compare_eq in E. subst y. f_equal. exact (IH _ H).
Qed.

Lemma rz_nth_firstn_skipn : forall {A} (l : list A) (o n k : nat) (d : A), (k < n)%nat ->
  nth k (firstn n (skipn o l)) d = nth (o + k) l d.
Proof.
  intros A l o n k d Hk. rewrite nth_firstn. destruct (Nat.ltb_spec k n) as [_|X]; [|lia].
  rewrite nth_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zwin_get : forall s off len (i : int),
  zwin s off len = true ->
  (to_Z len <= to_Z PrimString.max_length)%Z ->
  (to_Z off <= to_Z i < to_Z off + to_Z len)%Z ->
  PrimString.get s i = rz_c0 /\ (to_Z off + to_Z len <= to_Z (PrimString.length s))%Z.
Proof.
  intros s off len i Hz Hmax Hi. unfold zwin in Hz.
  destruct (PrimString.compare (PrimString.sub s off len) (PrimString.make len rz_c0)) eqn:E; try discriminate. clear Hz.
  rewrite PrimStringAxioms.compare_spec in E. apply rz_list_compare_eq in E.
  rewrite PrimStringAxioms.sub_spec, PrimStringAxioms.make_spec in E.
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl. pose proof (to_Z_bounded i) as Bi.
  rewrite Nat.min_l in E by lia.
  change (PrimInt63.land rz_c0 255%uint63) with rz_c0 in E.
  assert (HL : (Z.to_nat (to_Z off) + Z.to_nat (to_Z len) <= length (to_list s))%nat).
  { pose proof (f_equal (@length _) E) as EL. rewrite repeat_length, length_firstn, length_skipn in EL. lia. }
  split.
  - rewrite PrimStringAxioms.get_spec.
    set (k := (Z.to_nat (to_Z i) - Z.to_nat (to_Z off))%nat).
    assert (Hk : (k < Z.to_nat (to_Z len))%nat) by (unfold k; lia).
    pose proof (rz_nth_firstn_skipn (to_list s) (Z.to_nat (to_Z off)) (Z.to_nat (to_Z len)) k 0%uint63 Hk) as N.
    rewrite E in N. rewrite nth_repeat_lt in N by exact Hk.
    replace (Z.to_nat (to_Z off) + k)%nat with (Z.to_nat (to_Z i)) in N by (unfold k; lia). symmetry. exact N.
  - pose proof (PrimStringAxioms.length_spec s) as LS. pose proof (to_Z_bounded (PrimString.length s)) as BL. lia.
Qed.

Lemma rz_hex_nybble_c0 : hex_nybble rz_c0 = 0%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zwin_hex_byte_at : forall s off len (i : N),
  zwin s off len = true ->
  (to_Z len <= to_Z PrimString.max_length)%Z ->
  (to_Z off <= Z.of_N (2 * i))%Z -> (Z.of_N (2 * i + 1) < to_Z off + to_Z len)%Z ->
  hex_byte_at s i = Some (Z_to_bv 8 0).
Proof.
  intros s off len i Hz Hmax H1 H2.
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl.
  pose proof (to_Z_bounded PrimString.max_length) as Bm. change (to_Z PrimString.max_length) with 16777211%Z in *.
  pose proof (to_Z_bounded (PrimString.length s)) as BL.
  destruct (zwin_get s off len off Hz Hmax ltac:(lia)) as [_ HLs].
  assert (E0 : to_Z (of_Z (Z.of_N (2 * i))) = Z.of_N (2 * i)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  assert (E1 : to_Z (of_Z (Z.of_N (2 * i + 1))) = Z.of_N (2 * i + 1)) by (rewrite of_Z_spec; apply Z.mod_small; lia).
  destruct (zwin_get s off len (of_Z (Z.of_N (2 * i))) Hz Hmax ltac:(rewrite E0; lia)) as [G0 _].
  destruct (zwin_get s off len (of_Z (Z.of_N (2 * i + 1))) Hz Hmax ltac:(rewrite E1; lia)) as [G1 _].
  unfold hex_byte_at. cbv zeta.
  assert (HLT : (of_Z (Z.of_N (2 * i + 1)) <? PrimString.length s)%uint63 = true) by (apply ltb_spec; rewrite E1; lia).
  rewrite HLT. cbn [orb]. rewrite G0, G1, rz_hex_nybble_c0. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma rz_find_segment : forall (pre : list Segment) (sg : Segment) (rest : list Segment) (lo hi a : Z),
  Forall (fun g => (Z.of_N (seg_base g) + Z.of_N (seg_size g) <= lo)%Z) pre ->
  (Z.of_N (seg_base sg) <= lo)%Z -> (hi <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg))%Z ->
  (lo <= a)%Z -> (a + 1 <= hi)%Z ->
  find_segment (pre ++ sg :: rest) a 1 = Some sg.
Proof.
  induction pre as [|g pre IH]; intros sg rest lo hi a Hp Hb Ht Ha Hh.
  - cbn [app find_segment]. cbv zeta.
    replace (Z.of_N (seg_base sg) <=? a)%Z with true by (symmetry; apply Z.leb_le; lia).
    replace (a + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))%Z with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
  - inversion Hp as [|g' pre' Hg Hp' E]; subst g' pre'. cbn [app find_segment]. cbv zeta.
    replace (a + 1 <=? Z.of_N (seg_base g) + Z.of_N (seg_size g))%Z with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r. exact (IH sg rest lo hi a Hp' Hb Ht Ha Hh).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RZ.
Variable segs : list Segment.
Variables (seg : Segment) (s : PrimString.string).
Hypothesis SEGB : seg_bytes seg = [s].
Hypothesis SEGR : seg_readable seg = true.
Hypothesis SEGW : seg_writable seg = true.

(* [comment removed for export] *)
Lemma rz_segment_byte_at : forall off len (o : N),
  zwin s off len = true -> (to_Z len <= to_Z PrimString.max_length)%Z ->
  (to_Z off <= Z.of_N (2 * o))%Z -> (Z.of_N (2 * o + 1) < to_Z off + to_Z len)%Z ->
  segment_byte_at (seg_bytes seg) o = Some (Z_to_bv 8 0).
Proof using SEGB.
  intros off len o Hz Hmax H1 H2. rewrite SEGB. cbn [segment_byte_at].
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded len) as Bl.
  destruct (zwin_get s off len off Hz Hmax ltac:(lia)) as [_ HLs].
  assert (Hc : (o <? Z.to_N (to_Z (PrimString.length s) / 2))%N = true).
  { apply N.ltb_lt. apply N2Z.inj_lt. rewrite Z2N.id by (apply Z.div_pos; [pose proof (to_Z_bounded (PrimString.length s)); lia | lia]).
    apply Z.lt_le_trans with (Z.of_N o + 1)%Z; [lia|]. apply Z.div_le_lower_bound; lia. }
  rewrite Hc. exact (zwin_hex_byte_at s off len o Hz Hmax H1 H2).
Qed.

Lemma rw_bytes_b_zero : forall off len (n : nat) (A : Z),
  zwin s off len = true -> (to_Z len <= to_Z PrimString.max_length)%Z ->
  (forall a, (A <= a < A + Z.of_nat n)%Z -> find_segment segs a 1 = Some seg) ->
  (Z.of_N (seg_base seg) <= A)%Z -> (0 <= A)%Z -> (A + Z.of_nat n <= 2^64)%Z ->
  (to_Z off <= 2 * (A - Z.of_N (seg_base seg)))%Z ->
  (2 * (A - Z.of_N (seg_base seg) + Z.of_nat n) <= to_Z off + to_Z len)%Z ->
  rw_bytes_b segs A (repeat (Z_to_bv 8 0) n) = true.
Proof using SEGB SEGR SEGW.
  intros off len n. induction n as [|n IH]; intros A Hz Hmax HF HB HA HT Ho Hl; [reflexivity|].
  cbn [repeat rw_bytes_b].
  assert (EU : bv_unsigned (wa A) = A) by (apply wa_unsigned; lia).
  assert (HFA : find_segment segs A 1 = Some seg) by (apply HF; lia).
  set (o := Z.to_N (A - Z.of_N (seg_base seg))).
  assert (Eo : Z.of_N o = (A - Z.of_N (seg_base seg))%Z) by (unfold o; rewrite Z2N.id; lia).
  assert (HSB : segment_byte_at (seg_bytes seg) o = Some (Z_to_bv 8 0)).
  { apply (rz_segment_byte_at off len o Hz Hmax); rewrite ?N2Z.inj_add, ?N2Z.inj_mul, Eo; lia. }
  assert (HR : seg_rom segs (wa A) = Some (Z_to_bv 8 0)).
  { unfold seg_rom, memory_read. rewrite EU. change (Z.of_N 1) with 1%Z. rewrite HFA, SEGR.
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. fold o. rewrite HSB. reflexivity. }
  assert (HW : wview segs (fun _ => None) (wa A) = Some (Z_to_bv 8 0)).
  { unfold wview. rewrite EU, HFA, SEGW. fold o. exact HSB. }
  rewrite HR, HW. apply andb_true_intro. split.
  - unfold bv_eqb. apply Z.eqb_refl.
  - apply (IH (A + 1)%Z Hz Hmax).
    + intros a Ha. apply HF. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.
End RZ.
End RwZero.

(* [comment removed for export] *)
Module STRW_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
  u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof.
  intros segs m A n bs i k a ARR LEN (Hi & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
  u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
  mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
  ms_facts A n i k -> a = wa (A + i) ->
  u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
  filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
  length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
  mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
  wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
  intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
  assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
  { rewrite repeat_length. eapply ms_store_ok; eauto. }
  destruct MF as (Hi & Hk & A0 & An). subst a.
  split; [|split; [|split; [|split; [|split]]]].
  - apply (u8arr_write_bytes segs m A bs i _ ARR); [lia|]. rewrite repeat_length, LEN. lia.
  - apply filled_updZ; [exact FIL | lia | rewrite LEN; lia].
  - rewrite upd_bytes_length; [exact LEN|]. rewrite repeat_length, LEN. lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | rewrite repeat_length; lia |]. cbn [inside]. left. rewrite repeat_length. lia.
  - apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)
Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.

End STRW_memset.

(* [comment removed for export] *)
Module STRW_merge.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).
Local Notation M64 := 18446744073709551616%Z.

(* [comment removed for export] *)
Definition v4 (b0 b1 b2 b3 : byte) : Z :=
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.

Local Ltac br b := pose proof (byte_range b).

Lemma lw_u b0 b1 b2 b3 :
  bv_unsigned (LW [b0;b1;b2;b3]) = v4 b0 b1 b2 b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof. rewrite lw_unsigned4. reflexivity. Qed.

Lemma lw_wrap32 b0 b1 b2 b3 : bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3])) = v4 b0 b1 b2 b3.
Proof.
  rewrite lw_u, bv_wrap32_eq. br b0; br b1; br b2; br b3. unfold v4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lw_mod32 b0 b1 b2 b3 : (bv_unsigned (LW [b0;b1;b2;b3])) mod 2^32 = v4 b0 b1 b2 b3.
Proof. rewrite <- bv_wrap32_eq. apply lw_wrap32. Qed.

Lemma swrap32_small x : 0 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros. rewrite bv_swrap32_eq. rewrite Z.mod_small; lia. Qed.
Lemma mod64_small x : 0 <= x < 2^64 -> x mod M64 = x.
Proof. intros. apply Z.mod_small. lia. Qed.
Lemma mod32_small x : 0 <= x < 2^32 -> x mod 2^32 = x.
Proof. intros. apply Z.mod_small. lia. Qed.

Lemma swrap32_mod32 x : (bv_swrap 32 x) mod 2^32 = x mod 2^32.
Proof. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma mod64_mod32 x : (x mod M64) mod 2^32 = x mod 2^32.
Proof. Z.div_mod_to_equations. lia. Qed.

Lemma lor_mod32 a b : (Z.lor a b) mod 2^32 = Z.lor (a mod 2^32) (b mod 2^32).
Proof. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.

Lemma shl_mod32 x j : 0 <= j -> (Z.shiftl x j) mod 2^32 = ((x mod 2^32) * 2^j) mod 2^32.
Proof. intros. rewrite Z.shiftl_mul_pow2, <- Zmult_mod_idemp_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le4_lit_of_mod32 z (bs : list byte) : length bs = 4%nat ->
  (z mod M64) mod 2^32 = le_val (map bv_unsigned bs) -> le4 (Z_to_bv 64 z) = bs.
Proof.
  intros Hl Hz. apply le4_of_mod32; [exact Hl|]. rewrite unsigned_lit_wrap. exact Hz.
Qed.
Lemma le1_lit_of_mod8 z (b : byte) :
  (z mod M64) mod 2^8 = bv_unsigned b -> le1 (Z_to_bv 64 z) = [b].
Proof. intros Hz. apply le1_of_mod8. rewrite unsigned_lit_wrap. exact Hz. Qed.

Section merge.
  Variables b0 b1 b2 b3 c0 c1 c2 c3 : byte.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lo24 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64 mod 2^32 = bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^24) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  #[using="Type"] Lemma lo16 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64 mod 2^32 = bv_unsigned b2 + 256 * bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.
  #[using="Type"] Lemma lo8 : (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64 mod 2^32 = bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3.
  Proof.
    rewrite lw_wrap32, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite swrap32_small, mod64_small by lia. apply Z.mod_small. lia.
  Qed.

  #[using="Type"] Lemma hi8 : (v4 c0 c1 c2 c3 * 2^8) mod 2^32 = 256 * bv_unsigned c0 + 65536 * bv_unsigned c1 + 16777216 * bv_unsigned c2.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  #[using="Type"] Lemma hi16 : (v4 c0 c1 c2 c3 * 2^16) mod 2^32 = 65536 * bv_unsigned c0 + 16777216 * bv_unsigned c1.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.
  #[using="Type"] Lemma hi24 : (v4 c0 c1 c2 c3 * 2^24) mod 2^32 = 16777216 * bv_unsigned c0.
  Proof. br c0; br c1; br c2; br c3. unfold v4. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hi_a j : 0 <= j -> ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j)) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
  Proof. intros. rewrite mod64_mod32, swrap32_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.
  #[using="Type"] Lemma hi_r j : 0 <= j -> ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) j) mod M64) mod 2^32 = (v4 c0 c1 c2 c3 * 2^j) mod 2^32.
  Proof. intros. rewrite mod64_mod32, shl_mod32, lw_mod32 by lia. reflexivity. Qed.

  Local Ltac merge_tac lo hi hik k :=
    apply le4_lit_of_mod32; [reflexivity|];
    rewrite mod64_mod32, lor_mod32, lo, hi, hik by lia; cbn [map le_val];
    br b0; br b1; br b2; br b3; br c0; br c1; br c2; br c3;
    first [ rewrite (lor_add' _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ]
          | rewrite (lor_add _ _ k); [ lia | lia | lia | Z.div_mod_to_equations; lia ] ].

  (* [comment removed for export] *)
  #[using="Type"] Lemma merge_a24 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8)) mod M64)))
    = [b3; c0; c1; c2].
  Proof. merge_tac lo24 hi_a hi8 8%Z. Qed.
  #[using="Type"] Lemma merge_a16 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16)) mod M64)))
    = [b2; b3; c0; c1].
  Proof. merge_tac lo16 hi_a hi16 16%Z. Qed.
  #[using="Type"] Lemma merge_a8 :
    le4 (Z_to_bv 64 (Z.lor ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)
                            ((bv_swrap 32 (Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24)) mod M64)))
    = [b1; b2; b3; c0].
  Proof. merge_tac lo8 hi_a hi24 24%Z. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma merge_r24 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 8) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 24)) mod M64)))
    = [b3; c0; c1; c2].
  Proof. merge_tac lo24 hi_r hi8 8%Z. Qed.
  #[using="Type"] Lemma merge_r16 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 16) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 16)) mod M64)))
    = [b2; b3; c0; c1].
  Proof. merge_tac lo16 hi_r hi16 16%Z. Qed.
  #[using="Type"] Lemma merge_r8 :
    le4 (Z_to_bv 64 (Z.lor ((Z.shiftl (bv_unsigned (LW [c0;c1;c2;c3])) 24) mod M64)
                            ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (LW [b0;b1;b2;b3]))) 8)) mod M64)))
    = [b1; b2; b3; c0].
  Proof. merge_tac lo8 hi_r hi24 24%Z. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lwb0 : le1 (LW [b0;b1;b2;b3]) = [b0].
  Proof.
    apply le1_of_mod8. rewrite lw_u. br b0; br b1; br b2; br b3. unfold v4.
    Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma lwb1 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 8)) = [b1].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^8) with (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 + (2^56 - 2^24) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
  #[using="Type"] Lemma lwb2 : le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (LW [b0;b1;b2;b3])) 16)) = [b2].
  Proof.
    apply le1_lit_of_mod8. rewrite lw_u, Z.shiftr_div_pow2 by lia. br b0; br b1; br b2; br b3. unfold v4.
    replace (_ / 2^16) with (bv_unsigned b2 + 256 * bv_unsigned b3 + (2^48 - 2^16) * (bv_unsigned b3 / 128))
      by (Z.div_mod_to_equations; lia).
    rewrite mod64_small by lia. Z.div_mod_to_equations. lia.
  Qed.
End merge.
End STRW_merge.

(* [comment removed for export] *)
Module STRW_tac.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_merge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

(* [comment removed for export] *)
Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

(* [comment removed for export] *)
Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)
Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
  (0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
  eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
  rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
  intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
  assert (L : (Z.to_nat base + kw <= length src)%nat).
  { apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
  exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
  - apply (bytes_at_read segs m S src i 4 SRC); lia.
  - eapply window_sub; eauto; lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
  intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
  intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
         (Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
  pose proof (proj1 CP) as Lbs.
  assert (SOK : store_ok segs m1 a (length xs) = true).
  { rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
  subst a. split; [|split; [|split; [|split; [|split]]]].
  - apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
  - apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
  - apply (f_equal (@length byte)) in CP || idtac.
    rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
    rewrite Hl, Hxs. eapply window_sub; eauto; lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)
Ltac ld1 HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
                  ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
    zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
  end end.

(* [comment removed for export] *)
Ltac ld4 HW c w :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
    destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
      as [w [RD [Ew Lw]]];
    cbn [firstn skipn] in Ew;
    zstep; try clear RD
  end end.

(* [comment removed for export] *)
Ltac zify_bytes :=
  repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch type of b with
      | byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
      end
  end.
Ltac solve_le K :=
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
  cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
  zify_bytes;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
  lazymatch K with
  | 0%Z => idtac
  | _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
               | rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
  end;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)
Ltac by_le K :=
  symmetry;
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first
    [ lazymatch goal with
      | |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
          lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
      | |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
          lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
      | |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
          lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
      | |- le1 (sext _ _) = _ => apply lwb0
      end
    | solve_le K ].

(* [comment removed for export] *)
Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

(* [comment removed for export] *)
Ltac cst HW c k bytes_tac :=
  lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

(* [comment removed for export] *)
Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

(* [comment removed for export] *)
Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

(* [comment removed for export] *)
Ltac cp_norm P' :=
  lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

(* [comment removed for export] *)
Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
    (m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
  bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
  mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

(* [comment removed for export] *)
Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

(* [comment removed for export] *)
Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

(* [comment removed for export] *)
Ltac finish2 :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac mc_fin :=
  lazymatch goal with
  | DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
      let E := fresh "E" in
      pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
      apply rw_cells_of_u8arr in DST; rewrite L in DST
  end;
  finish2.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := zstep; fix_lit_store.
End STRW_tac.
