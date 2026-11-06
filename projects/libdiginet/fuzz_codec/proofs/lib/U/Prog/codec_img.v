From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Step Image.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** The facts of the UBSan image of fuzz_codec that the proofs of its own functions read, each proved by
    computation over the image (Img0). Three kinds:
    - read-only data (.rodata, so [mem_inv] makes every load read the image): the three jump tables of
      LLVMFuzzerTestOneInput (entries as the pcs they select), DESK, the seg7 table of diginet_seg7, the five
      strings check_personality passes, and the segment strings the GLYPH entries point to;
    - the tables in .data.rel.ro (a writable segment, so a premise says that memory there still holds the image
      bytes): SPEC_DESK, SPEC_C24, SPEC_PC, GLYPH and the library's personalities[], one 568-byte block;
    - the multiply-shift identities the compiler used for op / 15, q % 3, x % 25 and v % 65, each over the whole
      domain its operand has (a byte, op / 15 <= 17, a byte, a u16). *)

(** * Checks over a finite range of Z *)

Fixpoint zall (P : Z -> bool) (x : Z) (n : nat) : bool :=
  match n with O => true | S n' => P x && zall P (x + 1) n' end.

Lemma zall_spec : forall P n x, zall P x n = true -> forall y, x <= y < x + Z.of_nat n -> P y = true.
Proof.
  intros P n. induction n as [|n IH]; intros x H y Hy; [lia|].
  cbn [zall] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct (Z.eq_dec y x) as [->|Hne]; [exact H1|].
  apply (IH (x + 1) H2). lia.
Qed.

Lemma zall_range : forall P lo hi, zall P lo (Z.to_nat (hi - lo)) = true -> forall y, lo <= y < hi -> P y = true.
Proof.
  intros P lo hi H y Hy. apply (zall_spec P (Z.to_nat (hi - lo)) lo H). rewrite Z2Nat.id by lia. lia.
Qed.

(** * Reading the image *)

Section Kit.
Variable segs : list Segment.

(** The image holds [bs] at [A] (no condition on the segment's permissions). *)
Fixpoint img_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A) with
      | Some b' => bv_eqb b b' && img_bytes_b (A + 1) bs'
      | None => false
      end
  end.

Lemma img_bytes_b_nth : forall bs A (i : nat), img_bytes_b A bs = true -> (i < length bs)%nat ->
  seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros A i H Hi; cbn in Hi; [lia|].
  cbn [img_bytes_b] in H. destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i].
  - cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) i H2) by lia.
    replace (A + 1 + Z.of_nat i) with (A + Z.of_nat (S i)) by lia. reflexivity.
Qed.

Lemma img_bytes_b_image : forall bs A, img_bytes_b A bs = true -> image_bytes segs A (length bs) = Some bs.
Proof.
  induction bs as [|b bs IH]; intros A H; [reflexivity|].
  cbn [img_bytes_b] in H. destruct (seg_rom segs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  cbn [length image_bytes]. rewrite E, (IH (A + 1) H2). reflexivity.
Qed.

(** Memory that agrees with the image on [B, B + L) holds there what the image holds. *)
Lemma img_mrd_bytes_at : forall m B L A bs,
  (forall i, 0 <= i < L -> mrd segs m (wa (B + i)) = seg_rom segs (wa (B + i))) ->
  B <= A -> A + Z.of_nat (length bs) <= B + L -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  img_bytes_b A bs = true -> bytes_at segs m A bs.
Proof.
  intros m B L A bs HM H1 H2 HA HL HB. split; [exact HA|]. split; [exact HL|].
  intros i Hi. replace (A + Z.of_nat i) with (B + (A - B + Z.of_nat i)) by lia.
  rewrite HM by lia. replace (B + (A - B + Z.of_nat i)) with (A + Z.of_nat i) by lia.
  apply img_bytes_b_nth; assumption.
Qed.

Lemma img_ro_bytes_at : forall m A bs, mem_inv segs m -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  ro_bytes_b segs A bs = true -> bytes_at segs m A bs.
Proof. intros m A bs HI HA HL HB. apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact HB. Qed.

Lemma bytes_at_cells : forall m A cs, cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> ro_cells segs m A cs.
Proof. intros m A cs W H. split; assumption. Qed.

Lemma bytes_at_read0 : forall m A bs n, length bs = n -> bytes_at segs m A bs -> ov_read_bytes segs m (wa A) n = Some bs.
Proof.
  intros m A bs n Hn H. subst n. pose proof (bytes_at_ov_read segs m A bs 0 (length bs) H ltac:(lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r, skipn_O, firstn_all in E. exact E.
Qed.

End Kit.

Lemma no_nul : forall s : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) s = true -> ~ In (Z_to_bv 8 0) s.
Proof.
  intros s H Hin. rewrite forallb_forall in H. specialize (H _ Hin).
  assert (E : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity. rewrite E in H. cbv in H. discriminate H.
Qed.

Lemma bytes_ne : forall xs ys : list byte, map bv_unsigned xs <> map bv_unsigned ys -> xs <> ys.
Proof. intros xs ys H E. apply H. rewrite E. reflexivity. Qed.

Lemma sx32_small : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  destruct (Z.leb_spec0 0 v) as [Hp|Hn].
  - rewrite Z.mod_small by (change (bv_modulus 64) with (2^64); lia). apply bv_swrap_small.
    change (bv_half_modulus 32) with (2^31). lia.
  - change (bv_modulus 64) with (2^64).
    replace (v mod 2^64) with (v + 2^64) by (rewrite <- (Z.mod_add v 1) by lia; rewrite Z.mod_small by lia; lia).
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
    replace (v + 2^64 + 2^31) with (v + 2^31 + 2^32 * 2^32) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

(** * Read-only data (.rodata) *)

(** ** The jump tables of LLVMFuzzerTestOneInput

    Each entry is the 32-bit offset of its target from the table base; the code adds the base to the
    sign-extended entry and jumps there. [codec_Tk] lists the targets (the case pcs of the listing); [codec_Tk_cells]
    are the entries as the image holds them; [codec_Tk_pcs] checks that each entry decodes to its pc, and
    [codec_Tk_image] that the image holds the entries. T1 is the reader switch (kinds 0..13; kind 14 is the
    default), T2 the switch of run() (kinds 0..10), T3 the switch of owe() (kinds 0..10; SYSEX is the default). *)

Definition CODEC_T1 : Z := 0x10444.
Definition codec_T1 : list Z := [0x13448; 0x13714; 0x137b4; 0x13588; 0x138f4; 0x139fc; 0x13854;
  0x13448; 0x13ac8; 0x13674; 0x13a9c; 0x134e8; 0x13628; 0x13994].
Definition codec_T1_cells : list cell := [C4 (Z_to_bv 64 0x3004); C4 (Z_to_bv 64 0x32d0); C4 (Z_to_bv 64 0x3370); C4 (Z_to_bv 64 0x3144);
  C4 (Z_to_bv 64 0x34b0); C4 (Z_to_bv 64 0x35b8); C4 (Z_to_bv 64 0x3410); C4 (Z_to_bv 64 0x3004);
  C4 (Z_to_bv 64 0x3684); C4 (Z_to_bv 64 0x3230); C4 (Z_to_bv 64 0x3658); C4 (Z_to_bv 64 0x30a4);
  C4 (Z_to_bv 64 0x31e4); C4 (Z_to_bv 64 0x3550)].

Lemma codec_T1_pcs : map (fun c => match c with C4 v => CODEC_T1 + bv_unsigned v | _ => 0 end) codec_T1_cells = codec_T1.
Proof. vm_compute. reflexivity. Qed.

(** The 14 entries of T1 at 0x10444. *)
Lemma codec_T1_image : ro_bytes_b rsegs CODEC_T1 (cells_bytes codec_T1_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_T1_at : forall m, mem_inv rsegs m -> ro_cells rsegs m CODEC_T1 codec_T1_cells.
Proof.
  intros m HI. apply bytes_at_cells; [cbn; repeat split|].
  apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  exact codec_T1_image.
Qed.

Lemma codec_T1_read : forall m k, mem_inv rsegs m -> 0 <= k < 14 ->
  ov_read_bytes rsegs m (wa (CODEC_T1 + 4 * k)) 4 =
    Some (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T1 0 - CODEC_T1))).
Proof.
  intros m k HI Hk. apply bytes_at_read0; [apply length_le4|].
  apply img_ro_bytes_at; [exact HI | unfold CODEC_T1; lia | rewrite length_le4; unfold CODEC_T1; lia |].
  refine (zall_range (fun k => ro_bytes_b rsegs (CODEC_T1 + 4 * k)
            (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T1 0 - CODEC_T1)))) 0 14 _ k Hk).
  vm_compute. reflexivity.
Qed.

(** The entry is a positive offset below 2^31 (so sign extension keeps it) and its target is 4-aligned. *)
Lemma codec_T1_entry : forall k, 0 <= k < 14 ->
  0 < nth (Z.to_nat k) codec_T1 0 - CODEC_T1 < 2^31 /\ nth (Z.to_nat k) codec_T1 0 mod 4 = 0.
Proof.
  intros k Hk.
  pose proof (zall_range (fun k => (0 <? nth (Z.to_nat k) codec_T1 0 - CODEC_T1)
            && (nth (Z.to_nat k) codec_T1 0 - CODEC_T1 <? 2^31) && (nth (Z.to_nat k) codec_T1 0 mod 4 =? 0))
            0 14 ltac:(vm_compute; reflexivity) k Hk) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma codec_T1_sx : forall k, 0 <= k < 14 ->
  sx32 (Z_to_bv 64 (nth (Z.to_nat k) codec_T1 0 - CODEC_T1)) = Z_to_bv 64 (nth (Z.to_nat k) codec_T1 0 - CODEC_T1).
Proof. intros k Hk. apply sx32_small. pose proof (codec_T1_entry k Hk). lia. Qed.

Definition CODEC_T2 : Z := 0x1047c.
Definition codec_T2 : list Z := [0x143b4; 0x14454; 0x1440c; 0x14424; 0x143fc; 0x1446c; 0x14484;
  0x1443c; 0x144a0; 0x143cc; 0x143e4].
Definition codec_T2_cells : list cell := [C4 (Z_to_bv 64 0x3f38); C4 (Z_to_bv 64 0x3fd8); C4 (Z_to_bv 64 0x3f90); C4 (Z_to_bv 64 0x3fa8);
  C4 (Z_to_bv 64 0x3f80); C4 (Z_to_bv 64 0x3ff0); C4 (Z_to_bv 64 0x4008); C4 (Z_to_bv 64 0x3fc0);
  C4 (Z_to_bv 64 0x4024); C4 (Z_to_bv 64 0x3f50); C4 (Z_to_bv 64 0x3f68)].

Lemma codec_T2_pcs : map (fun c => match c with C4 v => CODEC_T2 + bv_unsigned v | _ => 0 end) codec_T2_cells = codec_T2.
Proof. vm_compute. reflexivity. Qed.

(** The 11 entries of T2 at 0x1047c. *)
Lemma codec_T2_image : ro_bytes_b rsegs CODEC_T2 (cells_bytes codec_T2_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_T2_at : forall m, mem_inv rsegs m -> ro_cells rsegs m CODEC_T2 codec_T2_cells.
Proof.
  intros m HI. apply bytes_at_cells; [cbn; repeat split|].
  apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  exact codec_T2_image.
Qed.

Lemma codec_T2_read : forall m k, mem_inv rsegs m -> 0 <= k < 11 ->
  ov_read_bytes rsegs m (wa (CODEC_T2 + 4 * k)) 4 =
    Some (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T2 0 - CODEC_T2))).
Proof.
  intros m k HI Hk. apply bytes_at_read0; [apply length_le4|].
  apply img_ro_bytes_at; [exact HI | unfold CODEC_T2; lia | rewrite length_le4; unfold CODEC_T2; lia |].
  refine (zall_range (fun k => ro_bytes_b rsegs (CODEC_T2 + 4 * k)
            (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T2 0 - CODEC_T2)))) 0 11 _ k Hk).
  vm_compute. reflexivity.
Qed.

(** The entry is a positive offset below 2^31 (so sign extension keeps it) and its target is 4-aligned. *)
Lemma codec_T2_entry : forall k, 0 <= k < 11 ->
  0 < nth (Z.to_nat k) codec_T2 0 - CODEC_T2 < 2^31 /\ nth (Z.to_nat k) codec_T2 0 mod 4 = 0.
Proof.
  intros k Hk.
  pose proof (zall_range (fun k => (0 <? nth (Z.to_nat k) codec_T2 0 - CODEC_T2)
            && (nth (Z.to_nat k) codec_T2 0 - CODEC_T2 <? 2^31) && (nth (Z.to_nat k) codec_T2 0 mod 4 =? 0))
            0 11 ltac:(vm_compute; reflexivity) k Hk) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma codec_T2_sx : forall k, 0 <= k < 11 ->
  sx32 (Z_to_bv 64 (nth (Z.to_nat k) codec_T2 0 - CODEC_T2)) = Z_to_bv 64 (nth (Z.to_nat k) codec_T2 0 - CODEC_T2).
Proof. intros k Hk. apply sx32_small. pose proof (codec_T2_entry k Hk). lia. Qed.

Definition CODEC_T3 : Z := 0x104a8.
Definition codec_T3 : list Z := [0x14528; 0x14738; 0x14688; 0x146d0; 0x145b4; 0x14790; 0x14890;
  0x14718; 0x14a0c; 0x145d0; 0x14928].
Definition codec_T3_cells : list cell := [C4 (Z_to_bv 64 0x4080); C4 (Z_to_bv 64 0x4290); C4 (Z_to_bv 64 0x41e0); C4 (Z_to_bv 64 0x4228);
  C4 (Z_to_bv 64 0x410c); C4 (Z_to_bv 64 0x42e8); C4 (Z_to_bv 64 0x43e8); C4 (Z_to_bv 64 0x4270);
  C4 (Z_to_bv 64 0x4564); C4 (Z_to_bv 64 0x4128); C4 (Z_to_bv 64 0x4480)].

Lemma codec_T3_pcs : map (fun c => match c with C4 v => CODEC_T3 + bv_unsigned v | _ => 0 end) codec_T3_cells = codec_T3.
Proof. vm_compute. reflexivity. Qed.

(** The 11 entries of T3 at 0x104a8. *)
Lemma codec_T3_image : ro_bytes_b rsegs CODEC_T3 (cells_bytes codec_T3_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_T3_at : forall m, mem_inv rsegs m -> ro_cells rsegs m CODEC_T3 codec_T3_cells.
Proof.
  intros m HI. apply bytes_at_cells; [cbn; repeat split|].
  apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  exact codec_T3_image.
Qed.

Lemma codec_T3_read : forall m k, mem_inv rsegs m -> 0 <= k < 11 ->
  ov_read_bytes rsegs m (wa (CODEC_T3 + 4 * k)) 4 =
    Some (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T3 0 - CODEC_T3))).
Proof.
  intros m k HI Hk. apply bytes_at_read0; [apply length_le4|].
  apply img_ro_bytes_at; [exact HI | unfold CODEC_T3; lia | rewrite length_le4; unfold CODEC_T3; lia |].
  refine (zall_range (fun k => ro_bytes_b rsegs (CODEC_T3 + 4 * k)
            (le4 (Z_to_bv 64 (nth (Z.to_nat k) codec_T3 0 - CODEC_T3)))) 0 11 _ k Hk).
  vm_compute. reflexivity.
Qed.

(** The entry is a positive offset below 2^31 (so sign extension keeps it) and its target is 4-aligned. *)
Lemma codec_T3_entry : forall k, 0 <= k < 11 ->
  0 < nth (Z.to_nat k) codec_T3 0 - CODEC_T3 < 2^31 /\ nth (Z.to_nat k) codec_T3 0 mod 4 = 0.
Proof.
  intros k Hk.
  pose proof (zall_range (fun k => (0 <? nth (Z.to_nat k) codec_T3 0 - CODEC_T3)
            && (nth (Z.to_nat k) codec_T3 0 - CODEC_T3 <? 2^31) && (nth (Z.to_nat k) codec_T3 0 mod 4 =? 0))
            0 11 ltac:(vm_compute; reflexivity) k Hk) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

Lemma codec_T3_sx : forall k, 0 <= k < 11 ->
  sx32 (Z_to_bv 64 (nth (Z.to_nat k) codec_T3 0 - CODEC_T3)) = Z_to_bv 64 (nth (Z.to_nat k) codec_T3 0 - CODEC_T3).
Proof. intros k Hk. apply sx32_small. pose proof (codec_T3_entry k Hk). lia. Qed.

(** ** DESK = {0, 1, 2} (u32 enum values, indexed by op / 15 % 3) *)
Definition CODEC_DESK : Z := 0x104d4.
Definition codec_DESK_cells : list cell := [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 2)].

(** DESK at 0x104d4. *)
Lemma codec_DESK_image : ro_bytes_b rsegs CODEC_DESK (cells_bytes codec_DESK_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_DESK_at : forall m, mem_inv rsegs m -> ro_cells rsegs m CODEC_DESK codec_DESK_cells.
Proof.
  intros m HI. apply bytes_at_cells; [cbn; repeat split|].
  apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  exact codec_DESK_image.
Qed.

Lemma codec_DESK_read : forall m i, mem_inv rsegs m -> 0 <= i < 3 ->
  ov_read_bytes rsegs m (wa (CODEC_DESK + 4 * i)) 4 = Some (le4 (Z_to_bv 64 i)).
Proof.
  intros m i HI Hi. apply bytes_at_read0; [apply length_le4|].
  apply img_ro_bytes_at; [exact HI | unfold CODEC_DESK; lia | rewrite length_le4; unfold CODEC_DESK; lia |].
  refine (zall_range (fun i => ro_bytes_b rsegs (CODEC_DESK + 4 * i) (le4 (Z_to_bv 64 i))) 0 3 _ i Hi).
  vm_compute. reflexivity.
Qed.

(** ** The table of diginet_seg7: 91 words at 0x104e0, indexed by c - 0x20 for c in [0x20, 0x7a]; -1 marks a
    character with no glyph. *)
Definition CODEC_SEG7 : Z := 0x104e0.
Definition codec_seg7_tab : list Z := [0; (-1); (-1); (-1); (-1); (-1); (-1); (-1); (-1); (-1); (-1); (-1); (-1); 1; (-1); (-1);
  126; 48; 109; 121; 51; 91; 95; 112; 127; 123; (-1); (-1); (-1); (-1); (-1); (-1);
  (-1); 119; 31; 78; 61; 79; 71; (-1); 55; (-1); 60; (-1); 14; (-1); (-1); 29;
  103; (-1); 5; 91; (-1); 62; (-1); (-1); (-1); 59; 109; (-1); (-1); (-1); (-1); (-1);
  (-1); 119; 31; 78; 61; 79; 71; (-1); 23; (-1); 60; (-1); 14; (-1); (-1); 29;
  103; (-1); 5; 91; (-1); 62; (-1); (-1); (-1); 59; 109].
Definition codec_seg7_cells : list cell := [C4 (Z_to_bv 64 0x0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x1); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 0x7e); C4 (Z_to_bv 64 0x30); C4 (Z_to_bv 64 0x6d); C4 (Z_to_bv 64 0x79);
  C4 (Z_to_bv 64 0x33); C4 (Z_to_bv 64 0x5b); C4 (Z_to_bv 64 0x5f); C4 (Z_to_bv 64 0x70);
  C4 (Z_to_bv 64 0x7f); C4 (Z_to_bv 64 0x7b); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x77); C4 (Z_to_bv 64 0x1f); C4 (Z_to_bv 64 0x4e);
  C4 (Z_to_bv 64 0x3d); C4 (Z_to_bv 64 0x4f); C4 (Z_to_bv 64 0x47); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 0x37); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3c); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 0xe); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x1d);
  C4 (Z_to_bv 64 0x67); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x5); C4 (Z_to_bv 64 0x5b);
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3e); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3b); C4 (Z_to_bv 64 0x6d); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x77); C4 (Z_to_bv 64 0x1f); C4 (Z_to_bv 64 0x4e);
  C4 (Z_to_bv 64 0x3d); C4 (Z_to_bv 64 0x4f); C4 (Z_to_bv 64 0x47); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 0x17); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3c); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 0xe); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x1d);
  C4 (Z_to_bv 64 0x67); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x5); C4 (Z_to_bv 64 0x5b);
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3e); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1));
  C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0x3b); C4 (Z_to_bv 64 0x6d)].

(** The seg7 table. *)
Lemma codec_seg7_image : ro_bytes_b rsegs CODEC_SEG7 (cells_bytes codec_seg7_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_seg7_at : forall m, mem_inv rsegs m -> ro_cells rsegs m CODEC_SEG7 codec_seg7_cells.
Proof.
  intros m HI. apply bytes_at_cells; [cbn; repeat split|].
  apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity |].
  exact codec_seg7_image.
Qed.

Lemma codec_seg7_cells_tab : map (fun c => match c with C4 v => bv_unsigned v | _ => 0 end) codec_seg7_cells =
  map (fun x => x mod 2^64) codec_seg7_tab.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_seg7_read : forall m i, mem_inv rsegs m -> 0 <= i < 91 ->
  ov_read_bytes rsegs m (wa (CODEC_SEG7 + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat i) codec_seg7_tab 0))).
Proof.
  intros m i HI Hi. apply bytes_at_read0; [apply length_le4|].
  apply img_ro_bytes_at; [exact HI | unfold CODEC_SEG7; lia | rewrite length_le4; unfold CODEC_SEG7; lia |].
  refine (zall_range (fun i => ro_bytes_b rsegs (CODEC_SEG7 + 4 * i)
            (le4 (Z_to_bv 64 (nth (Z.to_nat i) codec_seg7_tab 0)))) 0 91 _ i Hi).
  vm_compute. reflexivity.
Qed.

Lemma codec_seg7_range : forall i, 0 <= i < 91 -> -1 <= nth (Z.to_nat i) codec_seg7_tab 0 <= 127.
Proof.
  intros i Hi.
  pose proof (zall_range (fun i => (-1 <=? nth (Z.to_nat i) codec_seg7_tab 0) && (nth (Z.to_nat i) codec_seg7_tab 0 <=? 127))
            0 91 ltac:(vm_compute; reflexivity) i Hi) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma codec_seg7_sx : forall i, 0 <= i < 91 ->
  sx32 (Z_to_bv 64 (nth (Z.to_nat i) codec_seg7_tab 0)) = Z_to_bv 64 (nth (Z.to_nat i) codec_seg7_tab 0).
Proof. intros i Hi. apply sx32_small. pose proof (codec_seg7_range i Hi). lia. Qed.

(** ** The strings check_personality passes to strcmp and diginet_personality_from_name

    In the form strcmp's contract takes them: the characters, then a NUL, none of the characters NUL.
    "CNTRL|24" and "MAINUNIT" are also the names SPEC_C24 / personalities[0] and SPEC_PC / personalities[1]
    point to. *)
Definition CODEC_STR_C24 : Z := 0x103a1.
Definition codec_str_c24 : list byte := [Z_to_bv 8 0x43; Z_to_bv 8 0x4e; Z_to_bv 8 0x54; Z_to_bv 8 0x52; Z_to_bv 8 0x4c; Z_to_bv 8 0x7c; Z_to_bv 8 0x32; Z_to_bv 8 0x34].  (* "CNTRL|24" *)
Definition CODEC_STR_PC : Z := 0x10381.
Definition codec_str_pc : list byte := [Z_to_bv 8 0x4d; Z_to_bv 8 0x41; Z_to_bv 8 0x49; Z_to_bv 8 0x4e; Z_to_bv 8 0x55; Z_to_bv 8 0x4e; Z_to_bv 8 0x49; Z_to_bv 8 0x54].  (* "MAINUNIT" *)
Definition CODEC_STR_C2 : Z := 0x1031d.
Definition codec_str_c2 : list byte := [Z_to_bv 8 0x43; Z_to_bv 8 0x4e; Z_to_bv 8 0x54; Z_to_bv 8 0x52; Z_to_bv 8 0x4c; Z_to_bv 8 0x7c; Z_to_bv 8 0x32].  (* "CNTRL|2" *)
Definition CODEC_STR_PCS : Z := 0x10333.
Definition codec_str_pcs : list byte := [Z_to_bv 8 0x4d; Z_to_bv 8 0x41; Z_to_bv 8 0x49; Z_to_bv 8 0x4e; Z_to_bv 8 0x55; Z_to_bv 8 0x4e; Z_to_bv 8 0x49; Z_to_bv 8 0x54; Z_to_bv 8 0x53].  (* "MAINUNITS" *)
Definition CODEC_STR_NIL : Z := 0x102de.
Definition codec_str_nil : list byte := [].  (* "" *)

Lemma codec_str_c24_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CODEC_STR_C24 (codec_str_c24 ++ [Z_to_bv 8 0]).
Proof.
  intros m HI. apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity ..
    | vm_compute; reflexivity].
Qed.

Lemma codec_str_c24_nz : ~ In (Z_to_bv 8 0) codec_str_c24.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma codec_str_pc_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CODEC_STR_PC (codec_str_pc ++ [Z_to_bv 8 0]).
Proof.
  intros m HI. apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity ..
    | vm_compute; reflexivity].
Qed.

Lemma codec_str_pc_nz : ~ In (Z_to_bv 8 0) codec_str_pc.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma codec_str_c2_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CODEC_STR_C2 (codec_str_c2 ++ [Z_to_bv 8 0]).
Proof.
  intros m HI. apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity ..
    | vm_compute; reflexivity].
Qed.

Lemma codec_str_c2_nz : ~ In (Z_to_bv 8 0) codec_str_c2.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma codec_str_pcs_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CODEC_STR_PCS (codec_str_pcs ++ [Z_to_bv 8 0]).
Proof.
  intros m HI. apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity ..
    | vm_compute; reflexivity].
Qed.

Lemma codec_str_pcs_nz : ~ In (Z_to_bv 8 0) codec_str_pcs.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma codec_str_nil_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CODEC_STR_NIL (codec_str_nil ++ [Z_to_bv 8 0]).
Proof.
  intros m HI. apply img_ro_bytes_at; [exact HI | apply Z.leb_le; vm_compute; reflexivity ..
    | vm_compute; reflexivity].
Qed.

Lemma codec_str_nil_nz : ~ In (Z_to_bv 8 0) codec_str_nil.
Proof. apply no_nul. vm_compute. reflexivity. Qed.

Lemma codec_str_pc_ne_c24 : codec_str_pc <> codec_str_c24.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_c2_ne_c24 : codec_str_c2 <> codec_str_c24.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_c2_ne_pc : codec_str_c2 <> codec_str_pc.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_pcs_ne_c24 : codec_str_pcs <> codec_str_c24.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_pcs_ne_pc : codec_str_pcs <> codec_str_pc.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_nil_ne_c24 : codec_str_nil <> codec_str_c24.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

Lemma codec_str_nil_ne_pc : codec_str_nil <> codec_str_pc.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

(** ** The segment strings of GLYPH (owed_seg7): entry i has character [codec_glyph_chr], points to
    [codec_glyph_ptr] (in .rodata) and that string lists the lit segments [codec_glyph_str] ('a'..'g'). *)
Definition codec_glyph_chr : list Z := [0x30; 0x31; 0x32; 0x33; 0x34; 0x35; 0x36; 0x37; 0x38; 0x39;
  0x41; 0x62; 0x43; 0x64; 0x45; 0x46; 0x48; 0x68; 0x4a; 0x4c;
  0x6f; 0x50; 0x72; 0x53; 0x55; 0x59; 0x5a; 0x2d; 0x20].
Definition codec_glyph_ptr : list Z := [0x103dc; 0x103fb; 0x10325; 0x10428; 0x1038f; 0x103fe; 0x102a7; 0x1036b;
  0x103e3; 0x1036f; 0x10394; 0x10340; 0x10376; 0x103eb; 0x1037b; 0x102a2;
  0x103f1; 0x102e7; 0x1038a; 0x1032f; 0x102ae; 0x103d6; 0x1033d; 0x103fe;
  0x102df; 0x1039b; 0x10325; 0x1042e; 0x102de].
Definition codec_glyph_str : list (list Z) := [[0x61; 0x62; 0x63; 0x64; 0x65; 0x66]; [0x62; 0x63]; [0x61; 0x62; 0x64; 0x65; 0x67]; [0x61; 0x62; 0x63; 0x64; 0x67];
  [0x62; 0x63; 0x66; 0x67]; [0x61; 0x63; 0x64; 0x66; 0x67]; [0x61; 0x63; 0x64; 0x65; 0x66; 0x67]; [0x61; 0x62; 0x63];
  [0x61; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67]; [0x61; 0x62; 0x63; 0x64; 0x66; 0x67]; [0x61; 0x62; 0x63; 0x65; 0x66; 0x67]; [0x63; 0x64; 0x65; 0x66; 0x67];
  [0x61; 0x64; 0x65; 0x66]; [0x62; 0x63; 0x64; 0x65; 0x67]; [0x61; 0x64; 0x65; 0x66; 0x67]; [0x61; 0x65; 0x66; 0x67];
  [0x62; 0x63; 0x65; 0x66; 0x67]; [0x63; 0x65; 0x66; 0x67]; [0x62; 0x63; 0x64; 0x65]; [0x64; 0x65; 0x66];
  [0x63; 0x64; 0x65; 0x67]; [0x61; 0x62; 0x65; 0x66; 0x67]; [0x65; 0x67]; [0x61; 0x63; 0x64; 0x66; 0x67];
  [0x62; 0x63; 0x64; 0x65; 0x66]; [0x62; 0x63; 0x64; 0x66; 0x67]; [0x61; 0x62; 0x64; 0x65; 0x67]; [0x67];
  []].

Lemma codec_glyph_str_at : forall m i, mem_inv rsegs m -> 0 <= i < 29 ->
  bytes_at rsegs m (nth (Z.to_nat i) codec_glyph_ptr 0) (map (Z_to_bv 8) (nth (Z.to_nat i) codec_glyph_str [] ++ [0])).
Proof.
  intros m i HI Hi.
  pose proof (zall_range (fun i => (0 <=? nth (Z.to_nat i) codec_glyph_ptr 0)
      && (nth (Z.to_nat i) codec_glyph_ptr 0 + Z.of_nat (length (map (Z_to_bv 8) (nth (Z.to_nat i) codec_glyph_str [] ++ [0]))) <=? 2^64)
      && ro_bytes_b rsegs (nth (Z.to_nat i) codec_glyph_ptr 0) (map (Z_to_bv 8) (nth (Z.to_nat i) codec_glyph_str [] ++ [0])))
      0 29 ltac:(vm_compute; reflexivity) i Hi) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply img_ro_bytes_at; assumption.
Qed.

(** * The tables in .data.rel.ro

    [0x1f678, 0x1f8b0) holds, in this order, LLVMFuzzerTestOneInput's SPEC_DESK (0x1f678, 24 bytes),
    SPEC_C24 (0x1f690, 16), SPEC_PC (0x1f6a0, 16), owed_seg7's GLYPH (0x1f6b0, 29 x 16)
    and the library's personalities[] (0x1f880, 2 x 24). The segment is writable, so each lemma below
    takes the premise that memory there still reads as the image. *)
Definition codec_relro_base : Z := 0x1f678.
Definition codec_relro_bytes : list byte := [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x90; Z_to_bv 8 0xf6; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xa0; Z_to_bv 8 0xf6; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xa1; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x01; Z_to_bv 8 0x18; Z_to_bv 8 0x04; Z_to_bv 8 0x19; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x81; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x00; Z_to_bv 8 0x08; Z_to_bv 8 0x08; Z_to_bv 8 0x09; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x30; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xdc; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x31; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xfb; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x32; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x25; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x33; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x28; Z_to_bv 8 0x04; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x34; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x8f; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x35; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xfe; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x36; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xa7; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x37; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x6b; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x38; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xe3; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x39; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x6f; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x41; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x94; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x62; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x40; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x43; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x76; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x64; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xeb; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x45; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x7b; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x46; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xa2; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x48; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xf1; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x68; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xe7; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x4a; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x8a; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x4c; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x2f; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x6f; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xae; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x50; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xd6; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x72; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x3d; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x53; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xfe; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x55; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xdf; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x59; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x9b; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x5a; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x25; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x2d; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x2e; Z_to_bv 8 0x04; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x20; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xde; Z_to_bv 8 0x02; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0xa1; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x01; Z_to_bv 8 0x18; Z_to_bv 8 0x04; Z_to_bv 8 0x19; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x02; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x81; Z_to_bv 8 0x03; Z_to_bv 8 0x01; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00;
  Z_to_bv 8 0x00; Z_to_bv 8 0x08; Z_to_bv 8 0x08; Z_to_bv 8 0x09; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00].

Lemma codec_relro_image_b : img_bytes_b rsegs codec_relro_base codec_relro_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_relro_image : image_bytes rsegs codec_relro_base 568 = Some codec_relro_bytes.
Proof. exact (img_bytes_b_image rsegs codec_relro_bytes codec_relro_base codec_relro_image_b). Qed.

Lemma codec_relro_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  bytes_at rsegs m codec_relro_base codec_relro_bytes.
Proof.
  intros m HM. apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_relro_image_b].
Qed.

(** SPEC_DESK = {NULL, &SPEC_C24, &SPEC_PC}. *)
Definition CODEC_SPEC_DESK : Z := 0x1f678.
Definition codec_SPEC_DESK : list Z := [0; 0x1f690; 0x1f6a0].
Definition codec_SPEC_DESK_cells : list cell := [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1f690); C8 (Z_to_bv 64 0x1f6a0)].

(** SPEC_DESK. *)
Lemma codec_SPEC_DESK_image : img_bytes_b rsegs 0x1f678 (cells_bytes codec_SPEC_DESK_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_SPEC_DESK_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x1f678 codec_SPEC_DESK_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_SPEC_DESK_image].
Qed.

Lemma codec_SPEC_DESK_read : forall m i, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) -> 0 <= i < 3 ->
  ov_read_bytes rsegs m (wa (CODEC_SPEC_DESK + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) codec_SPEC_DESK 0))).
Proof.
  intros m i HM Hi. apply bytes_at_read0; [apply length_le8|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | rewrite ?length_le8; cbv [CODEC_SPEC_DESK codec_relro_base]; lia .. |].
  refine (zall_range (fun i => img_bytes_b rsegs (CODEC_SPEC_DESK + 8 * i)
            (le8 (Z_to_bv 64 (nth (Z.to_nat i) codec_SPEC_DESK 0)))) 0 3 _ i Hi).
  vm_compute. reflexivity.
Qed.

(** SPEC_C24 = {"CNTRL|24", device 1, strips 24, chars 4, counter 0x19} and SPEC_PC = {"MAINUNIT", device 0,
    strips 8, chars 8, counter 9}: the name pointer, the four u8 fields, 4 bytes of padding. *)
Definition codec_SPEC_C24_cells : list cell := [C8 (Z_to_bv 64 0x103a1); C1 (Z_to_bv 8 0x01); C1 (Z_to_bv 8 0x18); C1 (Z_to_bv 8 0x04);
  C1 (Z_to_bv 8 0x19); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]].
Definition codec_SPEC_PC_cells : list cell := [C8 (Z_to_bv 64 0x10381); C1 (Z_to_bv 8 0x00); C1 (Z_to_bv 8 0x08); C1 (Z_to_bv 8 0x08);
  C1 (Z_to_bv 8 0x09); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]].

(** SPEC_C24. *)
Lemma codec_SPEC_C24_image : img_bytes_b rsegs 0x1f690 (cells_bytes codec_SPEC_C24_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_SPEC_C24_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x1f690 codec_SPEC_C24_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_SPEC_C24_image].
Qed.

(** SPEC_PC. *)
Lemma codec_SPEC_PC_image : img_bytes_b rsegs 0x1f6a0 (cells_bytes codec_SPEC_PC_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_SPEC_PC_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x1f6a0 codec_SPEC_PC_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_SPEC_PC_image].
Qed.

(** personalities[] = {{desk 1, "CNTRL|24", 1, 24, 4, 0x19}, {desk 2, "MAINUNIT", 0, 8, 8, 9}}: per entry the u32 desk,
    4 bytes of padding, the name pointer, the four u8 fields, 4 bytes of padding. *)
Definition CODEC_PERS : Z := 0x1f880.
Definition codec_pers_cells : list cell := [C4 (Z_to_bv 64 0x1); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103a1); C1 (Z_to_bv 8 0x01);
  C1 (Z_to_bv 8 0x18); C1 (Z_to_bv 8 0x04); C1 (Z_to_bv 8 0x19); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00];
  C4 (Z_to_bv 64 0x2); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10381); C1 (Z_to_bv 8 0x00);
  C1 (Z_to_bv 8 0x08); C1 (Z_to_bv 8 0x08); C1 (Z_to_bv 8 0x09); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]].

(** personalities[]. *)
Lemma codec_pers_image : img_bytes_b rsegs 0x1f880 (cells_bytes codec_pers_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_pers_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x1f880 codec_pers_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_pers_image].
Qed.

(** GLYPH: 29 entries {u8 c; 7 bytes of padding; const char *segs}. *)
Definition CODEC_GLYPH : Z := 0x1f6b0.
Definition codec_GLYPH_cells : list cell := [C1 (Z_to_bv 8 0x30); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103dc);
  C1 (Z_to_bv 8 0x31); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103fb);
  C1 (Z_to_bv 8 0x32); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10325);
  C1 (Z_to_bv 8 0x33); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10428);
  C1 (Z_to_bv 8 0x34); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1038f);
  C1 (Z_to_bv 8 0x35); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103fe);
  C1 (Z_to_bv 8 0x36); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102a7);
  C1 (Z_to_bv 8 0x37); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1036b);
  C1 (Z_to_bv 8 0x38); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103e3);
  C1 (Z_to_bv 8 0x39); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1036f);
  C1 (Z_to_bv 8 0x41); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10394);
  C1 (Z_to_bv 8 0x62); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10340);
  C1 (Z_to_bv 8 0x43); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10376);
  C1 (Z_to_bv 8 0x64); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103eb);
  C1 (Z_to_bv 8 0x45); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1037b);
  C1 (Z_to_bv 8 0x46); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102a2);
  C1 (Z_to_bv 8 0x48); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103f1);
  C1 (Z_to_bv 8 0x68); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102e7);
  C1 (Z_to_bv 8 0x4a); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1038a);
  C1 (Z_to_bv 8 0x4c); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1032f);
  C1 (Z_to_bv 8 0x6f); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102ae);
  C1 (Z_to_bv 8 0x50); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103d6);
  C1 (Z_to_bv 8 0x72); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1033d);
  C1 (Z_to_bv 8 0x53); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x103fe);
  C1 (Z_to_bv 8 0x55); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102df);
  C1 (Z_to_bv 8 0x59); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1039b);
  C1 (Z_to_bv 8 0x5a); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10325);
  C1 (Z_to_bv 8 0x2d); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x1042e);
  C1 (Z_to_bv 8 0x20); CB 7 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x102de)].

(** GLYPH. *)
Lemma codec_GLYPH_image : img_bytes_b rsegs 0x1f6b0 (cells_bytes codec_GLYPH_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_GLYPH_at : forall m, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x1f6b0 codec_GLYPH_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_GLYPH_image].
Qed.

Lemma codec_GLYPH_tab : map (fun c => match c with C1 b => bv_unsigned b | C8 v => bv_unsigned v | _ => -1 end)
    codec_GLYPH_cells = concat (map (fun ij => [fst ij; -1; snd ij]) (combine codec_glyph_chr codec_glyph_ptr)).
Proof. vm_compute. reflexivity. Qed.

Lemma codec_GLYPH_chr_read : forall m i, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) -> 0 <= i < 29 ->
  ov_read_bytes rsegs m (wa (CODEC_GLYPH + 16 * i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) codec_glyph_chr 0)].
Proof.
  intros m i HM Hi. apply bytes_at_read0; [reflexivity|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | cbn [length]; cbv [CODEC_GLYPH codec_relro_base]; lia .. |].
  refine (zall_range (fun i => img_bytes_b rsegs (CODEC_GLYPH + 16 * i)
            [Z_to_bv 8 (nth (Z.to_nat i) codec_glyph_chr 0)]) 0 29 _ i Hi).
  vm_compute. reflexivity.
Qed.

Lemma codec_GLYPH_ptr_read : forall m i, (forall i, 0 <= i < 568 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) -> 0 <= i < 29 ->
  ov_read_bytes rsegs m (wa (CODEC_GLYPH + 16 * i + 8)) 8 = Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) codec_glyph_ptr 0))).
Proof.
  intros m i HM Hi. apply bytes_at_read0; [apply length_le8|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 568); [exact HM | rewrite ?length_le8; cbv [CODEC_GLYPH codec_relro_base]; lia .. |].
  refine (zall_range (fun i => img_bytes_b rsegs (CODEC_GLYPH + 16 * i + 8)
            (le8 (Z_to_bv 64 (nth (Z.to_nat i) codec_glyph_ptr 0)))) 0 29 _ i Hi).
  vm_compute. reflexivity.
Qed.

(** * The multiply-shift divisions

    [mul] then [srli]: the product never reaches 2^64 on these domains, so the wrapped form equals the plain one.
    op / 15 = (op * 0x89) >> 11 and kind = op + q - (q << 4) for a byte op (LLVMFuzzerTestOneInput, the head);
    q / 3 = (q * 0x56) >> 8 and q % 3 = q - t - (t << 1) for q = op / 15 <= 17 (the head);
    x % 25 = x - 25 * ((x * 0x29) >> 10) for a byte x (the SYSEX reader);
    v % 65 = v - t - (t << 6) with t = (v * 0xfc1) >> 18 for a u16 v (text_arg). *)

Lemma codec_div15 : forall op, 0 <= op < 256 -> Z.shiftr (op * 137) 11 = op / 15.
Proof.
  intros op H. apply Z.eqb_eq.
  refine (zall_range (fun x => Z.shiftr (x * 137) 11 =? x / 15) 0 256 _ op H). vm_compute. reflexivity.
Qed.

Lemma codec_div15_w : forall op, 0 <= op < 256 -> Z.shiftr ((op * 137) mod 18446744073709551616) 11 = op / 15.
Proof. intros op H. rewrite Z.mod_small by lia. apply codec_div15; exact H. Qed.

Lemma codec_div15_range : forall op, 0 <= op < 256 -> 0 <= op / 15 <= 17.
Proof. intros op H. split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r, Z.div_lt_upper_bound; lia. Qed.

Lemma codec_mod15 : forall op, 0 <= op < 256 ->
  op + Z.shiftr (op * 137) 11 - Z.shiftl (Z.shiftr (op * 137) 11) 4 = op mod 15.
Proof.
  intros op H. apply Z.eqb_eq.
  refine (zall_range (fun x => x + Z.shiftr (x * 137) 11 - Z.shiftl (Z.shiftr (x * 137) 11) 4 =? x mod 15) 0 256 _ op H).
  vm_compute. reflexivity.
Qed.

Lemma codec_div3 : forall q, 0 <= q < 18 -> Z.shiftr (q * 86) 8 = q / 3.
Proof.
  intros q H. apply Z.eqb_eq.
  refine (zall_range (fun x => Z.shiftr (x * 86) 8 =? x / 3) 0 18 _ q H). vm_compute. reflexivity.
Qed.

Lemma codec_div3_w : forall q, 0 <= q < 18 -> Z.shiftr ((q * 86) mod 18446744073709551616) 8 = q / 3.
Proof. intros q H. rewrite Z.mod_small by lia. apply codec_div3; exact H. Qed.

Lemma codec_mod3 : forall q, 0 <= q < 18 -> q - Z.shiftr (q * 86) 8 - Z.shiftl (Z.shiftr (q * 86) 8) 1 = q mod 3.
Proof.
  intros q H. apply Z.eqb_eq.
  refine (zall_range (fun x => x - Z.shiftr (x * 86) 8 - Z.shiftl (Z.shiftr (x * 86) 8) 1 =? x mod 3) 0 18 _ q H).
  vm_compute. reflexivity.
Qed.

Lemma codec_div25 : forall x, 0 <= x < 256 -> Z.shiftr (x * 41) 10 = x / 25.
Proof.
  intros x H. apply Z.eqb_eq.
  refine (zall_range (fun y => Z.shiftr (y * 41) 10 =? y / 25) 0 256 _ x H). vm_compute. reflexivity.
Qed.

Lemma codec_div25_w : forall x, 0 <= x < 256 -> Z.shiftr ((x * 41) mod 18446744073709551616) 10 = x / 25.
Proof. intros x H. rewrite Z.mod_small by lia. apply codec_div25; exact H. Qed.

Lemma codec_mod25 : forall x, 0 <= x < 256 -> x - Z.shiftr (x * 41) 10 * 25 = x mod 25.
Proof.
  intros x H. apply Z.eqb_eq.
  refine (zall_range (fun y => y - Z.shiftr (y * 41) 10 * 25 =? y mod 25) 0 256 _ x H). vm_compute. reflexivity.
Qed.

Lemma codec_div65 : forall v, 0 <= v < 65536 -> Z.shiftr (v * 4033) 18 = v / 65.
Proof.
  intros v H. apply Z.eqb_eq.
  refine (zall_range (fun y => Z.shiftr (y * 4033) 18 =? y / 65) 0 65536 _ v H). vm_compute. reflexivity.
Qed.

Lemma codec_div65_w : forall v, 0 <= v < 65536 -> Z.shiftr ((v * 4033) mod 18446744073709551616) 18 = v / 65.
Proof. intros v H. rewrite Z.mod_small by lia. apply codec_div65; exact H. Qed.

Lemma codec_mod65 : forall v, 0 <= v < 65536 ->
  v - Z.shiftr (v * 4033) 18 - Z.shiftl (Z.shiftr (v * 4033) 18) 6 = v mod 65.
Proof.
  intros v H. apply Z.eqb_eq.
  refine (zall_range (fun y => y - Z.shiftr (y * 4033) 18 - Z.shiftl (Z.shiftr (y * 4033) 18) 6 =? y mod 65) 0 65536 _ v H).
  vm_compute. reflexivity.
Qed.
