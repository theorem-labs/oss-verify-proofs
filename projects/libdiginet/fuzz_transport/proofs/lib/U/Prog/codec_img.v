(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_codec proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_img.v at d8e4e696562a3ec070d61f99e264ce9d80f5a5bd to fuzz_transport's images; only the facts of the announce names and personalities[] are kept; the RELRO block of codec_pers_at is fuzz_transport's whole .data.rel.ro *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** The facts of the UBSan image of fuzz_transport that the walk of diginet_personality_from_name reads, each
    proved by computation over the image (Img0): the announce names "CNTRL|24" and "MAINUNIT" in .rodata (so
    [mem_inv] makes every load read the image), and the library's personalities[] in .data.rel.ro (a writable
    segment, so a premise says that memory there still holds the image bytes). Kept from fuzz_codec's file of
    the same name, whose other facts are about fuzz_codec's own harness tables. *)

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

(** ** The announce names diginet_personality_from_name passes to strcmp

    In the form strcmp's contract takes them: the characters, then a NUL, none of the characters NUL.
    "CNTRL|24" and "MAINUNIT" are also the names SPEC_C24 / personalities[0] and SPEC_PC / personalities[1]
    point to. *)
Definition CODEC_STR_C24 : Z := 0x10339.
Definition codec_str_c24 : list byte := [Z_to_bv 8 0x43; Z_to_bv 8 0x4e; Z_to_bv 8 0x54; Z_to_bv 8 0x52; Z_to_bv 8 0x4c; Z_to_bv 8 0x7c; Z_to_bv 8 0x32; Z_to_bv 8 0x34].  (* "CNTRL|24" *)
Definition CODEC_STR_PC : Z := 0x10330.
Definition codec_str_pc : list byte := [Z_to_bv 8 0x4d; Z_to_bv 8 0x41; Z_to_bv 8 0x49; Z_to_bv 8 0x4e; Z_to_bv 8 0x55; Z_to_bv 8 0x4e; Z_to_bv 8 0x49; Z_to_bv 8 0x54].  (* "MAINUNIT" *)

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

Lemma codec_str_pc_ne_c24 : codec_str_pc <> codec_str_c24.
Proof. apply bytes_ne. vm_compute. intro E. discriminate E. Qed.

(** * personalities[] in .data.rel.ro

    fuzz_transport's .data.rel.ro starts at codec_relro_base; it holds, with other tables, the library's
    personalities[] (CODEC_PERS, 2 x 24). The segment is writable, so each lemma below takes the premise that
    memory there still reads as the image. *)
Definition codec_relro_base : Z := 0x21ef8.

(** personalities[] = {{desk 1, "CNTRL|24", 1, 24, 4, 0x19}, {desk 2, "MAINUNIT", 0, 8, 8, 9}}: per entry the u32 desk,
    4 bytes of padding, the name pointer, the four u8 fields, 4 bytes of padding. *)
Definition CODEC_PERS : Z := 0x21f90.
Definition codec_pers_cells : list cell := [C4 (Z_to_bv 64 0x1); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10339); C1 (Z_to_bv 8 0x01);
  C1 (Z_to_bv 8 0x18); C1 (Z_to_bv 8 0x04); C1 (Z_to_bv 8 0x19); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00];
  C4 (Z_to_bv 64 0x2); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10330); C1 (Z_to_bv 8 0x00);
  C1 (Z_to_bv 8 0x08); C1 (Z_to_bv 8 0x08); C1 (Z_to_bv 8 0x09); CB 4 [Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00; Z_to_bv 8 0x00]].

(** personalities[]. *)
Lemma codec_pers_image : img_bytes_b rsegs 0x21f90 (cells_bytes codec_pers_cells) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma codec_pers_at : forall m, (forall i, 0 <= i < 216 -> mrd rsegs m (wa (codec_relro_base + i)) = seg_rom rsegs (wa (codec_relro_base + i))) ->
  ro_cells rsegs m 0x21f90 codec_pers_cells.
Proof.
  intros m HM. apply bytes_at_cells; [cbn; repeat split|].
  apply (img_mrd_bytes_at rsegs m codec_relro_base 216); [exact HM | apply Z.leb_le; vm_compute; reflexivity ..
    | exact codec_pers_image].
Qed.
