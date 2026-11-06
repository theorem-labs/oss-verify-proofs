(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit.
Import ListNotations.
Open Scope Z_scope.

Definition fact_byte (f : mfact) (x : Z) : option byte :=
  match f with
  | MCell (ZLit a) w (ZLit v) => if is_cellw w && (a <=? x) && (x <? a + Z.of_nat w) then nth_error (cbytes (cellw w v)) (Z.to_nat (x - a)) else None
  | MZeroC (ZLit a) n => if (a <=? x) && (x <? a + n) then Some (Z_to_bv 8 0) else None
  | MZero (ZLit a) n => if (a <=? x) && (x <? a + n) then Some (Z_to_bv 8 0) else None
  | MImg lo hi => if (lo <=? x) && (x <? hi) then seg_rom asegs (wa x) else None
  | _ => None
  end.

Lemma fact_byte_sound : forall V (m : mem) f x b, mfact_ok asegs V m f -> fact_byte f x = Some b -> mrd asegs m (wa x) = Some b.
Proof.
  intros V m f x b OK E. destruct f as [e w v|e k|e w v|e k|e k c|lo hi|e k|e k|e k]; cbn [fact_byte] in E; try discriminate.
  -   destruct e as [a| | | | |]; try discriminate. destruct v as [v| | | | |]; try discriminate.
    destruct (is_cellw w && (a <=? x) && (x <? a + Z.of_nat w)) eqn:C; [|discriminate].
    apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    cbn [mfact_ok zv] in OK. destruct OK as [[WF (B0 & B1 & BB)] _]. cbn [cells_bytes] in BB. rewrite app_nil_r in BB.
    assert (LT : (Z.to_nat (x - a) < length (cbytes (cellw w v)))%nat) by (apply nth_error_Some; rewrite E; discriminate).
    specialize (BB (Z.to_nat (x - a)) LT). rewrite Z2Nat.id in BB by lia. replace (a + (x - a)) with x in BB by lia. rewrite BB. exact E.
  -   destruct e as [a| | | | |]; try discriminate. destruct ((a <=? x) && (x <? a + k)) eqn:C; [|discriminate]. injection E as <-.
    apply andb_prop in C as [C2 C3]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    cbn [mfact_ok zv] in OK. destruct OK as [[WF (B0 & B1 & BB)] _]. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
    assert (L : length (zeros k) = Z.to_nat k) by (unfold zeros; apply repeat_length).
    specialize (BB (Z.to_nat (x - a)) ltac:(rewrite L; lia)). rewrite Z2Nat.id in BB by lia.
    replace (a + (x - a)) with x in BB by lia. rewrite zeros_nth in BB by lia. exact BB.
  -   destruct e as [a| | | | |]; try discriminate. destruct ((a <=? x) && (x <? a + k)) eqn:C; [|discriminate]. injection E as <-.
    apply andb_prop in C as [C2 C3]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    cbn [mfact_ok zv] in OK. specialize (OK (x - a) ltac:(lia)). replace (a + (x - a)) with x in OK by lia. unfold mrd. rewrite OK. reflexivity.
  -   destruct ((lo <=? x) && (x <? hi)) eqn:C; [|discriminate].
    apply andb_prop in C as [C2 C3]. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    cbn [mfact_ok] in OK. unfold mrd. rewrite (OK x ltac:(lia)). exact E.
Qed.

Fixpoint find_byte (l : list mfact) (x : Z) : option byte :=
  match l with [] => None | f :: l' => match fact_byte f x with Some b => Some b | None => find_byte l' x end end.
Lemma find_byte_sound : forall V (m : mem) l x b, Forall (mfact_ok asegs V m) l -> find_byte l x = Some b -> mrd asegs m (wa x) = Some b.
Proof.
  intros V m l. induction l as [|f l IH]; intros x b HF E; [discriminate|]. inversion HF as [|? ? Hf Hl]; subst. cbn [find_byte] in E.
  destruct (fact_byte f x) as [b'|] eqn:FB; [injection E as <-; exact (fact_byte_sound V m f x b' Hf FB)| exact (IH x b Hl E)].
Qed.

Fixpoint lit_bytes_b (l : list mfact) (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match find_byte l A with Some b' => bv_eqb b b' && lit_bytes_b l (A + 1) bs' | None => false end
  end.
Lemma lit_bytes_at : forall V (m : mem) l bs A, Forall (mfact_ok asegs V m) l -> lit_bytes_b l A bs = true ->
  0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m A bs.
Proof.
  intros V m l bs. induction bs as [|b bs IH]; intros A HF H H0 H1.
  - split; [exact H0|]. split; [exact H1|]. intros i Hi. cbn in Hi. lia.
  - cbn [lit_bytes_b] in H. destruct (find_byte l A) as [b'|] eqn:FB; [|discriminate]. apply andb_prop in H as [E1 E2].
    unfold bv_eqb in E1. apply Z.eqb_eq in E1. apply bv_eq in E1. subst b'.
    cbn [length] in H1. destruct (IH (A + 1) HF E2 ltac:(lia) ltac:(lia)) as (_ & _ & BB).
    split; [exact H0|]. split; [exact H1|]. intros i Hi. destruct i as [|i].
    + rewrite Z.add_0_r. cbn [nth_error]. exact (find_byte_sound V m l A b HF FB).
    + cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BB. cbn [length] in Hi. lia.
Qed.

Lemma lit_cells : forall V (m : mem) l A cs, Forall (mfact_ok asegs V m) l -> cells_wf cs -> lit_bytes_b l A (cells_bytes cs) = true ->
  0xa9000 <= A -> A + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m A cs.
Proof.
  intros V m l A cs HF WF HB H0 H1. pose proof (cells_bytes_length cs WF) as LEN.
  apply rw_cell_of_bytes; [exact WF| | exact H0| exact H1].
  apply (lit_bytes_at V m l); [exact HF| exact HB| lia| rewrite LEN; lia].
Qed.
Ltac lcells V m HM A cs H :=
  pose proof (lit_cells V m _ A cs HM ltac:(cbn; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W0 & W1 & W) H0 H1 H2. split; [exact H0|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.
Lemma zero_run : forall (m : mem) A Z0 n W wn, (forall i, 0 <= i < n -> m (wa (Z0 + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m W wn ->
  forall off k, 0 <= off -> 0 <= k -> off + k <= n -> A = Z0 + off -> W <= A -> A + k <= W + wn -> 0 <= A ->
  rw_cells asegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A Z0 n W wn ZR WR off k O0 K0 OK -> WA WB A0.
  assert (HI : Z0 + off + k <= 2^64) by (destruct WR as (_ & W1 & _); lia).
  split; [split; [cbn; split; [apply repeat_length| exact I]|]| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact (wr_at_sub m W wn _ k WR A0 WA WB)].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact A0|]. split; [rewrite repeat_length, Z2Nat.id by lia; exact HI|].
  intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
  unfold mrd. replace (Z0 + off + Z.of_nat i) with (Z0 + (off + Z.of_nat i)) by lia. rewrite ZR by lia. reflexivity.
Qed.

From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct AsanPlanImages AsanHexScan.
Lemma rw_window_rom : forall (x : word), 0xa9000 <= bv_unsigned x < 0x609000 -> seg_rom asegs x <> None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (find_segment asegs (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    change asegs with ASEGS in Hin. rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_readable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at].
      match goal with |- context [segment_byte_at ?l ?o] => destruct (segment_byte_at l o) as [b|] eqn:SB end; [discriminate|]. exfalso.
      revert SB. apply (segment_byte_at_some1 _ 8192); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at].
      match goal with |- context [segment_byte_at ?l ?o] => destruct (segment_byte_at l o) as [b|] eqn:SB end; [discriminate|]. exfalso.
      revert SB. apply (segment_byte_at_some1 _ 5627904); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xab000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [change asegs with ASEGS; rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [change asegs with ASEGS; rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

Lemma junk_cells : forall (m : mem) A n, 0xa9000 <= A -> A + Z.of_nat n <= 0x609000 -> exists bs, rw_cells asegs m A [CB n bs].
Proof.
  intros m A n H0 H1.
  destruct (readable_bytes m n A) as (bs & L & BY); [| lia| lia|].
  { intros y Hy. unfold mrd. destruct (m (wa y)) as [b|]; [exists b; reflexivity|].
    destruct (seg_rom asegs (wa y)) as [b|] eqn:SR; [exists b; reflexivity|]. exfalso. revert SR. apply rw_window_rom. rewrite wa_unsigned by lia. lia. }
  exists bs. split; [split; [cbn; split; [exact L| exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. apply a0_rw_image_wr_at; lia.
Qed.
