(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexZero.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARepInit_kit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LV (V : nat -> Z) (i : nat) : Z :=
  if Nat.eqb i 6 then 256 * V 10%nat + V 6%nat
  else if Nat.eqb i 42 then V 44%nat else if Nat.eqb i 91 then V 78%nat
  else if Nat.eqb i 220 then V 207%nat else if Nat.eqb i 221 then V 208%nat else if Nat.eqb i 222 then V 209%nat
  else if Nat.eqb i 239 then V 226%nat else if Nat.eqb i 240 then V 227%nat else if Nat.eqb i 241 then V 228%nat
  else if Nat.eqb i 258 then V 245%nat else if Nat.eqb i 323 then V 310%nat else if Nat.eqb i 357 then V 344%nat
  else if Nat.eqb i 406 then V 393%nat else if Nat.eqb i 485 then V 469%nat else if Nat.eqb i 486 then V 470%nat
  else if Nat.eqb i 503 then V 487%nat else if Nat.eqb i 584 then V 568%nat
  else if Nat.eqb i 617 then V 601%nat else if Nat.eqb i 618 then V 602%nat else if Nat.eqb i 619 then V 603%nat
  else if Nat.eqb i 620 then V 604%nat else if Nat.eqb i 621 then V 605%nat else if Nat.eqb i 622 then V 606%nat
  else if Nat.eqb i 623 then V 607%nat else if Nat.eqb i 624 then V 608%nat else if Nat.eqb i 625 then V 609%nat
  else if Nat.eqb i 626 then V 610%nat else if Nat.eqb i 627 then V 611%nat
  else if Nat.eqb i 484 then V 468%nat else if Nat.eqb i 324 then V 311%nat
  else V i.
(* [comment removed for export] *)
Lemma LV_sp0 : forall V w U, al_sp0 (mkALayout (LV V) w U) = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
Proof. intros. unfold al_sp0. cbn [al_V LV Nat.eqb]. lia. Qed.
Lemma LV_t : forall V w U, al_t (mkALayout (LV V) w U) = 4096 * V 227%nat.            Proof. reflexivity. Qed.
Lemma LV_ctx : forall V w U, al_ctx (mkALayout (LV V) w U) = 4096 * V 228%nat.        Proof. reflexivity. Qed.
Lemma LV_space_beg : forall V w U, al_space_beg (mkALayout (LV V) w U) = 4096 * (V 208%nat - V 209%nat) + 0x10000. Proof. reflexivity. Qed.
Lemma LV_ptr_array : forall V w U, al_ptr_array (mkALayout (LV V) w U) = 4096 * V 226%nat. Proof. reflexivity. Qed.
Lemma LV_nodes : forall V w U, al_nodes (mkALayout (LV V) w U) = 4096 * V 469%nat.    Proof. reflexivity. Qed.
Lemma LV_store : forall V w U, al_store (mkALayout (LV V) w U) = 4096 * V 470%nat.    Proof. reflexivity. Qed.
Lemma LV_fake : forall V w U, al_fake (mkALayout (LV V) w U) = 4096 * V 393%nat.      Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition pfact_eqb' (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'   (* [comment removed for export] *)
  | _, _ => false
  end.
#[using="Type"] Lemma pfact_eqb'_eq : forall f g, pfact_eqb' f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma pfact_find' : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb' f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb'_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (pfact_find' V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.
Ltac mwr V m HM a n H := pose proof (mwr_find asegs V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.
Ltac mimg V m HM lo hi H := pose proof (mimg_cover asegs V m _ lo hi HM ltac:(vm_compute; reflexivity)) as H.
(* [comment removed for export] *)
Section CANSEC1b. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma mwrs_find : forall V m (l : list mfact) a n,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MWrS a' n' => zexp_eqb a' a && zexp_eqb n' n | _ => false end) l = true ->
  wr_at asegs m (zv V a) (zv V n).
Proof.
  intros V m l a n HF HE. apply existsb_exists in HE as (f & Hin & Hf).
  destruct f; try discriminate. apply andb_prop in Hf as [H1 H2]. apply zexp_eqb_eq in H1. apply zexp_eqb_eq in H2. subst.
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
End CANSEC1b.
Ltac mwrs V m HM a n H := pose proof (mwrs_find V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma bytes_eq_of_unsigned' : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma wr_at_sub : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zshape (cs : list cell) : bool :=
  match cs with
  | [] => true
  | C1 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C2 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C4 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C8 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | CB n bs :: cs' => Nat.eqb (length bs) n && forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs && zshape cs'
  end.

#[using="Type"] Lemma repeat_zero_eq : forall (bs : list byte), forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs = true ->
  bs = repeat (Z_to_bv 8 0) (length bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; [reflexivity|]. apply andb_prop in H as [H1 H2].
  f_equal; [| apply IH; exact H2]. apply bv_eq. apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.

#[using="Type"] Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma le2_zero : le2 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 2.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma word_zero_eq : forall v : word, (bv_unsigned v =? 0) = true -> v = Z_to_bv 64 0.
Proof. intros v H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma byte_zero_eq : forall b : byte, (bv_unsigned b =? 0) = true -> b = Z_to_bv 8 0.
Proof. intros b H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma cbytes_zero : forall c, zshape [c] = true -> cbytes c = repeat (Z_to_bv 8 0) (csize c) /\ cells_wf [c].
Proof.
  intros c H. destruct c as [v|v|v|v|n bs]; cbn [zshape] in H; rewrite ?andb_true_r in H.
  - apply word_zero_eq in H. subst v. split; [exact le8_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le4_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le2_zero| cbn; split; exact I].
  - apply byte_zero_eq in H. subst v. split; [reflexivity| cbn; split; exact I].
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. split; [| cbn; split; [exact H1| exact I]].
    cbn [cbytes csize]. rewrite (repeat_zero_eq bs H2) at 1. rewrite H1. reflexivity.
Qed.

#[using="Type"] Lemma zshape_bytes : forall cs, zshape cs = true ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) /\ cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [split; [reflexivity| exact I]|].
  assert (Hc : zshape [c] = true /\ zshape cs = true).
  { destruct c; cbn in H |- *; repeat (apply andb_prop in H as [H ?]); rewrite ?andb_true_r; auto.
    split; [apply andb_true_intro; split; assumption| assumption]. }
  destruct Hc as [Hc Hcs]. destruct (cbytes_zero c Hc) as [Ec Wc]. destruct (IH Hcs) as [Ecs Wcs].
  split.
  - cbn [cells_bytes cells_size]. rewrite Ec, Ecs, <- repeat_app. reflexivity.
  - destruct c; cbn in Wc |- *; tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcells : forall m A cs,
  zshape cs = true ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m (wa (A + i)) = Some (Z_to_bv 8 0)) ->
  wr_at asegs m A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m A cs.
Proof.
  intros m A cs Hz Z0 W. destruct (zshape_bytes cs Hz) as [E WF].
  eapply rw_cells_recast; [apply (mzero_rw_cells asegs m A (Z.of_nat (cells_size cs))); [exact Z0| exact W| lia]| exact WF| |].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, E. unfold zeros. rewrite Nat2Z.id. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

#[using="Type"] Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
      specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

End CANSEC2.
Notation S3 := Asan_seg_bytes_003 (only parsing).
Section CANSEC3. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition SEG3 : Z := 0xa7000.

#[using="Type"] Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma a_find_segment_3 : forall i, 0xa7000 <= i < 0x603000 -> find_segment asegs i 1 = Some Asan_segment_003.
Proof.
  intros i Hi. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x32000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x32000 i); destruct (Z.leb_spec0 (i + 1) 0xa4000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xa4000 i); destruct (Z.leb_spec0 (i + 1) 0xa7000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xa7000 i); destruct (Z.leb_spec0 (i + 1) 0x603000); cbn [andb]; try lia. reflexivity.
Qed.
#[using="Type"] Lemma seg3_base : Z.of_N (seg_base Asan_segment_003) = 0xa7000.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma seg3_readable : seg_readable Asan_segment_003 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma img_zero_run : forall (off n : N) m lo,
  zscanN Asan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x603000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) ->
  forall i, 0 <= i < Z.of_N n -> mrd asegs m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros off n m lo SC -> Hhi Hnone i Hi.
  unfold mrd. rewrite (Hnone (0xa7000 + Z.of_N off + i)) by lia.
  unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_3 (0xa7000 + Z.of_N off + i)) by lia. rewrite seg3_readable, seg3_base. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes seg_bytes Asan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (Z.to_N (0xa7000 + Z.of_N off + i - 0xa7000) <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace (Z.to_N (0xa7000 + Z.of_N off + i - 0xa7000)) with (off + Z.to_N i)%N by lia.
  rewrite (zscanN_sound _ 64 off n SC (Z.to_N i)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma img_zero_stk : forall (off n : N) m lo,
  zscanN Asan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x603000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at asegs m lo (Z.of_N n) ->
  stk asegs m lo (lo + Z.of_N n).
Proof.
  intros off n m lo SC Hlo Hhi Hnone W. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  (nd_pre W 3%nat; intros W1 W2 W3; nd_post). split; [lia|]. split; [lia|]. intros a Ha.
  split; [replace a with (lo + (a - lo)) by lia; apply W3; lia|].
  exists (Z_to_bv 8 0). replace a with (lo + (a - lo)) by lia. apply R. lia.
Qed.

#[using="Type"] Lemma img_zero_bytes_at : forall (off n : N) m lo k,
  zscanN Asan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x603000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> (Z.of_nat k <= Z.of_N n) ->
  bytes_at asegs m lo (repeat (Z_to_bv 8 0) k).
Proof.
  intros off n m lo k SC Hlo Hhi Hnone Hk. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). apply R. lia.
Qed.

#[using="Type"] Lemma img_zero_cells : forall (off n : N) m lo cs,
  zscanN Asan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x603000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at asegs m lo (Z.of_nat (cells_size cs)) ->
  zshape cs = true -> Z.of_nat (cells_size cs) <= Z.of_N n ->
  rw_cells asegs m lo cs.
Proof.
  intros off n m lo cs SC Hlo Hhi Hnone W Hz Hsz. destruct (zshape_bytes cs Hz) as [E WF].
  split; [split; [exact WF|]| exact W]. rewrite E. eapply img_zero_bytes_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_CB0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn. unfold bytes_at. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - cbn. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr asegs m A [].
Proof. intros m A H0 H1. unfold u32arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof. intros m A H0 H1. unfold u64arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u32s_zero : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u32s flat_map]. rewrite IH.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app, le4_zero. reflexivity.
Qed.
#[using="Type"] Lemma u64s_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s flat_map]. rewrite IH.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app, le8_zero. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_zero : forall m A n,
  (forall i, 0 <= i < Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  bytes_at asegs m A (repeat (Z_to_bv 8 0) n).
Proof.
  intros m A n Z0 H0 H1. split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
  rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). unfold mrd. rewrite (Z0 (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

#[using="Type"] Lemma u32arr_zero : forall m A n,
  (forall i, 0 <= i < 4 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m A (4 * Z.of_nat n) ->
  u32arr asegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. (pose proof W as ndP__; nd_pre ndP__ 3%nat; intros W1 W2 _; nd_post). split; [| rewrite repeat_length; exact W].
  rewrite u32s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

#[using="Type"] Lemma u64arr_zero : forall m A n,
  (forall i, 0 <= i < 8 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m A (8 * Z.of_nat n) ->
  u64arr asegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. (pose proof W as ndP__; nd_pre ndP__ 3%nat; intros W1 W2 _; nd_post). split; [| rewrite repeat_length; exact W].
  rewrite u64s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma img_cell : forall m A (bs : list byte) (v : Z),
  (forall i, A <= i < A + 8 -> m (wa i) = None) ->
  length bs = 8%nat -> rw_bytes_b asegs A bs = true -> bs = le8 (Z_to_bv 64 v) -> 0 <= A -> A + 8 <= 2^64 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A bs v Hm Hl Hb Hbs H0 H1.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A bs)| cbn; split; [reflexivity| exact I]| |].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hm. rewrite Hl in Ha. lia.
  - exact Hb. - lia. - rewrite Hl. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, Hbs. reflexivity.
  - cbn. rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma img_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells asegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac aimg V m HM A cs H :=
  pose proof (img_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rw_cells_cons : forall m A c cs,
  rw_cells asegs m A [c] -> rw_cells asegs m (A + Z.of_nat (csize c)) cs -> rw_cells asegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app asegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.
#[using="Type"] Lemma rw_cells_hd : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [H _]. exact H. Qed.
#[using="Type"] Lemma rw_cells_tl : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.

(* [comment removed for export] *)
End CANSEC4.
Ltac recast H := eapply rw_cells_recast; [exact H| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned'; vm_compute; reflexivity| reflexivity].

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LV (V : nat -> Z) (i : nat) : Z :=
  if Nat.eqb i 6 then 256 * V 10%nat + V 6%nat
  else if Nat.eqb i 42 then V 44%nat else if Nat.eqb i 91 then V 78%nat
  else if Nat.eqb i 220 then V 207%nat else if Nat.eqb i 221 then V 208%nat else if Nat.eqb i 222 then V 209%nat
  else if Nat.eqb i 239 then V 226%nat else if Nat.eqb i 240 then V 227%nat else if Nat.eqb i 241 then V 228%nat
  else if Nat.eqb i 258 then V 245%nat else if Nat.eqb i 323 then V 310%nat else if Nat.eqb i 357 then V 344%nat
  else if Nat.eqb i 406 then V 393%nat else if Nat.eqb i 485 then V 469%nat else if Nat.eqb i 486 then V 470%nat
  else if Nat.eqb i 503 then V 487%nat else if Nat.eqb i 584 then V 568%nat
  else if Nat.eqb i 617 then V 601%nat else if Nat.eqb i 618 then V 602%nat else if Nat.eqb i 619 then V 603%nat
  else if Nat.eqb i 620 then V 604%nat else if Nat.eqb i 621 then V 605%nat else if Nat.eqb i 622 then V 606%nat
  else if Nat.eqb i 623 then V 607%nat else if Nat.eqb i 624 then V 608%nat else if Nat.eqb i 625 then V 609%nat
  else if Nat.eqb i 626 then V 610%nat else if Nat.eqb i 627 then V 611%nat
  else if Nat.eqb i 484 then V 468%nat else if Nat.eqb i 324 then V 311%nat
  else V i.
(* [comment removed for export] *)
Lemma LV_sp0 : forall V w U, al_sp0 (mkALayout (LV V) w U) = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
Proof. intros. unfold al_sp0. cbn [al_V LV Nat.eqb]. lia. Qed.
Lemma LV_t : forall V w U, al_t (mkALayout (LV V) w U) = 4096 * V 227%nat.            Proof. reflexivity. Qed.
Lemma LV_ctx : forall V w U, al_ctx (mkALayout (LV V) w U) = 4096 * V 228%nat.        Proof. reflexivity. Qed.
Lemma LV_space_beg : forall V w U, al_space_beg (mkALayout (LV V) w U) = 4096 * (V 208%nat - V 209%nat) + 0x10000. Proof. reflexivity. Qed.
Lemma LV_ptr_array : forall V w U, al_ptr_array (mkALayout (LV V) w U) = 4096 * V 226%nat. Proof. reflexivity. Qed.
Lemma LV_nodes : forall V w U, al_nodes (mkALayout (LV V) w U) = 4096 * V 469%nat.    Proof. reflexivity. Qed.
Lemma LV_store : forall V w U, al_store (mkALayout (LV V) w U) = 4096 * V 470%nat.    Proof. reflexivity. Qed.
Lemma LV_fake : forall V w U, al_fake (mkALayout (LV V) w U) = 4096 * V 393%nat.      Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition pfact_eqb' (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'   (* [comment removed for export] *)
  | _, _ => false
  end.
#[using="Type"] Lemma pfact_eqb'_eq : forall f g, pfact_eqb' f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
#[using="Type"] Lemma pfact_find' : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb' f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb'_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (pfact_find' V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.
Ltac mwr V m HM a n H := pose proof (mwr_find asegs V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.
Ltac mimg V m HM lo hi H := pose proof (mimg_cover asegs V m _ lo hi HM ltac:(vm_compute; reflexivity)) as H.
(* [comment removed for export] *)
Section CANSEC1b. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma mwrs_find : forall V m (l : list mfact) a n,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MWrS a' n' => zexp_eqb a' a && zexp_eqb n' n | _ => false end) l = true ->
  wr_at asegs m (zv V a) (zv V n).
Proof.
  intros V m l a n HF HE. apply existsb_exists in HE as (f & Hin & Hf).
  destruct f; try discriminate. apply andb_prop in Hf as [H1 H2]. apply zexp_eqb_eq in H1. apply zexp_eqb_eq in H2. subst.
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
End CANSEC1b.
Ltac mwrs V m HM a n H := pose proof (mwrs_find V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma bytes_eq_of_unsigned' : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma wr_at_sub : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zshape (cs : list cell) : bool :=
  match cs with
  | [] => true
  | C1 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C2 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C4 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C8 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | CB n bs :: cs' => Nat.eqb (length bs) n && forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs && zshape cs'
  end.

#[using="Type"] Lemma repeat_zero_eq : forall (bs : list byte), forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs = true ->
  bs = repeat (Z_to_bv 8 0) (length bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; [reflexivity|]. apply andb_prop in H as [H1 H2].
  f_equal; [| apply IH; exact H2]. apply bv_eq. apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.

#[using="Type"] Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma le2_zero : le2 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 2.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma word_zero_eq : forall v : word, (bv_unsigned v =? 0) = true -> v = Z_to_bv 64 0.
Proof. intros v H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma byte_zero_eq : forall b : byte, (bv_unsigned b =? 0) = true -> b = Z_to_bv 8 0.
Proof. intros b H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma cbytes_zero : forall c, zshape [c] = true -> cbytes c = repeat (Z_to_bv 8 0) (csize c) /\ cells_wf [c].
Proof.
  intros c H. destruct c as [v|v|v|v|n bs]; cbn [zshape] in H; rewrite ?andb_true_r in H.
  - apply word_zero_eq in H. subst v. split; [exact le8_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le4_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le2_zero| cbn; split; exact I].
  - apply byte_zero_eq in H. subst v. split; [reflexivity| cbn; split; exact I].
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. split; [| cbn; split; [exact H1| exact I]].
    cbn [cbytes csize]. rewrite (repeat_zero_eq bs H2) at 1. rewrite H1. reflexivity.
Qed.

#[using="Type"] Lemma zshape_bytes : forall cs, zshape cs = true ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) /\ cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [split; [reflexivity| exact I]|].
  assert (Hc : zshape [c] = true /\ zshape cs = true).
  { destruct c; cbn in H |- *; repeat (apply andb_prop in H as [H ?]); rewrite ?andb_true_r; auto.
    split; [apply andb_true_intro; split; assumption| assumption]. }
  destruct Hc as [Hc Hcs]. destruct (cbytes_zero c Hc) as [Ec Wc]. destruct (IH Hcs) as [Ecs Wcs].
  split.
  - cbn [cells_bytes cells_size]. rewrite Ec, Ecs, <- repeat_app. reflexivity.
  - destruct c; cbn in Wc |- *; tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zcells : forall m A cs,
  zshape cs = true ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m (wa (A + i)) = Some (Z_to_bv 8 0)) ->
  wr_at asegs m A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m A cs.
Proof.
  intros m A cs Hz Z0 W. destruct (zshape_bytes cs Hz) as [E WF].
  eapply rw_cells_recast; [apply (mzero_rw_cells asegs m A (Z.of_nat (cells_size cs))); [exact Z0| exact W| lia]| exact WF| |].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, E. unfold zeros. rewrite Nat2Z.id. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

#[using="Type"] Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
      specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

End CANSEC2.
Notation S3 := AsanUbsan_seg_bytes_003 (only parsing).
Section CANSEC3. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition SEG3 : Z := 0xa7000.

#[using="Type"] Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55d000%N.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma a_find_segment_3 : forall i, 0xa7000 <= i < 0x604000 -> find_segment asegs i 1 = Some AsanUbsan_segment_003.
Proof.
  intros i Hi. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x32000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x32000 i); destruct (Z.leb_spec0 (i + 1) 0xa5000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xa5000 i); destruct (Z.leb_spec0 (i + 1) 0xa7000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xa7000 i); destruct (Z.leb_spec0 (i + 1) 0x604000); cbn [andb]; try lia. reflexivity.
Qed.
#[using="Type"] Lemma seg3_base : Z.of_N (seg_base AsanUbsan_segment_003) = 0xa7000.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma seg3_readable : seg_readable AsanUbsan_segment_003 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma img_zero_run : forall (off n : N) m lo,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x604000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) ->
  forall i, 0 <= i < Z.of_N n -> mrd asegs m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros off n m lo SC -> Hhi Hnone i Hi.
  unfold mrd. rewrite (Hnone (0xa7000 + Z.of_N off + i)) by lia.
  unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_3 (0xa7000 + Z.of_N off + i)) by lia. rewrite seg3_readable, seg3_base. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes seg_bytes AsanUbsan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (Z.to_N (0xa7000 + Z.of_N off + i - 0xa7000) <? 0x55d000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace (Z.to_N (0xa7000 + Z.of_N off + i - 0xa7000)) with (off + Z.to_N i)%N by lia.
  rewrite (zscanN_sound _ 64 off n SC (Z.to_N i)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma img_zero_stk : forall (off n : N) m lo,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x604000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at asegs m lo (Z.of_N n) ->
  stk asegs m lo (lo + Z.of_N n).
Proof.
  intros off n m lo SC Hlo Hhi Hnone W. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  (nd_pre W 3%nat; intros W1 W2 W3; nd_post). split; [lia|]. split; [lia|]. intros a Ha.
  split; [replace a with (lo + (a - lo)) by lia; apply W3; lia|].
  exists (Z_to_bv 8 0). replace a with (lo + (a - lo)) by lia. apply R. lia.
Qed.

#[using="Type"] Lemma img_zero_bytes_at : forall (off n : N) m lo k,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x604000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> (Z.of_nat k <= Z.of_N n) ->
  bytes_at asegs m lo (repeat (Z_to_bv 8 0) k).
Proof.
  intros off n m lo k SC Hlo Hhi Hnone Hk. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). apply R. lia.
Qed.

#[using="Type"] Lemma img_zero_cells : forall (off n : N) m lo cs,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xa7000 + Z.of_N off -> lo + Z.of_N n <= 0x604000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at asegs m lo (Z.of_nat (cells_size cs)) ->
  zshape cs = true -> Z.of_nat (cells_size cs) <= Z.of_N n ->
  rw_cells asegs m lo cs.
Proof.
  intros off n m lo cs SC Hlo Hhi Hnone W Hz Hsz. destruct (zshape_bytes cs Hz) as [E WF].
  split; [split; [exact WF|]| exact W]. rewrite E. eapply img_zero_bytes_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_CB0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn. unfold bytes_at. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - cbn. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr asegs m A [].
Proof. intros m A H0 H1. unfold u32arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof. intros m A H0 H1. unfold u64arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u32s_zero : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u32s flat_map]. rewrite IH.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app, le4_zero. reflexivity.
Qed.
#[using="Type"] Lemma u64s_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s flat_map]. rewrite IH.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app, le8_zero. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_zero : forall m A n,
  (forall i, 0 <= i < Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  bytes_at asegs m A (repeat (Z_to_bv 8 0) n).
Proof.
  intros m A n Z0 H0 H1. split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
  rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). unfold mrd. rewrite (Z0 (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

#[using="Type"] Lemma u32arr_zero : forall m A n,
  (forall i, 0 <= i < 4 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m A (4 * Z.of_nat n) ->
  u32arr asegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. (pose proof W as ndP__; nd_pre ndP__ 3%nat; intros W1 W2 _; nd_post). split; [| rewrite repeat_length; exact W].
  rewrite u32s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

#[using="Type"] Lemma u64arr_zero : forall m A n,
  (forall i, 0 <= i < 8 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m A (8 * Z.of_nat n) ->
  u64arr asegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. (pose proof W as ndP__; nd_pre ndP__ 3%nat; intros W1 W2 _; nd_post). split; [| rewrite repeat_length; exact W].
  rewrite u64s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma img_cell : forall m A (bs : list byte) (v : Z),
  (forall i, A <= i < A + 8 -> m (wa i) = None) ->
  length bs = 8%nat -> rw_bytes_b asegs A bs = true -> bs = le8 (Z_to_bv 64 v) -> 0 <= A -> A + 8 <= 2^64 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A bs v Hm Hl Hb Hbs H0 H1.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A bs)| cbn; split; [reflexivity| exact I]| |].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hm. rewrite Hl in Ha. lia.
  - exact Hb. - lia. - rewrite Hl. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, Hbs. reflexivity.
  - cbn. rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma img_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok asegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells asegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac aimg V m HM A cs H :=
  pose proof (img_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rw_cells_cons : forall m A c cs,
  rw_cells asegs m A [c] -> rw_cells asegs m (A + Z.of_nat (csize c)) cs -> rw_cells asegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app asegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.
#[using="Type"] Lemma rw_cells_hd : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [H _]. exact H. Qed.
#[using="Type"] Lemma rw_cells_tl : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.

(* [comment removed for export] *)
End CANSEC4.
Ltac recast H := eapply rw_cells_recast; [exact H| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned'; vm_compute; reflexivity| reflexivity].
End TwB.
End ARepInit_kit.

(* [comment removed for export] *)
Module AHandoffKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac mf1b V m HM a i v H :=
  let ai := eval vm_compute in (a + i) in
  let bi := eval vm_compute in (v / 256 ^ i mod 256) in
  mf V m HM (MCell (ZLit ai) 1 (ZLit bi)) H.

Ltac mf8 V m HM a v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  let H4 := fresh "B4" in let H5 := fresh "B5" in let H6 := fresh "B6" in let H7 := fresh "B7" in
  mf1b V m HM a 0 v H0; mf1b V m HM a 1 v H1; mf1b V m HM a 2 v H2; mf1b V m HM a 3 v H3;
  mf1b V m HM a 4 v H4; mf1b V m HM a 5 v H5; mf1b V m HM a 6 v H6; mf1b V m HM a 7 v H7;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in let J4 := fresh "J" in
  let J5 := fresh "J" in let J6 := fresh "J" in let J7 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3; rw_join J3 H4 J4; rw_join J4 H5 J5; rw_join J5 H6 J6; rw_join J6 H7 J7;
  assert (H : rw_cells asegs m a [C8 (Z_to_bv 64 v)]) by recast J7; clear J7.

Ltac mf4 V m HM a v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  mf1b V m HM a 0 v H0; mf1b V m HM a 1 v H1; mf1b V m HM a 2 v H2; mf1b V m HM a 3 v H3;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3;
  assert (H : rw_cells asegs m a [C4 (Z_to_bv 64 v)]) by recast J3; clear J3.

(* [comment removed for export] *)
Ltac mf1bo V m HM base off i v H :=
  let oi := eval vm_compute in (off + i) in
  let bi := eval vm_compute in (v / 256 ^ i mod 256) in
  mf V m HM (MCell (ZAdd base (ZLit oi)) 1 (ZLit bi)) H.
Ltac mf8o V m HM base off v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  let H4 := fresh "B4" in let H5 := fresh "B5" in let H6 := fresh "B6" in let H7 := fresh "B7" in
  mf1bo V m HM base off 0 v H0; mf1bo V m HM base off 1 v H1; mf1bo V m HM base off 2 v H2; mf1bo V m HM base off 3 v H3;
  mf1bo V m HM base off 4 v H4; mf1bo V m HM base off 5 v H5; mf1bo V m HM base off 6 v H6; mf1bo V m HM base off 7 v H7;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in let J4 := fresh "J" in
  let J5 := fresh "J" in let J6 := fresh "J" in let J7 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3; rw_join J3 H4 J4; rw_join J4 H5 J5; rw_join J5 H6 J6; rw_join J6 H7 J7;
  lazymatch type of J7 with rw_cells _ _ ?A _ =>
    assert (H : rw_cells asegs m A [C8 (Z_to_bv 64 v)]) by recast J7; clear J7 end.

(* [comment removed for export] *)
Section ZeroRun. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma mzero_cells : forall (V : nat -> Z) (m : amem) (l : list mfact) a n lo k,
  Forall (mfact_ok asegs V m) l -> existsb (mfact_eqb (MZero a n)) l = true ->
  zv V a <= lo -> lo + k <= zv V a + n -> 0 <= lo -> lo + k <= 2^64 -> 0 <= k ->
  rw_cells asegs m lo [CB (Z.to_nat k) (zeros k)].
Proof.
  intros V m l a n lo k HM HE H1 H2 H3 H4 H5.
  pose proof (mfact_find asegs V m l (MZero a n) HM HE) as Z0. cbn [mfact_ok] in Z0.
  apply (overlay_zero_rw asegs m lo k); [exact H3 | unfold MainExport.two64; lia | exact H5 |].
  intros i Hi. replace (lo + i) with (zv V a + (lo - zv V a + i)) by lia. apply Z0. lia.
Qed.
End ZeroRun.

(* [comment removed for export] *)
Section TlsAt. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition tls_at (V : nat -> Z) : Prop :=
  ATPv = 0x5e15b8
  /\ kt_res = (if 6165744 <? 4096 * V 208%nat then 1 else 0)
  /\ kt_t = (if 6165744 <? 4096 * V 227%nat then 1 else 0)
  /\ AAHMv = 4096 * V 207%nat.      (* [comment removed for export] *)
#[using="Type"] Lemma tls_at_tp : forall V, tls_at V -> ATPv = 0x5e15b8.
Proof. intros V H. exact (proj1 H). Qed.
End TlsAt.

(* [comment removed for export] *)
Section ShadowRun. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma zchunk_pointwise_k : forall (m : amem) A n, rw_cells asegs m A [CB (Z.to_nat n) (zeros n)] -> 0x603000 <= A ->
  forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post).
  unfold zeros in B1, B. rewrite repeat_length in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_zero_pt : forall (V : nat -> Z) (m : amem) a,
  ashadow1 V m -> Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts ->
  ashadow a ->
  ~ (0x7fffa000 <= a < 0x7fffa000 + 779776) ->
  ~ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512) ->
  ~ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192) ->
  m (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros V m a SH1 HM HP HSH E1 E2 E3.
  mf V m HM (MZeroC (ZV 1084) 8) Z84. mf V m HM (MZeroC (ZV 1085) 8) Z85.
  pf V HP (PVar 1084 2201439137792 17594333495288) P84. pf V HP (PVar 1085 2201439137792 17594333495288) P85.
  destruct (Z_le_gt_dec (V 1084%nat) a) as [A1|A1]; [destruct (Z_lt_le_dec a (V 1084%nat + 8)) as [A2|A2]|];
    [ replace a with (V 1084%nat + (a - V 1084%nat)) by lia; apply (zchunk_pointwise_k m _ 8 Z84); lia | | ].
  all: (destruct (Z_le_gt_dec (V 1085%nat) a) as [B1|B1]; [destruct (Z_lt_le_dec a (V 1085%nat + 8)) as [B2|B2]|];
        [ replace a with (V 1085%nat + (a - V 1085%nat)) by lia; apply (zchunk_pointwise_k m _ 8 Z85); lia | | ]).
  all: apply SH1; [exact HSH|]; unfold ashadow_exposed; clear HM HP SH1 Z84 Z85;
       intros [X|[X|[X|[X|X]]]]; first [tauto | lia | unfold ASHOFF in *; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma shadow_zero_run : forall (V : nat -> Z) (m : amem) lo n,
  ashadow1 V m -> Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a) ->
  (forall a, lo <= a < lo + n ->
      ~ (0x7fffa000 <= a < 0x7fffa000 + 779776)
   /\ ~ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512)
   /\ ~ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192)) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at asegs m lo n /\ rw_cells asegs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n SH1 HM HP Hn HSH HEX.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. (nd_pre (HEX (lo + i) ltac:(lia)) 3%nat; intros E1 E2 E3; nd_post).
    apply (shadow_zero_pt V m (lo + i) SH1 HM HP); [apply HSH; lia | exact E1 | exact E2 | exact E3]. }
  split; [exact Z0|].
  destruct (HSH lo ltac:(lia)) as [S1|S1]; destruct (HSH (lo + n - 1) ltac:(lia)) as [S2|S2];
    apply overlay_zero_rw; first [exact Z0 | unfold MainExport.two64; lia | lia].
Qed.
End ShadowRun.

Section Test. Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Variables (V : nat -> Z) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  (* [comment removed for export] *)
  #[using="V HM"] Lemma cflags32_test : rw_cells asegs m 0x140148 [C8 (Z_to_bv 64 128849084416)].
  Proof. mf8 V m HM 0x140148 128849084416 F. exact F. Qed.
End Test.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac mf1b V m HM a i v H :=
  let ai := eval vm_compute in (a + i) in
  let bi := eval vm_compute in (v / 256 ^ i mod 256) in
  mf V m HM (MCell (ZLit ai) 1 (ZLit bi)) H.

Ltac mf8 V m HM a v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  let H4 := fresh "B4" in let H5 := fresh "B5" in let H6 := fresh "B6" in let H7 := fresh "B7" in
  mf1b V m HM a 0 v H0; mf1b V m HM a 1 v H1; mf1b V m HM a 2 v H2; mf1b V m HM a 3 v H3;
  mf1b V m HM a 4 v H4; mf1b V m HM a 5 v H5; mf1b V m HM a 6 v H6; mf1b V m HM a 7 v H7;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in let J4 := fresh "J" in
  let J5 := fresh "J" in let J6 := fresh "J" in let J7 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3; rw_join J3 H4 J4; rw_join J4 H5 J5; rw_join J5 H6 J6; rw_join J6 H7 J7;
  assert (H : rw_cells asegs m a [C8 (Z_to_bv 64 v)]) by recast J7; clear J7.

Ltac mf4 V m HM a v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  mf1b V m HM a 0 v H0; mf1b V m HM a 1 v H1; mf1b V m HM a 2 v H2; mf1b V m HM a 3 v H3;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3;
  assert (H : rw_cells asegs m a [C4 (Z_to_bv 64 v)]) by recast J3; clear J3.

(* [comment removed for export] *)
Ltac mf1bo V m HM base off i v H :=
  let oi := eval vm_compute in (off + i) in
  let bi := eval vm_compute in (v / 256 ^ i mod 256) in
  mf V m HM (MCell (ZAdd base (ZLit oi)) 1 (ZLit bi)) H.
Ltac mf8o V m HM base off v H :=
  let H0 := fresh "B0" in let H1 := fresh "B1" in let H2 := fresh "B2" in let H3 := fresh "B3" in
  let H4 := fresh "B4" in let H5 := fresh "B5" in let H6 := fresh "B6" in let H7 := fresh "B7" in
  mf1bo V m HM base off 0 v H0; mf1bo V m HM base off 1 v H1; mf1bo V m HM base off 2 v H2; mf1bo V m HM base off 3 v H3;
  mf1bo V m HM base off 4 v H4; mf1bo V m HM base off 5 v H5; mf1bo V m HM base off 6 v H6; mf1bo V m HM base off 7 v H7;
  let J1 := fresh "J" in let J2 := fresh "J" in let J3 := fresh "J" in let J4 := fresh "J" in
  let J5 := fresh "J" in let J6 := fresh "J" in let J7 := fresh "J" in
  rw_join H0 H1 J1; rw_join J1 H2 J2; rw_join J2 H3 J3; rw_join J3 H4 J4; rw_join J4 H5 J5; rw_join J5 H6 J6; rw_join J6 H7 J7;
  lazymatch type of J7 with rw_cells _ _ ?A _ =>
    assert (H : rw_cells asegs m A [C8 (Z_to_bv 64 v)]) by recast J7; clear J7 end.

(* [comment removed for export] *)
Section ZeroRun. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma mzero_cells : forall (V : nat -> Z) (m : amem) (l : list mfact) a n lo k,
  Forall (mfact_ok asegs V m) l -> existsb (mfact_eqb (MZero a n)) l = true ->
  zv V a <= lo -> lo + k <= zv V a + n -> 0 <= lo -> lo + k <= 2^64 -> 0 <= k ->
  rw_cells asegs m lo [CB (Z.to_nat k) (zeros k)].
Proof.
  intros V m l a n lo k HM HE H1 H2 H3 H4 H5.
  pose proof (mfact_find asegs V m l (MZero a n) HM HE) as Z0. cbn [mfact_ok] in Z0.
  apply (overlay_zero_rw asegs m lo k); [exact H3 | unfold AS.MainExport.TwB.two64; lia | exact H5 |].
  intros i Hi. replace (lo + i) with (zv V a + (lo - zv V a + i)) by lia. apply Z0. lia.
Qed.
End ZeroRun.

(* [comment removed for export] *)
Section TlsAt. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition tls_at (V : nat -> Z) : Prop :=
  ATPv = 0x5e19b8
  /\ kt_res = (if 6166768 <? 4096 * V 208%nat then 1 else 0)
  /\ kt_t = (if 6166768 <? 4096 * V 227%nat then 1 else 0)
  /\ AAHMv = 4096 * V 207%nat.      (* [comment removed for export] *)
#[using="Type"] Lemma tls_at_tp : forall V, tls_at V -> ATPv = 0x5e19b8.
Proof. intros V H. exact (proj1 H). Qed.
End TlsAt.

(* [comment removed for export] *)
Section ShadowRun. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma zchunk_pointwise_k : forall (m : amem) A n, rw_cells asegs m A [CB (Z.to_nat n) (zeros n)] -> 0x604000 <= A ->
  forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. (nd_pre B 3%nat; intros B0 B1 B; nd_post).
  unfold zeros in B1, B. rewrite repeat_length in B1, B.
  specialize (B (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shadow_zero_pt : forall (V : nat -> Z) (m : amem) a,
  ashadow1 V m -> Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts ->
  ashadow a ->
  ~ (0x7fffa000 <= a < 0x7fffa000 + 780288) ->
  ~ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512) ->
  ~ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192) ->
  m (wa a) = Some (Z_to_bv 8 0).
Proof.
  intros V m a SH1 HM HP HSH E1 E2 E3.
  mf V m HM (MZeroC (ZV 1084) 8) Z84. mf V m HM (MZeroC (ZV 1085) 8) Z85.
  pf V HP (PVar 1084 2201439137792 17594333495288) P84. pf V HP (PVar 1085 2201439137792 17594333495288) P85.
  destruct (Z_le_gt_dec (V 1084%nat) a) as [A1|A1]; [destruct (Z_lt_le_dec a (V 1084%nat + 8)) as [A2|A2]|];
    [ replace a with (V 1084%nat + (a - V 1084%nat)) by lia; apply (zchunk_pointwise_k m _ 8 Z84); lia | | ].
  all: (destruct (Z_le_gt_dec (V 1085%nat) a) as [B1|B1]; [destruct (Z_lt_le_dec a (V 1085%nat + 8)) as [B2|B2]|];
        [ replace a with (V 1085%nat + (a - V 1085%nat)) by lia; apply (zchunk_pointwise_k m _ 8 Z85); lia | | ]).
  all: apply SH1; [exact HSH|]; unfold ashadow_exposed; clear HM HP SH1 Z84 Z85;
       intros [X|[X|[X|[X|X]]]]; first [tauto | lia | unfold ASHOFF in *; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma shadow_zero_run : forall (V : nat -> Z) (m : amem) lo n,
  ashadow1 V m -> Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a) ->
  (forall a, lo <= a < lo + n ->
      ~ (0x7fffa000 <= a < 0x7fffa000 + 780288)
   /\ ~ (ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 <= a < ASHOFF + (4096 * V 208%nat - 4096 * V 209%nat + 137439019008) / 8 + 512)
   /\ ~ (ASHOFF + 4096 * V 228%nat / 8 <= a < ASHOFF + 4096 * V 228%nat / 8 + 8192)) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at asegs m lo n /\ rw_cells asegs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n SH1 HM HP Hn HSH HEX.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. (nd_pre (HEX (lo + i) ltac:(lia)) 3%nat; intros E1 E2 E3; nd_post).
    apply (shadow_zero_pt V m (lo + i) SH1 HM HP); [apply HSH; lia | exact E1 | exact E2 | exact E3]. }
  split; [exact Z0|].
  destruct (HSH lo ltac:(lia)) as [S1|S1]; destruct (HSH (lo + n - 1) ltac:(lia)) as [S2|S2];
    apply overlay_zero_rw; first [exact Z0 | unfold AS.MainExport.TwB.two64; lia | lia].
Qed.
End ShadowRun.

Section Test. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Variables (V : nat -> Z) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  (* [comment removed for export] *)
  #[using="V HM"] Lemma cflags32_test : rw_cells asegs m 0x140548 [C8 (Z_to_bv 64 128849084416)].
  Proof. mf8 V m HM 0x140548 128849084416 F. exact F. Qed.
End Test.
End TwB.
End AHandoffKit.

(* [comment removed for export] *)
Module ARepInit_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition X0 : aconc := mkAConc (fun _ => mkXClass [] []) [].
(* [comment removed for export] *)
Definition ST0 (V : nat -> Z) : astate := ainit (a_space_beg0 V) (a_ptr_array0 V).

#[using="Type"] Lemma get_cls_ST0 : forall V c, get_cls (ST0 V) c = aclass0.
Proof. intros. apply get_cls_ainit. Qed.
#[using="Type"] Lemma max_count_ST0 : forall V c, max_count (ST0 V) c = 0.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma ndist_ST0 : forall V c, ndist (ST0 V) c = 0.
Proof. intros. unfold ndist. rewrite get_cls_ST0. cbn. apply Zdiv_0_l. Qed.
#[using="Type"] Lemma busy_of_X0 : forall c k, busy_of X0 c k = None.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma busy_slots_X0 : forall c, busy_slots X0 c = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_Z_bounds : forall x, x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x. unfold page_round_up_Z, page_size. split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Local Ltac aobj_close :=
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI;
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]; split; [lia|]; split; [lia|]; split; lia.

#[using="Type"] Theorem alayout_stack_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  al_bot (mkALayout (LV V) w U) + 0x800000 = al_top (mkALayout (LV V) w U) /\ al_top (mkALayout (LV V) w U) mod 4096 = 0
  /\ ATOP + 0x800000 <= al_top (mkALayout (LV V) w U) <= ATOP + 0x800000 + 4096 /\ al_top (mkALayout (LV V) w U) <= 2^47.      (* [comment removed for export] *)
Proof.
  intros V w U HP HAT. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  unfold al_bot, al_top. rewrite LV_sp0.
  pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
  set (T := page_round_up_Z _) in *. clearbody T.
  apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
  split; [lia|]. split; [apply Z_mod_mult|]. split; lia.
Qed.

#[using="Type"] Theorem alayout_ok_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  tls_at V ->      (* [comment removed for export] *)
  alayout_ok (mkALayout (LV V) w U).
Proof.
  intros V w U HP HU HAT HTLS.
  pf V HP (PVar 0 4294901760 4294967295) Q0. pf V HP (PVar 6 0 255) Q6. pf V HP (PVar 10 0 7) Q10.
  constructor; rewrite ?LV_t, ?LV_ctx, ?LV_nodes, ?LV_store, ?LV_fake, ?LV_ptr_array, ?LV_space_beg; unfold al_res, al_dtls; cbn [al_V]; lv_lits.
  - (* [comment removed for export] *)
    pf V HP (PVar 227 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6238208) DI.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 228 1 34359736304) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 65536) 6238208) DIh228.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 469 1 34359736064) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6238208) DIh469.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 470 1 34359734272) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6238208) DIh470.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 393 1 34359733495) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6238208) DIh393.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 208 4295491576 34326181871) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 226 1 34359734272) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 65536) 6238208) DIh226.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 310 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6238208) DI.
    aobj_close.
  - (* [comment removed for export] *) pf V HP (PVar 208 4295491576 34326181871) P. lia.
  - (* [comment removed for export] *) pf V HP (PVar 209 0 15) P. lia.
  - (* [comment removed for export] *)
    pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) H4.
    pf V HP (PVar 209 0 15) P.
    change 65535 with (Z.ones 16) in H4. rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod MainExport.two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold MainExport.two64; lia]. destruct Hv as [q Hq]. unfold MainExport.two64 in Hq.
    replace (4096 * (V 208%nat - V 209%nat) + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536); [apply Z_mod_mult|].
    pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)). lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *)
    clear Q0 Q6 Q10. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    unfold al_bot, al_top. rewrite LV_sp0.
    pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
    set (T := page_round_up_Z _) in *. clearbody T.
    apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
    split; [lia|]. split; [apply Z_mod_mult|]. split; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *) exact HU.
  - (* [comment removed for export] *) (nd_pre HTLS 4%nat; intros HTP HKR HKT _; nd_post). rewrite HTP, HKR.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 65536) 6238208) D. pf V HP (PVar 208 4295491576 34326181871) P.
    destruct (6165744 <? 4096 * V 208%nat) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; clear - D P E; lia.
  - (* [comment removed for export] *) (nd_pre HTLS 4%nat; intros HTP HKR HKT _; nd_post). rewrite HTP, HKT.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6238208) D. pf V HP (PVar 227 1 34359736319) P.
    destruct (6165744 <? 4096 * V 227%nat) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; clear - D P E; lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. (nd_pre HTLS 4%nat; intros _ _ _ HA; nd_post). symmetry. exact HA.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits.
    pf V HP (PVar 207 1 34359735410) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 65536) 6238208) DIh207.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 208)) 137439023104) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 65536) 6238208) D. unfold adisj. clear - D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem awf_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V ->
  awf (mkALayout (LV V) w U) (ST0 V) X0.
Proof.
  intros V w U HP HU HAT HTLS. (pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  unfold awf. repeat match goal with |- _ /\ _ => split end.
  - unfold ST0, ainit, a_space_beg0, al_space_beg. cbn [a_space_beg al_V LV Nat.eqb]. lia.
  - reflexivity.
  - exact S3. - exact (proj1 S1). - exact S2.
  - intros c Hc. rewrite get_cls_ST0, max_count_ST0, busy_slots_X0, ndist_ST0. cbn.
    unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity;
      first [ apply Zmod_0_l | constructor | intros k [] ].
  - intros c _. apply get_cls_ST0.
  - intros b [].
  - intros p c n H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros p ch H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b1 b2 [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem ablocks_init : forall L st, ablocks L st X0 [].      (* [comment removed for export] *)
Proof.
  intros L st. split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem qcoupled_init : forall L V, qcoupled L (ST0 V) X0 qconc0.
Proof.
  intros L V. unfold qcoupled. cbn.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
  split; [intros k; split; [intros []| intros (b & [] & _)]|].
  split; [intros c k; split; [intros []| intros (b & [] & _)]|]. constructor.
Qed.

#[using="Type"] Theorem qnum_init : forall V, qnum (ST0 V).
Proof.
  intros V. unfold qnum. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition X0 : aconc := mkAConc (fun _ => mkXClass [] []) [].
(* [comment removed for export] *)
Definition ST0 (V : nat -> Z) : astate := ainit (a_space_beg0 V) (a_ptr_array0 V).

#[using="Type"] Lemma get_cls_ST0 : forall V c, get_cls (ST0 V) c = aclass0.
Proof. intros. apply get_cls_ainit. Qed.
#[using="Type"] Lemma max_count_ST0 : forall V c, max_count (ST0 V) c = 0.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma ndist_ST0 : forall V c, ndist (ST0 V) c = 0.
Proof. intros. unfold ndist. rewrite get_cls_ST0. cbn. apply Zdiv_0_l. Qed.
#[using="Type"] Lemma busy_of_X0 : forall c k, busy_of X0 c k = None.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma busy_slots_X0 : forall c, busy_slots X0 c = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_Z_bounds : forall x, x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x. unfold page_round_up_Z, page_size. split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Local Ltac aobj_close :=
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI;
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]; split; [lia|]; split; [lia|]; split; lia.

#[using="Type"] Theorem alayout_stack_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  al_bot (mkALayout (LV V) w U) + 0x800000 = al_top (mkALayout (LV V) w U) /\ al_top (mkALayout (LV V) w U) mod 4096 = 0
  /\ ATOP + 0x800000 <= al_top (mkALayout (LV V) w U) <= ATOP + 0x800000 + 4096 /\ al_top (mkALayout (LV V) w U) <= 2^47.      (* [comment removed for export] *)
Proof.
  intros V w U HP HAT. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  unfold al_bot, al_top. rewrite LV_sp0.
  pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
  set (T := page_round_up_Z _) in *. clearbody T.
  apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
  split; [lia|]. split; [apply Z_mod_mult|]. split; lia.
Qed.

#[using="Type"] Theorem alayout_ok_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP ->
  tls_at V ->      (* [comment removed for export] *)
  alayout_ok (mkALayout (LV V) w U).
Proof.
  intros V w U HP HU HAT HTLS.
  pf V HP (PVar 0 4294901760 4294967295) Q0. pf V HP (PVar 6 0 255) Q6. pf V HP (PVar 10 0 7) Q10.
  constructor; rewrite ?LV_t, ?LV_ctx, ?LV_nodes, ?LV_store, ?LV_fake, ?LV_ptr_array, ?LV_space_beg; unfold al_res, al_dtls; cbn [al_V]; lv_lits.
  - (* [comment removed for export] *)
    pf V HP (PVar 227 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6242304) DI.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 228 1 34359736304) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 65536) 6242304) DIh228.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 469 1 34359736064) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6242304) DIh469.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 470 1 34359734272) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6242304) DIh470.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 393 1 34359733495) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6242304) DIh393.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 208 4295491576 34326181871) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 226 1 34359734272) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 65536) 6242304) DIh226.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 310 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6242304) DI.
    aobj_close.
  - (* [comment removed for export] *) pf V HP (PVar 208 4295491576 34326181871) P. lia.
  - (* [comment removed for export] *) pf V HP (PVar 209 0 15) P. lia.
  - (* [comment removed for export] *)
    pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) H4.
    pf V HP (PVar 209 0 15) P.
    change 65535 with (Z.ones 16) in H4. rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod AS.MainExport.TwB.two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold AS.MainExport.TwB.two64; lia]. destruct Hv as [q Hq]. unfold AS.MainExport.TwB.two64 in Hq.
    replace (4096 * (V 208%nat - V 209%nat) + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536); [apply Z_mod_mult|].
    pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)). lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *)
    clear Q0 Q6 Q10. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    unfold al_bot, al_top. rewrite LV_sp0.
    pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
    set (T := page_round_up_Z _) in *. clearbody T.
    apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
    split; [lia|]. split; [apply Z_mod_mult|]. split; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *) exact HU.
  - (* [comment removed for export] *) (nd_pre HTLS 4%nat; intros HTP HKR HKT _; nd_post). rewrite HTP, HKR.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 65536) 6242304) D. pf V HP (PVar 208 4295491576 34326181871) P.
    destruct (6166768 <? 4096 * V 208%nat) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; clear - D P E; lia.
  - (* [comment removed for export] *) (nd_pre HTLS 4%nat; intros HTP HKR HKT _; nd_post). rewrite HTP, HKT.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6242304) D. pf V HP (PVar 227 1 34359736319) P.
    destruct (6166768 <? 4096 * V 227%nat) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; clear - D P E; lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 469)) 1048576 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 470)) 8388608 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 393)) 11571200 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. (nd_pre HTLS 4%nat; intros _ _ _ HA; nd_post). symmetry. exact HA.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits.
    pf V HP (PVar 207 1 34359735410) P. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 65536) 6242304) DIh207.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 469)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 470)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 393)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 208)) 137439023104) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) unfold al_ahm. cbn [al_V]; lv_lits. rewrite (proj1 HTLS). pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 65536) 6242304) D. unfold adisj. clear - D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem awf_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP -> tls_at V ->
  awf (mkALayout (LV V) w U) (ST0 V) X0.
Proof.
  intros V w U HP HU HAT HTLS. (pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  unfold awf. repeat match goal with |- _ /\ _ => split end.
  - unfold ST0, ainit, a_space_beg0, al_space_beg. cbn [a_space_beg al_V LV Nat.eqb]. lia.
  - reflexivity.
  - exact S3. - exact (proj1 S1). - exact S2.
  - intros c Hc. rewrite get_cls_ST0, max_count_ST0, busy_slots_X0, ndist_ST0. cbn.
    unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity;
      first [ apply Zmod_0_l | constructor | intros k [] ].
  - intros c _. apply get_cls_ST0.
  - intros b [].
  - intros p c n H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros p ch H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b1 b2 [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem ablocks_init : forall L st, ablocks L st X0 [].      (* [comment removed for export] *)
Proof.
  intros L st. split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem qcoupled_init : forall L V, qcoupled L (ST0 V) X0 qconc0.
Proof.
  intros L V. unfold qcoupled. cbn.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
  split; [intros k; split; [intros []| intros (b & [] & _)]|].
  split; [intros c k; split; [intros []| intros (b & [] & _)]|]. constructor.
Qed.

#[using="Type"] Theorem qnum_init : forall V, qnum (ST0 V).
Proof.
  intros V. unfold qnum. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
End TwB.
End ARepInit_A.

(* [comment removed for export] *)
Module ARepInit_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
  (* [comment removed for export] *)
  #[using="Type"] Lemma aia_zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N ->
    (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) ->
    zscanN s (S f) base n = true.
  Proof.
    intros s f. induction f as [|f IH]; intros base n Hn H.
    - cbn [zscanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
      destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
      unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
    - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
      remember (S f) as f1 eqn:Ef1. cbn [zscanN].
      destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1].
      + unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
      + rewrite N.div2_div. set (h := (n / 2)%N).
        assert (Hh : (2 * h <= n < 2 * h + 2)%N).
        { unfold h. pose proof (N.div_mod n 2 ltac:(discriminate)) as D. pose proof (N.mod_lt n 2 ltac:(discriminate)) as M.
          revert D M. generalize (n / 2)%N (n mod 2)%N. intros q r D M. lia. }
        clearbody h. subst f1. apply andb_true_intro. split.
        * apply IH; [lia|]. intros i Hi. apply H. lia.
        * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
  Qed.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Let L := mkALayout (LV V) w U.

  #[using="V HM"] Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xa4000 0xa7000 IMG. apply IMG. lia. Qed.

  (* [comment removed for export] *)
  #[using="V HM"] Lemma flags85_init : rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 0xabe48) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells asegs m 704072 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="V HM"] Lemma cflags34_init : rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)].
  Proof.
    mf8 V m HM 0x140148 128849084416 F.
    assert (F' : rw_cells asegs m 1311048 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="HM"] Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)] I1.
    aimg V m HM 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                          C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] I2.
    aimg V m HM 0xa54d0 [C8 (Z_to_bv 64 0xa7360)] I3.
    aimg V m HM 0xa6018 [C8 (Z_to_bv 64 0xaf2d9)] I4.
    aimg V m HM 0xa6108 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)] I6.
    aimg V m HM 0xaf2e8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x130860 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x130862 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x1400c0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    (* [comment removed for export] *)
    assert (I11 : rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)]).
    { aimg V m HM 6165960 [C4 (Z_to_bv 64 0)] K. replace (ATPv + 16) with 6165960 by (rewrite ATPv_img; reflexivity). exact K. }
    mf V m HM (MCell (ZLit 0xabdb8) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 0xabdc0) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 0xabdc2) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 0xabdc4) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 0xabdf8) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 0xabdfc) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 0xabe00) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 0xabe04) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 0xabe08) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 0xabe24) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 0xabe28) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells asegs m 704040 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 0xae5f8) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 0xade5c) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 0xade60) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 0xade64) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 0xaf2d8) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 0xaf2d9) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 0xaf2e0) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 0xaf2fc) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 0x130861) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 0x13e0a0) 8 (ZLit 4096)) F21.
    mf8 V m HM 0x140148 128849084416 F22.
    mf8 V m HM 0x1401a0 18446744073709551615 F23.      (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6165856) 8 (ZLit 6302048)) F24. replace 6165856 with (ATPv + -88) in F24 by (rewrite ATPv_img; reflexivity).
    mf V m HM (MCell (ZLit 0x602960) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)) F26.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))) F27.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|]. split; [exact I6|].
    split; [apply rw_cells_cons; [exact F1| apply rw_cells_cons; [exact F2| apply rw_cells_cons; [exact F3| exact F4]]]|].
    split; [apply rw_cells_cons; [exact F5| apply rw_cells_cons; [exact F6| apply rw_cells_cons; [exact F7| apply rw_cells_cons; [exact F8| exact F9]]]]|].
    split; [apply rw_cells_cons; [exact F10| exact F11']|].
    split; [exact flags85_init|].
    split; [exact F12|]. split; [exact F13|]. split; [exact F14|]. split; [exact F15|].
    split; [apply rw_cells_cons; [exact F16| exact F17]|].
    split; [apply rw_cells_cons; [exact F18| exact I7]|].
    split; [exact F19|].
    split; [apply rw_cells_cons; [exact I8| apply rw_cells_cons; [exact F20| exact I9]]|].
    split; [exact F21|]. split; [exact I10|]. split; [exact F22|]. split; [exact cflags34_init|]. split; [exact F23|].
    split; [exact F24|]. split; [exact F25|]. split; [exact I11|]. split; [exact F26| exact F27].
  Qed.

  #[using="V HM"] Theorem arep_rt2_init : arep_rt2 m.
  Proof.
    unfold arep_rt2.
    mf8 V m HM 0x140228 16843009 F1.
    assert (F1' : rw_cells asegs m 1311272 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf8 V m HM 0x1401b8 0 F2.
    aimg V m HM 0xa71d8 [C8 (Z_to_bv 64 0x9edb8)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  #[using="V HM"] Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0xa7238 [C8 (Z_to_bv 64 0x9dff0); C8 (Z_to_bv 64 0x9aee0)] I1.
    aimg V m HM 0xa7210 [C8 (Z_to_bv 64 0xa3ea8)] I2.
    aimg V m HM 0xa7220 [C8 (Z_to_bv 64 0x9abc8)] I3.
    aimg V m HM 0xa7308 [C8 (Z_to_bv 64 0x9eff4)] I4.
    aimg V m HM 0xa7200 [C8 (Z_to_bv 64 0x9e5a4)] I5.
    mf8 V m HM 0x140178 4294967296 F1.
    mf8 V m HM 0x140220 72340172838076673 F2.
    mf V m HM (MCell (ZLit 0xae600) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 0xabe58) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 0x13e098) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0xa5490 [C8 (Z_to_bv 64 0x13e0a0); C8 (Z_to_bv 64 0xa7398)] I6.
    aimg V m HM 0xa7398 [C8 (Z_to_bv 64 0x19361)] I7.
    mf V m HM (MCell (ZLit 0x13e0a0) 8 (ZLit 4096)) F6.
    mf8 V m HM 0x140200 1103823372544 F7.
    mf8 V m HM 0x140218 72339073309605888 F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 0x601878) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed.

  #[using="HM"] Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 0xaafb8) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 0xaafc8) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 0xaafd8) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 0xaafe0) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xab008 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 0xab240) 1 (ZLit 0)) F6.
    aimg V m HM 0xab370 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 0xaafc0) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells asegs m 700352 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 0xaafd0) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  (* [comment removed for export] *)
  #[using="V HM"] Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 0xab2b0) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 0xab2b8) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 0xab2c0) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 0xab308) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 0xab309) 1 (ZLit 0)) F5.
    aimg V m HM 0xab30a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  #[using="HM"] Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xab310 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma aia_scan : zscanN Asan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof.
    assert (ZW : zwin Asan_seg_bytes_003 (Uint63.of_Z 69632) (Uint63.of_Z 1056864) = true) by (vm_cast_no_check (eq_refl true)).
    assert (EB : Z.to_N (AIA_BASE - SEG3) = 34816%N) by (unfold AIA_BASE, SEG3; reflexivity).
    assert (ES : Z.to_N AIA_SIZE = 528432%N) by (unfold AIA_SIZE; reflexivity).
    rewrite EB, ES. apply aia_zscanN_complete; [change (2 ^ N.of_nat 63)%N with 9223372036854775808%N; lia|].
    intros i Hi. apply (zwin_hex_byte_at _ _ _ _ ZW).
    - vm_compute. intros HX. discriminate HX.
    - change (Uint63.to_Z (Uint63.of_Z 69632)) with 69632%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 69632)) with 69632%Z. change (Uint63.to_Z (Uint63.of_Z 1056864)) with 1056864%Z. lia.
  Qed.

  #[using="V HM"] Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x13e088 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xaf800 (0xaf800 + 0x81030) IMG. mwr V m HM (ZLit 671744) 5632000 W.      (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EQN : Z.of_N (Z.to_N AIA_SIZE) = AIA_SIZE) by (apply Z2N.id; unfold AIA_SIZE; lia).
    pose proof (img_zero_stk (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) m AIA_BASE aia_scan) as K. rewrite EQN in K.
    apply K.
    - unfold AIA_BASE, SEG3. reflexivity.
    - unfold AIA_BASE, AIA_SIZE. lia.
    - intros i Hi. apply IMG. unfold AIA_BASE, AIA_SIZE in Hi. lia.
    - eapply wr_at_sub; [exact W| unfold AIA_BASE; lia| unfold AIA_BASE; lia| unfold AIA_BASE, AIA_SIZE; lia].
  Qed.
End B.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  (* [comment removed for export] *)
  #[using="Type"] Lemma aia_zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N ->
    (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) ->
    zscanN s (S f) base n = true.
  Proof.
    intros s f. induction f as [|f IH]; intros base n Hn H.
    - cbn [zscanN]. change (2 ^ N.of_nat 0)%N with 1%N in Hn.
      destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1]; [|lia].
      unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
    - assert (P2 : (2 ^ N.of_nat (S f) = 2 * 2 ^ N.of_nat f)%N) by (rewrite Nat2N.inj_succ, N.pow_succ_r'; reflexivity).
      remember (S f) as f1 eqn:Ef1. cbn [zscanN].
      destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|].
      destruct (N.eqb_spec n 1) as [E1|N1].
      + unfold byte_zero. specialize (H 0%N ltac:(lia)). rewrite N.add_0_r in H. rewrite H. reflexivity.
      + rewrite N.div2_div. set (h := (n / 2)%N).
        assert (Hh : (2 * h <= n < 2 * h + 2)%N).
        { unfold h. pose proof (N.div_mod n 2 ltac:(discriminate)) as D. pose proof (N.mod_lt n 2 ltac:(discriminate)) as M.
          revert D M. generalize (n / 2)%N (n mod 2)%N. intros q r D M. lia. }
        clearbody h. subst f1. apply andb_true_intro. split.
        * apply IH; [lia|]. intros i Hi. apply H. lia.
        * apply IH; [lia|]. intros i Hi. replace (base + h + i)%N with (base + (h + i))%N by lia. apply H. lia.
  Qed.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Let L := mkALayout (LV V) w U.

  #[using="V HM"] Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xa5000 0xa7000 IMG. apply IMG. lia. Qed.

  (* [comment removed for export] *)
  #[using="V HM"] Lemma flags85_init : rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 0xac248) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells asegs m 705096 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="V HM"] Lemma cflags34_init : rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)].
  Proof.
    mf8 V m HM 0x140548 128849084416 F.
    assert (F' : rw_cells asegs m 1312072 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="HM"] Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)] I1.
    aimg V m HM 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                          C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] I2.
    aimg V m HM 0xa58b0 [C8 (Z_to_bv 64 0xa7740)] I3.
    aimg V m HM 0xa63f8 [C8 (Z_to_bv 64 0xaf6d9)] I4.
    aimg V m HM 0xa64e8 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)] I6.
    aimg V m HM 0xaf6e8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x130c60 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x130c62 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x1404c0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    (* [comment removed for export] *)
    assert (I11 : rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)]).
    { aimg V m HM 6166984 [C4 (Z_to_bv 64 0)] K. replace (ATPv + 16) with 6166984 by (rewrite ATPv_img; reflexivity). exact K. }
    mf V m HM (MCell (ZLit 0xac1b8) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 0xac1c0) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 0xac1c2) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 0xac1c4) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 0xac1f8) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 0xac1fc) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 0xac200) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 0xac204) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 0xac208) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 0xac224) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 0xac228) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells asegs m 705064 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 0xae9f8) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 0xae25c) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 0xae260) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 0xae264) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 0xaf6d8) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 0xaf6d9) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 0xaf6e0) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 0xaf6fc) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 0x130c61) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 0x13e4a0) 8 (ZLit 4096)) F21.
    mf8 V m HM 0x140548 128849084416 F22.
    mf8 V m HM 0x1405a0 18446744073709551615 F23.      (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6166880) 8 (ZLit 6303072)) F24. replace 6166880 with (ATPv + -88) in F24 by (rewrite ATPv_img; reflexivity).
    mf V m HM (MCell (ZLit 0x602d60) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)) F26.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))) F27.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|]. split; [exact I6|].
    split; [apply rw_cells_cons; [exact F1| apply rw_cells_cons; [exact F2| apply rw_cells_cons; [exact F3| exact F4]]]|].
    split; [apply rw_cells_cons; [exact F5| apply rw_cells_cons; [exact F6| apply rw_cells_cons; [exact F7| apply rw_cells_cons; [exact F8| exact F9]]]]|].
    split; [apply rw_cells_cons; [exact F10| exact F11']|].
    split; [exact flags85_init|].
    split; [exact F12|]. split; [exact F13|]. split; [exact F14|]. split; [exact F15|].
    split; [apply rw_cells_cons; [exact F16| exact F17]|].
    split; [apply rw_cells_cons; [exact F18| exact I7]|].
    split; [exact F19|].
    split; [apply rw_cells_cons; [exact I8| apply rw_cells_cons; [exact F20| exact I9]]|].
    split; [exact F21|]. split; [exact I10|]. split; [exact F22|]. split; [exact cflags34_init|]. split; [exact F23|].
    split; [exact F24|]. split; [exact F25|]. split; [exact I11|]. split; [exact F26| exact F27].
  Qed.

  #[using="V HM"] Theorem arep_rt2_init : arep_rt2 m.
  Proof.
    unfold arep_rt2.
    mf8 V m HM 0x140628 16843009 F1.
    assert (F1' : rw_cells asegs m 1312296 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf8 V m HM 0x1405b8 0 F2.
    aimg V m HM 0xa75b8 [C8 (Z_to_bv 64 0x9f19c)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  #[using="V HM"] Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0xa7618 [C8 (Z_to_bv 64 0x9e3d4); C8 (Z_to_bv 64 0x9b2c4)] I1.
    aimg V m HM 0xa75f0 [C8 (Z_to_bv 64 0xa428c)] I2.
    aimg V m HM 0xa7600 [C8 (Z_to_bv 64 0x9afac)] I3.
    aimg V m HM 0xa76e8 [C8 (Z_to_bv 64 0x9f3d8)] I4.
    aimg V m HM 0xa75e0 [C8 (Z_to_bv 64 0x9e988)] I5.
    mf8 V m HM 0x140578 4294967296 F1.
    mf8 V m HM 0x140620 72340172838076673 F2.
    mf V m HM (MCell (ZLit 0xaea00) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 0xac258) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 0x13e498) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0xa5870 [C8 (Z_to_bv 64 0x13e4a0); C8 (Z_to_bv 64 0xa7778)] I6.
    aimg V m HM 0xa7778 [C8 (Z_to_bv 64 0x19361)] I7.
    mf V m HM (MCell (ZLit 0x13e4a0) 8 (ZLit 4096)) F6.
    mf8 V m HM 0x140600 1103823372544 F7.
    mf8 V m HM 0x140618 72339073309605888 F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 0x601c78) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed.

  #[using="HM"] Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 0xab3b8) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 0xab3c8) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 0xab3d8) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 0xab3e0) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xab408 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 0xab640) 1 (ZLit 0)) F6.
    aimg V m HM 0xab770 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 0xab3c0) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells asegs m 701376 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 0xab3d0) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  (* [comment removed for export] *)
  #[using="V HM"] Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 0xab6b0) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 0xab6b8) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 0xab6c0) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 0xab708) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 0xab709) 1 (ZLit 0)) F5.
    aimg V m HM 0xab70a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  #[using="HM"] Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xab710 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof.
    assert (ZW : zwin AsanUbsan_seg_bytes_003 (Uint63.of_Z 71680) (Uint63.of_Z 1056864) = true) by (vm_cast_no_check (eq_refl true)).
    assert (EB : Z.to_N (AIA_BASE - SEG3) = 35840%N) by (unfold AIA_BASE, SEG3; reflexivity).
    assert (ES : Z.to_N AIA_SIZE = 528432%N) by (unfold AIA_SIZE; reflexivity).
    rewrite EB, ES. apply aia_zscanN_complete; [change (2 ^ N.of_nat 63)%N with 9223372036854775808%N; lia|].
    intros i Hi. apply (zwin_hex_byte_at _ _ _ _ ZW).
    - vm_compute. intros HX. discriminate HX.
    - change (Uint63.to_Z (Uint63.of_Z 71680)) with 71680%Z. lia.
    - change (Uint63.to_Z (Uint63.of_Z 71680)) with 71680%Z. change (Uint63.to_Z (Uint63.of_Z 1056864)) with 1056864%Z. lia.
  Qed.

  #[using="V HM"] Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x13e488 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xafc00 (0xafc00 + 0x81030) IMG. mwr V m HM (ZLit 675840) 5632000 W.      (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (EQN : Z.of_N (Z.to_N AIA_SIZE) = AIA_SIZE) by (apply Z2N.id; unfold AIA_SIZE; lia).
    pose proof (img_zero_stk (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) m AIA_BASE aia_scan) as K. rewrite EQN in K.
    apply K.
    - unfold AIA_BASE, SEG3. reflexivity.
    - unfold AIA_BASE, AIA_SIZE. lia.
    - intros i Hi. apply IMG. unfold AIA_BASE, AIA_SIZE in Hi. lia.
    - eapply wr_at_sub; [exact W| unfold AIA_BASE; lia| unfold AIA_BASE; lia| unfold AIA_BASE, AIA_SIZE; lia].
  Qed.
End B.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End ARepInit_B.

(* [comment removed for export] *)
Module ARepInit_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section E.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z) (w : bool) (U : list (list Z)).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  Let RNG := fp_ok lz AL.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
    shad (al_space_beg L) <= bv_unsigned p < shad (al_space_beg L) + 17179869184 -> AL p.

  #[using="rc U HU"] Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
  Qed.

  #[using="rc U A0I HU"] Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  #[using="Type"] Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
  Proof.
    intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  #[using="rc U A0I HU"] Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng RNG lo len.
  Proof. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  #[using="rc U A0I HU"] Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)); [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  #[using="rc U HU"] Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng RNG b 0.
  Proof. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.

  (* [comment removed for export] *)
  #[using="U A0I HU"] Lemma obj_rng : forall k a n, nth_error asan_vis k = Some (ZMul (ZLit 4096) (ZV a), ZLit n) ->     (* [comment removed for export] *)
    4096 <= 4096 * V a -> 4096 * V a + n <= ATOP -> rng RNG (4096 * V a) n.
  Proof. intros k a n Hk H1 H2. atop_facts. eapply (vis_rng k); [exact Hk| cbn; lia| cbn; lia| lia| lia]. Qed.

  #[using="A0I HP HU HAT HTLS ASH0"] Theorem arng_init : arng L RNG (ST0 V).
  Proof.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_t _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ T1 T2 _; nd_post). (pose proof (ao_ctx _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ C1 C2 _; nd_post). (pose proof (ao_nodes _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ N1 N2 _; nd_post).
    (pose proof (ao_store _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ S1 S2 _; nd_post). (pose proof (ao_fake _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ F1 F2 _; nd_post). (pose proof (ao_dtls _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ D1 D2 _; nd_post).
    (pose proof (alayout_space _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros B1 B2 B3 B4; nd_post). (pose proof (ao_ptr _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ P1 P2 _; nd_post).
    revert T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array, K_SPACE_SIZE, K_SPACE_EXTRA. cbn [al_V]; lv_lits.
    intros T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold L in *.
    assert (ESB : al_space_beg (mkALayout (LV V) w U) = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (rewrite LV_space_beg; lia).
    rewrite ?ESB in B1, B2, B3, B4.
    unfold arng, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array. cbn [al_V]; lv_lits. rewrite ESB.
    split; [eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia]|].
    split; [eapply (obj_rng 8); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 7); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 3); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 2); [reflexivity| lia| atop_facts; lia]|].
    split.
    { unfold K_SPACE_SIZE, K_SPACE_EXTRA. eapply (vis_rng 9); [reflexivity| | | lia| lia];
        cbn [fst snd zv nth_error asan_vis asan_vis_app app]; lia. }
    split; [eapply (obj_rng 4); [reflexivity| lia| atop_facts; lia]|].
    split.
    { rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 4); [reflexivity| | | |]; cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia. }
    split; [eapply (obj_rng 5); [reflexivity| lia| atop_facts; lia]|].
    split.
    { intros c Hc. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. change (shlen 0) with 0.
      unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      repeat split; apply rng_empty; rewrite ?shad_div; unfold AsanEmbed.ASHOFF; try (Z.div_mod_to_equations; lia); lia. }
    (* [comment removed for export] *)
    split.
    { cbn [a_nres ST0 ainit]. change (8 * 0) with 0. apply rng_empty. change (al_V L 239%nat) with (V 226%nat). atop_facts. lia. }
    split. { unfold RSEC, sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob ST0 ainit app flat_map]. rewrite map_to_list_empty. constructor. }
    (* [comment removed for export] *)
    assert (SBA : shad (al_space_beg L) mod 4096 = 0 /\ 0 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869184 <= 2^64).
    { unfold L. rewrite shad_div, ESB. unfold AsanEmbed.ASHOFF in *. clear -B1 B2 B3. unfold K_ALIGN in B3. Z.div_mod_to_equations. lia. }
    unfold L in SBA.
    (nd_pre SBA 3%nat; intros SBA SB0 SB1; nd_post). rewrite <- ESB. replace (shlen K_SPACE_SIZE) with 17179869184 by reflexivity.
    split.
    { apply rng_fp_ok_allowed; [exact SB0| exact SB1|].
      intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV. apply ASH0; rewrite PV; [clear -Hz; Z.div_mod_to_equations; lia|].
      clear -Hz SBA. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    rewrite (proj1 HTLS).
    eapply (vis_rng 12); [reflexivity | cbn [fst snd zv]; clear; lia | cbn [fst snd zv]; clear; lia | clear; lia | clear; lia].
  Qed.
End E.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lv_lit k := let b := eval lazy [Nat.eqb] in (Nat.eqb k k) in constr_eq b true.
Local Ltac lv_lits := repeat match goal with |- context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v end.
Local Ltac lv_lits_in H := repeat match type of H with context [LV ?V ?k] => lv_lit k; let v := eval lazy [LV Nat.eqb] in (LV V k) in change (LV V k) with v in H end.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
  let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section E.
  Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z) (w : bool) (U : list (list Z)).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.
  Let RNG := fp_ok lz AL.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
    shad (al_space_beg L) <= bv_unsigned p < shad (al_space_beg L) + 17179869184 -> AL p.

  #[using="rc U HU"] Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
  Proof.
    intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
    unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
  Qed.

  #[using="rc U A0I HU"] Lemma vis_rng_gen : forall b n lo len,
    In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
    b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros b n lo len HIN H1 H2 H3 H4. apply rng_fp_ok_allowed; [lia| lia|].
    intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
    apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
    exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
    Z.div_mod_to_equations. nia.
  Qed.

  #[using="Type"] Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->      (* [comment removed for export] *)
    In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
    /\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
  Proof.
    intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
  Qed.

  #[using="rc U A0I HU"] Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
    zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng RNG lo len.
  Proof. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.

  #[using="rc U A0I HU"] Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
    2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
    rng RNG lo len.
  Proof.
    intros k bn lo len Hk H1 H2 H3 H4.
    eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)); [| lia| lia| lia| lia].
    replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
    exact (proj2 (allow_in_app k bn Hk)).
  Qed.

  #[using="rc U HU"] Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng RNG b 0.
  Proof. intros b Hb. apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed.

  (* [comment removed for export] *)
  #[using="U A0I HU"] Lemma obj_rng : forall k a n, nth_error asan_vis k = Some (ZMul (ZLit 4096) (ZV a), ZLit n) ->     (* [comment removed for export] *)
    4096 <= 4096 * V a -> 4096 * V a + n <= ATOP -> rng RNG (4096 * V a) n.
  Proof. intros k a n Hk H1 H2. atop_facts. eapply (vis_rng k); [exact Hk| cbn; lia| cbn; lia| lia| lia]. Qed.

  #[using="A0I HP HU HAT HTLS ASH0"] Theorem arng_init : arng L RNG (ST0 V).
  Proof.
    pose proof (alayout_ok_init V w U HP HU HAT HTLS) as ALO.
    (pose proof (ao_t _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ T1 T2 _; nd_post). (pose proof (ao_ctx _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ C1 C2 _; nd_post). (pose proof (ao_nodes _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ N1 N2 _; nd_post).
    (pose proof (ao_store _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ S1 S2 _; nd_post). (pose proof (ao_fake _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ F1 F2 _; nd_post). (pose proof (ao_dtls _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ D1 D2 _; nd_post).
    (pose proof (alayout_space _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros B1 B2 B3 B4; nd_post). (pose proof (ao_ptr _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ P1 P2 _; nd_post).
    revert T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array, K_SPACE_SIZE, K_SPACE_EXTRA. cbn [al_V]; lv_lits.
    intros T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
    unfold L in *.
    assert (ESB : al_space_beg (mkALayout (LV V) w U) = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (rewrite LV_space_beg; lia).
    rewrite ?ESB in B1, B2, B3, B4.
    unfold arng, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array. cbn [al_V]; lv_lits. rewrite ESB.
    split; [eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia]|].
    split; [eapply (obj_rng 8); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 7); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 3); [reflexivity| lia| atop_facts; lia]|].
    split; [eapply (obj_rng 2); [reflexivity| lia| atop_facts; lia]|].
    split.
    { unfold K_SPACE_SIZE, K_SPACE_EXTRA. eapply (vis_rng 9); [reflexivity| | | lia| lia];
        cbn [fst snd zv nth_error asan_vis asan_vis_app app]; lia. }
    split; [eapply (obj_rng 4); [reflexivity| lia| atop_facts; lia]|].
    split.
    { rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      eapply (vis_rng_sh 4); [reflexivity| | | |]; cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia. }
    split; [eapply (obj_rng 5); [reflexivity| lia| atop_facts; lia]|].
    split.
    { intros c Hc. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. change (shlen 0) with 0.
      unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      repeat split; apply rng_empty; rewrite ?shad_div; unfold AsanEmbed.ASHOFF; try (Z.div_mod_to_equations; lia); lia. }
    (* [comment removed for export] *)
    split.
    { cbn [a_nres ST0 ainit]. change (8 * 0) with 0. apply rng_empty. change (al_V L 239%nat) with (V 226%nat). atop_facts. lia. }
    split. { unfold RSEC, sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob ST0 ainit app flat_map]. rewrite map_to_list_empty. constructor. }
    (* [comment removed for export] *)
    assert (SBA : shad (al_space_beg L) mod 4096 = 0 /\ 0 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869184 <= 2^64).
    { unfold L. rewrite shad_div, ESB. unfold AsanEmbed.ASHOFF in *. clear -B1 B2 B3. unfold K_ALIGN in B3. Z.div_mod_to_equations. lia. }
    unfold L in SBA.
    (nd_pre SBA 3%nat; intros SBA SB0 SB1; nd_post). rewrite <- ESB. replace (shlen K_SPACE_SIZE) with 17179869184 by reflexivity.
    split.
    { apply rng_fp_ok_allowed; [exact SB0| exact SB1|].
      intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV. apply ASH0; rewrite PV; [clear -Hz; Z.div_mod_to_equations; lia|].
      clear -Hz SBA. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    rewrite (proj1 HTLS).
    eapply (vis_rng 12); [reflexivity | cbn [fst snd zv]; clear; lia | cbn [fst snd zv]; clear; lia | clear; lia | clear; lia].
  Qed.
End E.
End CANSEC1.
End TwB.
End ARepInit_E.

(* [comment removed for export] *)
Module ARepInit_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section C.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.

  (* [comment removed for export] *)
  #[using="rc HP HU"] Lemma top_eq : al_top L = 32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat.
  Proof.
    pf V HP (PVar 344 0 1) P344. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 0 4294901760 4294967295) P0.
    pf V HP (PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095) R.
    unfold two64 in R.
    assert (R' : 0 <= 16 * V 6%nat + -4096 * V 344%nat + 3935 <= 4095).
    { destruct (Z.lt_ge_cases (16 * V 6%nat + -4096 * V 344%nat + 3935) 0) as [NEG|NN].
      - exfalso. rewrite <- (Z.mod_add _ 1) in R by lia. rewrite Z.mod_small in R by lia. lia.
      - rewrite Z.mod_small in R by lia. exact R. }
    unfold al_top, L. rewrite LV_sp0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia.
  Qed.

  #[using="Type"] Lemma t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ctx_eq : al_ctx L = 4096 * V 228%nat. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="rc HM HU"] Lemma t_zero : forall i, 80 <= i < 3168 -> m (wa (al_t L + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
    rewrite t_eq. replace (4096 * V 227%nat + i) with (4096 * V 227%nat + 80 + (i - 80)) by lia. apply ZR. lia.
  Qed.
  #[using="HM"] Lemma t_wr : wr_at asegs m (al_t L) 4096.
  Proof. mwr V m HM (ZMul (ZLit 4096) (ZV 227)) 4096 W. rewrite t_eq. exact W. Qed.
  #[using="tlsI HP HU HAT HTLS"] Lemma t_pos : 4096 <= al_t L /\ al_t L + 4096 <= ATOP.     (* [comment removed for export] *)
  Proof. (pose proof (ao_t _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 4%nat; intros _ A B _; nd_post). exact (conj A B). Qed.

  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem athread_init : athread L (ST0 V) X0 m.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold athread. split.
    { mf V m HM (MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))) F0.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))) F8.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))) F16.
      unfold al_bot. rewrite top_eq, t_eq.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat) in F8 by lia.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat - 8388608) in F16 by lia.
      apply rw_cells_cons; [exact F0|]. apply rw_cells_cons; [exact F8|].
      replace (4096 * V 227%nat + Z.of_nat (csize (C8 (Z_to_bv 64 (al_ctx L)))) + Z.of_nat (csize (C8 (Z_to_bv 64 (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat)))))
        with (4096 * V 227%nat + 16) by (cbn; lia).
      exact F16. }
    split.
    { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)) F40. rewrite t_eq. exact F40. }
    split.
    { intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_ST0, max_count_ST0. cbn [c_count aclass0 a_cinit ST0 ainit x_cls X0 xc_cache app length map].
      exists (repeat (Z_to_bv 64 0) 16). unfold K_NUM_CLASSES in Hc.
      split; [| split; [| rewrite repeat_length; reflexivity]].
      - apply zcells; [reflexivity| |].
        + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 208 + c * 80 + i) with (al_t L + (208 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
      - apply u32arr_zero.
        + intros i Hi. cbn in Hi. replace (al_t L + 208 + c * 80 + 16 + i) with (al_t L + (224 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 8 0) 32). apply zcells; [reflexivity| |].
      + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 2768 + i) with (al_t L + (2768 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 64 0) 46). split; [| rewrite repeat_length; reflexivity]. apply u64arr_zero.
      + intros i Hi. cbn in Hi. replace (al_t L + 2800 + i) with (al_t L + (2800 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)) F3168. rewrite t_eq. exact F3168.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem aqcache_loc_init : aqcache L m (aq_tcache L) [] [] 0.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold aqcache, aq_tcache. split; [| exact I].
    apply zcells; [reflexivity| |].
    - cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 80 + i) with (al_t L + (80 + i)) by lia. apply t_zero. lia.
    - eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
  Qed.
End C.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section C.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.

  (* [comment removed for export] *)
  #[using="rc HP HU"] Lemma top_eq : al_top L = 32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat.
  Proof.
    pf V HP (PVar 344 0 1) P344. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 0 4294901760 4294967295) P0.
    pf V HP (PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095) R.
    unfold two64 in R.
    assert (R' : 0 <= 16 * V 6%nat + -4096 * V 344%nat + 3935 <= 4095).
    { destruct (Z.lt_ge_cases (16 * V 6%nat + -4096 * V 344%nat + 3935) 0) as [NEG|NN].
      - exfalso. rewrite <- (Z.mod_add _ 1) in R by lia. rewrite Z.mod_small in R by lia. lia.
      - rewrite Z.mod_small in R by lia. exact R. }
    unfold al_top, L. rewrite LV_sp0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia.
  Qed.

  #[using="Type"] Lemma t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ctx_eq : al_ctx L = 4096 * V 228%nat. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="rc HM HU"] Lemma t_zero : forall i, 80 <= i < 3168 -> m (wa (al_t L + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
    rewrite t_eq. replace (4096 * V 227%nat + i) with (4096 * V 227%nat + 80 + (i - 80)) by lia. apply ZR. lia.
  Qed.
  #[using="HM"] Lemma t_wr : wr_at asegs m (al_t L) 4096.
  Proof. mwr V m HM (ZMul (ZLit 4096) (ZV 227)) 4096 W. rewrite t_eq. exact W. Qed.
  #[using="tlsI HP HU HAT HTLS"] Lemma t_pos : 4096 <= al_t L /\ al_t L + 4096 <= ATOP.     (* [comment removed for export] *)
  Proof. (pose proof (ao_t _ (alayout_ok_init V w U HP HU HAT HTLS)) as ndP__; nd_pre ndP__ 4%nat; intros _ A B _; nd_post). exact (conj A B). Qed.

  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem athread_init : athread L (ST0 V) X0 m.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold athread. split.
    { mf V m HM (MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))) F0.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))) F8.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))) F16.
      unfold al_bot. rewrite top_eq, t_eq.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat) in F8 by lia.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat - 8388608) in F16 by lia.
      apply rw_cells_cons; [exact F0|]. apply rw_cells_cons; [exact F8|].
      replace (4096 * V 227%nat + Z.of_nat (csize (C8 (Z_to_bv 64 (al_ctx L)))) + Z.of_nat (csize (C8 (Z_to_bv 64 (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat)))))
        with (4096 * V 227%nat + 16) by (cbn; lia).
      exact F16. }
    split.
    { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)) F40. rewrite t_eq. exact F40. }
    split.
    { intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_ST0, max_count_ST0. cbn [c_count aclass0 a_cinit ST0 ainit x_cls X0 xc_cache app length map].
      exists (repeat (Z_to_bv 64 0) 16). unfold K_NUM_CLASSES in Hc.
      split; [| split; [| rewrite repeat_length; reflexivity]].
      - apply zcells; [reflexivity| |].
        + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 208 + c * 80 + i) with (al_t L + (208 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
      - apply u32arr_zero.
        + intros i Hi. cbn in Hi. replace (al_t L + 208 + c * 80 + 16 + i) with (al_t L + (224 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 8 0) 32). apply zcells; [reflexivity| |].
      + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 2768 + i) with (al_t L + (2768 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 64 0) 46). split; [| rewrite repeat_length; reflexivity]. apply u64arr_zero.
      + intros i Hi. cbn in Hi. replace (al_t L + 2800 + i) with (al_t L + (2800 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)) F3168. rewrite t_eq. exact F3168.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem aqcache_loc_init : aqcache L m (aq_tcache L) [] [] 0.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold aqcache, aq_tcache. split; [| exact I].
    apply zcells; [reflexivity| |].
    - cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 80 + i) with (al_t L + (80 + i)) by lia. apply t_zero. lia.
    - eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
  Qed.
End C.
End CANSEC1.
End TwB.
End ARepInit_C.

(* [comment removed for export] *)
Module ARepInit_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AHandoffDefs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section D.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Let L := mkALayout (LV V) w U.

  #[using="rc HU"] Lemma sb_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
  Proof. unfold al_space_beg. cbn [al_V L LV Nat.eqb]. lia. Qed.
  #[using="rc HU"] Lemma sb_eq' : aspace_beg V = al_space_beg L.
  Proof. unfold aspace_beg. rewrite sb_eq. lia. Qed.
  #[using="tlsI HP HU HAT HTLS"] Lemma sb_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
                   /\ 0 <= al_space_beg L < 2^47.
  Proof. (nd_pre (alayout_space _ (alayout_ok_init V w U HP HU HAT HTLS)) 4%nat; intros (S1 & _) S2 S3 S4; nd_post). exact (conj S1 (conj S2 (conj S3 S4))). Qed.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="rc HM HU"] Lemma ri_zero : forall i, 0 <= i < 4096 -> m (wa (al_space_beg L + K_SPACE_SIZE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37 + i)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008 + i) by lia. apply ZR. lia.
  Qed.
  #[using="rc HM HU"] Lemma ri_wr : wr_at asegs m (al_space_beg L + K_SPACE_SIZE) 4096.
  Proof.
    mwr V m HM (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096 W.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact W.
  Qed.

  Ltac ri_cells c Hc :=
    apply zcells; [reflexivity
      | cbn [cells_size csize Nat.add]; intros i Hi; unfold aregion_info, ARI_STRIDE;
        match goal with |- m (wa ?x) = _ => replace x with (al_space_beg L + K_SPACE_SIZE + (x - (al_space_beg L + K_SPACE_SIZE))) by lia end;
        apply ri_zero; lia
      | unfold aregion_info, ARI_STRIDE; eapply wr_at_sub; [exact ri_wr| unfold K_SPACE_SIZE; lia| lia| cbn; lia] ].

  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem aregion_cells_init : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aregion_cells. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
    split; [ri_cells c Hc|]. split; [ri_cells c Hc|].
    split; [exists (repeat (Z_to_bv 8 0) 4); ri_cells c Hc|].
    split; [ri_cells c Hc|]. exists (repeat (Z_to_bv 8 0) 56); ri_cells c Hc.
  Qed.

  (* [comment removed for export] *)
  #[using="rc U HU"] Lemma shad_add : forall a k, a mod 8 = 0 -> shad (a + k) = shad a + k / 8.
  Proof. intros a k Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.
  #[using="rc U HU"] Lemma shlen_eq : forall n, shlen n = n / 8.
  Proof. intros n. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem afreearray_init : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold afreearray. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free map].
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    split; [apply u32arr_nil; lia|]. split.
    - exists []. rewrite Z.add_0_r. change (Z.to_nat (0 - 4 * 0)) with 0%nat. apply rw_cells_CB0; lia.
    - exists []. change (Z.to_nat (shlen 0)) with 0%nat. apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem aslots_init : forall c, 1 <= c < K_NUM_CLASSES -> aslots L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslots. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    exists []. unfold aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (0 - 0)) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem aslot_shadow_init : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslot_shadow. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    unfold fill_at, aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (shlen (0 - 0))) with 0%nat. cbn [repeat].
    apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI HP HU HAT HTLS SH0"] Theorem ashadow_avail_init : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    destruct (primary_shadow0 V m SH0 HP) as [Z0' W0]. rewrite sb_eq' in Z0', W0.
    assert (A8 : al_space_beg L mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
    unfold ashadow_avail. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite !Z.add_0_r, !Z.sub_0_r.
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX. change (2^32) with 4294967296.
    replace (shad (al_space_beg L + c * 4294967296 + 3758096384)) with (shad (al_space_beg L) + (c * 536870912 + 469762048))
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    replace (shad (al_space_beg L + c * 4294967296)) with (shad (al_space_beg L) + c * 536870912)
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    rewrite !shlen_eq. change (3758096384 / 8) with 469762048. change (536870912 / 8) with 67108864.
    split; split.
    - intros i Hi. replace (shad (al_space_beg L) + c * 536870912 + i) with (shad (al_space_beg L) + (c * 536870912 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
    - intros i Hi. replace (shad (al_space_beg L) + (c * 536870912 + 469762048) + i) with (shad (al_space_beg L) + (c * 536870912 + 469762048 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
  Qed.
End D.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section D.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis HTLS : tls_at V.      (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Let L := mkALayout (LV V) w U.

  #[using="rc HU"] Lemma sb_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
  Proof. unfold al_space_beg. cbn [al_V L LV Nat.eqb]. lia. Qed.
  #[using="rc HU"] Lemma sb_eq' : aspace_beg V = al_space_beg L.
  Proof. unfold aspace_beg. rewrite sb_eq. lia. Qed.
  #[using="tlsI HP HU HAT HTLS"] Lemma sb_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
                   /\ 0 <= al_space_beg L < 2^47.
  Proof. (nd_pre (alayout_space _ (alayout_ok_init V w U HP HU HAT HTLS)) 4%nat; intros (S1 & _) S2 S3 S4; nd_post). exact (conj S1 (conj S2 (conj S3 S4))). Qed.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="rc HM HU"] Lemma ri_zero : forall i, 0 <= i < 4096 -> m (wa (al_space_beg L + K_SPACE_SIZE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37 + i)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008 + i) by lia. apply ZR. lia.
  Qed.
  #[using="rc HM HU"] Lemma ri_wr : wr_at asegs m (al_space_beg L + K_SPACE_SIZE) 4096.
  Proof.
    mwr V m HM (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096 W.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact W.
  Qed.

  Ltac ri_cells c Hc :=
    apply zcells; [reflexivity
      | cbn [cells_size csize Nat.add]; intros i Hi; unfold aregion_info, ARI_STRIDE;
        match goal with |- m (wa ?x) = _ => replace x with (al_space_beg L + K_SPACE_SIZE + (x - (al_space_beg L + K_SPACE_SIZE))) by lia end;
        apply ri_zero; lia
      | unfold aregion_info, ARI_STRIDE; eapply wr_at_sub; [exact ri_wr| unfold K_SPACE_SIZE; lia| lia| cbn; lia] ].

  #[using="rc tlsI HM HP HU HAT HTLS"] Theorem aregion_cells_init : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aregion_cells. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
    split; [ri_cells c Hc|]. split; [ri_cells c Hc|].
    split; [exists (repeat (Z_to_bv 8 0) 4); ri_cells c Hc|].
    split; [ri_cells c Hc|]. exists (repeat (Z_to_bv 8 0) 56); ri_cells c Hc.
  Qed.

  (* [comment removed for export] *)
  #[using="rc U HU"] Lemma shad_add : forall a k, a mod 8 = 0 -> shad (a + k) = shad a + k / 8.
  Proof. intros a k Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.
  #[using="rc U HU"] Lemma shlen_eq : forall n, shlen n = n / 8.
  Proof. intros n. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem afreearray_init : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold afreearray. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free map].
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    split; [apply u32arr_nil; lia|]. split.
    - exists []. rewrite Z.add_0_r. change (Z.to_nat (0 - 4 * 0)) with 0%nat. apply rw_cells_CB0; lia.
    - exists []. change (Z.to_nat (shlen 0)) with 0%nat. apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem aslots_init : forall c, 1 <= c < K_NUM_CLASSES -> aslots L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslots. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    exists []. unfold aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (0 - 0)) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  #[using="rc tlsI HP HU HAT HTLS"] Theorem aslot_shadow_init : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslot_shadow. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    unfold fill_at, aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (shlen (0 - 0))) with 0%nat. cbn [repeat].
    apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI HP HU HAT HTLS SH0"] Theorem ashadow_avail_init : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. (pose proof sb_facts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    destruct (primary_shadow0 V m SH0 HP) as [Z0' W0]. rewrite sb_eq' in Z0', W0.
    assert (A8 : al_space_beg L mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
    unfold ashadow_avail. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite !Z.add_0_r, !Z.sub_0_r.
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX. change (2^32) with 4294967296.
    replace (shad (al_space_beg L + c * 4294967296 + 3758096384)) with (shad (al_space_beg L) + (c * 536870912 + 469762048))
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    replace (shad (al_space_beg L + c * 4294967296)) with (shad (al_space_beg L) + c * 536870912)
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    rewrite !shlen_eq. change (3758096384 / 8) with 469762048. change (536870912 / 8) with 67108864.
    split; split.
    - intros i Hi. replace (shad (al_space_beg L) + c * 536870912 + i) with (shad (al_space_beg L) + (c * 536870912 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
    - intros i Hi. replace (shad (al_space_beg L) + (c * 536870912 + 469762048) + i) with (shad (al_space_beg L) + (c * 536870912 + 469762048 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
  Qed.
End D.
End CANSEC1.
End TwB.
End ARepInit_D.
