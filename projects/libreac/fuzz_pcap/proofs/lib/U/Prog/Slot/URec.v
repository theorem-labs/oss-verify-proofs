From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv UCut USROcf.
Import ListNotations.
Open Scope Z_scope.

(* The walk's loop: from K4 at index i and position p, every run outputs the rest of the walk and the call after the
   reopen, by induction on the file bytes left after p. *)

Lemma uwalk_unfold : forall g p, 0 <= p -> uwalk g p ++ uC0 g = uout1 g p ++ uafter g p.
Proof.
  intros g p Hp. unfold uwalk, uafter, uout1, ukind, upos, uQ.
  rewrite (PW.walk_unfold_len (usw g) (uF g) (ucap g) p Hp). rewrite <- app_assoc. reflexivity.
Qed.

(* The next position after a fit record lies past p and inside the file. *)
Lemma upos_fit : forall g p, 0 <= p -> ukind g (uQ g p) = PN.KFit ->
  p < upos g (uQ g p) <= un g.
Proof.
  intros g p Hp K. unfold ukind, upos, uQ, un, zlen in *.
  destruct (PW.kind_fit (usw g) (uF g) (ucap g) _ K) as (_ & _ & EP & HE & HI).
  pose proof (PW.psn_q_ge (usw g) (uF g) (ucap g) p) as HQ.
  rewrite EP. unfold PN.flen in HE. lia.
Qed.

Section Rec.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition HC4 (g : ghost) (i p : Z) : Prop :=
  forall c, Inv_K4 B APIf ra empty g i p c ->
    SRO (ms_segs B) c (uwalk g (upos g (uQ g p)) ++ uC0 g) (Post_o B APIf ra g).
Definition HC6 (g : ghost) (i p : Z) : Prop :=
  forall c, Inv_K1306c B APIf ra empty g i p c -> SRO (ms_segs B) c (uafter g p) (Post_o B APIf ra g).
Definition HC5 (g : ghost) (p : Z) : Prop :=
  forall c, Inv_K5 B APIf ra empty g p c -> SRO (ms_segs B) c (uC0 g) (Post_o B APIf ra g).

(* L: from K4 (i, p) through the record checks and the next call (from upos of the record) to 0x13034. *)
Hypothesis HL : forall g i p, HC6 g (i + 1) (upos g (uQ g p)) ->
  forall c, Inv_K4 B APIf ra empty g i p c ->
    SRO (ms_segs B) c (uout1 g (upos g (uQ g p)) ++ uafter g (upos g (uQ g p))) (Post_o B APIf ra g).
(* L2: from 0x13034 to K4 or K5. *)
Hypothesis HL2 : forall g i p, HC4 g i p -> HC5 g p -> HC6 g i p.
Hypothesis H5 : forall g p, HC5 g p.

Lemma uk4_fuel : forall g k i p, (Z.to_nat (un g - p) < k)%nat -> HC4 g i p.
Proof.
  intros g k. induction k as [|k IH]; intros i p Hk; [lia|].
  intros c HK.
  pose proof HK as (b & h & buf & a3 & Hgood & fx' & L & A & regs & mem & md & Ec & Hfrm & HF & HP & HPr).
  destruct HPr as (_ & _ & Hi & Hp & K & _).
  destruct (upos_fit g p ltac:(lia) K) as (H1 & H2).
  set (p1 := upos g (uQ g p)) in *.
  rewrite (uwalk_unfold g p1 ltac:(lia)).
  apply (HL g i p); [|exact HK].
  apply HL2; [apply IH; lia | apply H5].
Qed.

Lemma uk4_all : forall g i p, HC4 g i p.
Proof. intros g i p. apply (uk4_fuel g (S (Z.to_nat (un g - p))) i p). lia. Qed.

(* The cut-free twin (SROcf; the cut statements in the PInvCF.Hcut_cf form, with the slot's cap bound
   sb_cap (g_b g) <= CAP_AG as a premise). *)
Definition HC4_cf (g : ghost) (i p : Z) : Prop :=
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K4 B APIf ra empty g i p c ->
    SROcf (ms_segs B) c (uwalk g (upos g (uQ g p)) ++ uC0 g) (Post_o B APIf ra g).
Definition HC6_cf (g : ghost) (i p : Z) : Prop :=
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K1306c B APIf ra empty g i p c ->
    SROcf (ms_segs B) c (uafter g p) (Post_o B APIf ra g).
Definition HC5_cf (g : ghost) (p : Z) : Prop :=
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K5 B APIf ra empty g p c ->
    SROcf (ms_segs B) c (uC0 g) (Post_o B APIf ra g).

Hypothesis HL_cf : forall g i p, HC6_cf g (i + 1) (upos g (uQ g p)) ->
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K4 B APIf ra empty g i p c ->
    SROcf (ms_segs B) c (uout1 g (upos g (uQ g p)) ++ uafter g (upos g (uQ g p))) (Post_o B APIf ra g).
Hypothesis HL2_cf : forall g i p, HC4_cf g i p -> HC5_cf g p -> HC6_cf g i p.
Hypothesis H5_cf : forall g p, HC5_cf g p.

Lemma uk4_fuel_cf : forall g k i p, (Z.to_nat (un g - p) < k)%nat -> HC4_cf g i p.
Proof.
  intros g k. induction k as [|k IH]; intros i p Hk; [lia|].
  intros c Hcap HK.
  pose proof HK as (b & h & buf & a3 & Hgood & fx' & L & A & regs & mem & md & Ec & Hfrm & HF & HP & HPr).
  destruct HPr as (_ & _ & Hi & Hp & K & _).
  destruct (upos_fit g p ltac:(lia) K) as (H1 & H2).
  set (p1 := upos g (uQ g p)) in *.
  rewrite (uwalk_unfold g p1 ltac:(lia)).
  apply (HL_cf g i p); [| exact Hcap | exact HK].
  apply HL2_cf; [apply IH; lia | apply H5_cf].
Qed.

Lemma uk4_all_cf : forall g i p, HC4_cf g i p.
Proof. intros g i p. apply (uk4_fuel_cf g (S (Z.to_nat (un g - p))) i p). lia. Qed.

End Rec.
