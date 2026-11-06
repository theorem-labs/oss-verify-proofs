From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition res_inv : Type := sstart -> Z -> rview -> layout -> astate -> Prop.

Definition slot_frame (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (ra empty : Z) (rc : RunCeil) (fx : FPState) (j : nat) (E : sstart)
    (CS : list byte -> list Z) : Prop :=
  frame_facts B API LS SH SK ra empty /\ (j < 4)%nat /\
  slot_pre (fx := fx) (rc := rc) (SH := SH) (SK := SK) B (API rc) ra empty j E CS /\ CS_ok CS.

Definition entry_ok (CS : list byte -> list Z) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    SR (ms_segs B) (slot_cfg (fx := fx) B E)
      (fun c => slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS c \/
                LI (rc := rc) B (API rc) E RI 0 0 c).

Definition pass_when (RI : res_inv) (P : sstart -> Z -> Prop) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall t k c,
      LI (rc := rc) B (API rc) E RI t k c -> t < OPS_MAX -> k < ss_n E -> P E k ->
      SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').

Definition pass_ok (RI : res_inv) (op : Z) : Prop := pass_when RI (fun E k => op_at E k = op).

Definition pass9_dead_ok (RI : res_inv) : Prop :=
  pass_when RI (fun E k => op_at E k = 9 /\ (k + 1 = ss_n E \/ Z.even (in_byte E (k + 1)) = true)).

Definition pass9_gone_ok (RI : res_inv) : Prop :=
  pass_when RI (fun E k => op_at E k = 9 /\ k + 1 < ss_n E /\ Z.odd (in_byte E (k + 1)) = true).

Definition exit_ok (CS : list byte -> list Z) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall t k c,
      LI (rc := rc) B (API rc) E RI t k c -> t = OPS_MAX \/ k = ss_n E ->
      SR (ms_segs B) c (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS).

Lemma pass_when_split : forall RI (P P1 P2 : sstart -> Z -> Prop),
  (forall E k, k < ss_n E -> P E k -> P1 E k \/ P2 E k) ->
  pass_when RI P1 -> pass_when RI P2 -> pass_when RI P.
Proof.
  intros RI P P1 P2 HS H1 H2 B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk HP.
  destruct (HS E k Hk HP) as [Q|Q]; [exact (H1 B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Q)|
                                     exact (H2 B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Q)].
Qed.

Lemma pass9_of_branches : forall RI, pass9_dead_ok RI -> pass9_gone_ok RI -> pass_ok RI 9.
Proof.
  intros RI HD HG. unfold pass_ok. eapply pass_when_split; [|exact HD|exact HG]. cbv beta.
  intros E k Hk Hop. destruct (Z.eq_dec (k + 1) (ss_n E)) as [Heq|Hne]; [left; split; [exact Hop|left; exact Heq]|].
  destruct (Z.even (in_byte E (k + 1))) eqn:Ev; [left; split; [exact Hop|right; reflexivity]|].
  right. split; [exact Hop|]. split; [lia|]. rewrite <- Z.negb_even, Ev. reflexivity.
Qed.
