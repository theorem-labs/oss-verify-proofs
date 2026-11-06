(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import MainExport MainFactsAsan MainEntry.
Import ListNotations.
Open Scope Z_scope.

Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Definition aspace_beg (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.

Theorem primary_shadow0 : forall (V : nat -> Z) (m : word -> option byte),
  ashadow0 V m -> Forall (pfact_ok V) asan_pure_facts ->
  (forall i, 0 <= i < 2^34 -> m (wa (shad (aspace_beg V) + i)) = Some (Z_to_bv 8 0))
  /\ wr_at asegs m (shad (aspace_beg V)) (2^34).
Proof.
  intros V m SH HP.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 208)) 137439023104) D207.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 208)) 137439023104) D78.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D226.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D228.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 245)) 4096) D245.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200) D377.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576) D453.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608) D454.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 471)) 4096) D471.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
  set (SB := aspace_beg V).
  assert (SBR : 4096 * V 208%nat + 4096 <= SB /\ SB + 2^37 + 4096 <= 4096 * V 208%nat + 137439023104 /\ SB mod 8 = 0).
  { subst SB. unfold aspace_beg. clear - P209. Local Ltac2 Set LiaHints.tbl := fun () => "0090>14921081086.2516085729392.7 29784549078.2445193322230.2 4720506910.2  59308587409.1259308587409.8 59308587409.9 65455456165.2 00000100@00A00G00M00g011027028SS4P2082S12S22HaSS4P209S4P209S2P03P102DW2S12S22S82Ha2HrS2S82Ha2HrS4D4712S12S22S82Ha2Hr4D4544D4534D3774D3104D2454D2284D2274D2073D784P208S".
split; [lia|]. split; [lia|]. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }   (* [comment removed for export] *)
  destruct SBR as (S1 & S2 & S8).
  assert (SHE : shad SB = 2147450880 + SB / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (ashadow0_range V m (shad SB) (2^34) SH ltac:(lia)) as (Z0 & W0 & _); [| split; [exact Z0| exact W0]].
  intros a Ha. rewrite SHE in Ha.
  split.
  - unfold ashadow. right. clear - Ha P208 S1 S2. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - intros (bn & Hin & Hr). unfold asan_vis_app in Hin. cbn [In] in Hin. unfold ASHOFF in Hr.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd zv] in Hr.
    + clear - Ha Hr D471 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D454 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D453 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D377 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D310 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D245 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D228 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D227 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + (* [comment removed for export] *)
      clear - Ha Hr S1 S2 S8 P209. subst SB. unfold aspace_beg in *. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D207 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + clear - Ha Hr D78 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + (* [comment removed for export] *) clear - Ha Hr P208 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + (* [comment removed for export] *) clear - Ha Hr DW P0 P10 P208 S1 S2 S8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
