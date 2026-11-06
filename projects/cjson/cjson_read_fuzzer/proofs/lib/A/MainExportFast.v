(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mj1 (kw : list kentry) (VR : vranges) (HLO HHI : Z) (f : mfact) (K : kentry) : bool :=
  match f, K with
  | MCell a w v, KWord sa w' e =>
      if Nat.eqb w w' && is_cellw w && addr_match VR sa a && val_match e v then covered kw sa (Z.of_nat w) else false
  | MZeroC a n, KZero sa ne => if lit_len ne n && addr_match VR sa a then covered kw sa n else false
  | MZeroC a n, KWord sa w (ELit 0) => if Z.eqb n (Z.of_nat w) && addr_match VR sa a then covered kw sa n else false
  | MRo a w v, KWord sa w' e => Nat.eqb w w' && addr_match VR sa a && val_match e v
  | MZero a n, KZero sa ne => lit_len ne n && addr_match VR sa a
  | MFill a n c, KFill sa ne c' => Z.eqb c c' && lit_len ne n && addr_match VR sa a
  | MImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi' && (HLO <=? lo) && (hi <=? HHI)
  | MWr a n, KWr sa ne => lit_len ne n && addr_match VR sa a
  | MZeroS a n, KZero sa ne => sym_len VR ne n && addr_match VR sa a
  | MWrS a n, KWr sa ne => sym_len VR ne n && addr_match VR sa a
  | _, _ => false
  end.

Lemma mjustify_mj1 : forall kn VR HLO HHI f, mjustify kn VR HLO HHI f = existsb (mj1 kn VR HLO HHI f) kn.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition zfp (a : zexp) : Z := match a with ZLit z => z | ZAdd _ (ZLit k) => k | _ => 0 end.
Definition sfp (sa : saddr) : Z := match a_base sa with ELit z => z + a_off sa | _ => a_off sa end.
Definition kfp (K : kentry) : Z :=
  match K with
  | KWord sa _ _ => sfp sa | KZero sa _ => sfp sa | KFill sa _ _ => sfp sa | KWr sa _ => sfp sa | KImg lo _ => lo | _ => 0
  end.
Definition ffp (f : mfact) : Z :=
  match f with
  | MCell a _ _ => zfp a | MZeroC a _ => zfp a | MRo a _ _ => zfp a | MZero a _ => zfp a | MFill a _ _ => zfp a
  | MImg lo _ => lo | MWr a _ => zfp a | MZeroS a _ => zfp a | MWrS a _ => zfp a
  end.
Definition is_kwr (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.

Definition mjustify_fast (kn : list kentry) (VR : vranges) (HLO HHI : Z) (MF : list mfact) : bool :=
  let knf := List.map (fun K => (kfp K, K)) kn in
  let kw := List.filter is_kwr kn in
  forallb (fun f => let ff := ffp f in
                    if existsb (fun p => if Z.eqb (fst p) ff then mj1 kw VR HLO HHI f (snd p) else false) knf
                    then true else mjustify kn VR HLO HHI f) MF.

Lemma covered_filter : forall kn sa n, covered (List.filter is_kwr kn) sa n = true -> covered kn sa n = true.
Proof.
  intros kn sa n H. unfold covered in *. apply existsb_exists in H as (K & HK & HT).
  apply filter_In in HK as [HK _]. apply existsb_exists. exists K. split; assumption.
Qed.

Lemma mj1_filter : forall kn VR HLO HHI f K,
  mj1 (List.filter is_kwr kn) VR HLO HHI f K = true -> mj1 kn VR HLO HHI f K = true.
Proof.
  intros kn VR HLO HHI f K H. destruct f, K; cbn [mj1] in *; try exact H; try discriminate H.
  - destruct (Nat.eqb w w0 && is_cellw w && addr_match VR a0 a && val_match v0 v)%bool; [apply covered_filter; exact H | discriminate H].
  - destruct v; try discriminate H. destruct z; try discriminate H.
    destruct (Z.eqb n (Z.of_nat w) && addr_match VR a0 a)%bool; [apply covered_filter; exact H | discriminate H].
  - destruct (lit_len n0 n && addr_match VR a0 a)%bool; [apply covered_filter; exact H | discriminate H].
Qed.

Theorem mjustify_fast_sound : forall kn VR HLO HHI MF,
  mjustify_fast kn VR HLO HHI MF = true -> forallb (mjustify kn VR HLO HHI) MF = true.
Proof.
  intros kn VR HLO HHI MF H. unfold mjustify_fast in H. cbv zeta in H.
  apply forallb_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) H f Hf) as Hx. cbv beta in Hx.
  destruct (existsb _ _) eqn:Ee in Hx; [| exact Hx].
  apply existsb_exists in Ee as (p & Hp & Ht). apply in_map_iff in Hp as (K & <- & HK). cbn [fst snd] in Ht.
  destruct (Z.eqb (kfp K) (ffp f)); [| discriminate Ht].
  rewrite mjustify_mj1. apply existsb_exists. exists K. split; [exact HK | apply mj1_filter; exact Ht].
Qed.
