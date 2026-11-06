(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymPlan UbSymPlanSoundA LibIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TP0 (lo hi : Z) : Prop := LibIface.lib_stmt_U ->
  forall (sp0 gm area brkv mas tid sec : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    lo <= hdr_paylen content <= hi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32904) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

(* [comment removed for export] *)
Definition TPK (k lo hi : Z) : Prop := LibIface.lib_stmt_U ->
  forall (sp0 B area brkv mas tid sec : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    lo <= hdr_paylen content <= hi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32904) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

(* [comment removed for export] *)
Record tpc : Type := TPC { c_lo : Z; c_hi : Z; c_ok : TP0 c_lo c_hi }.
Record tpck (k : Z) : Type := TPCK { ck_lo : Z; ck_hi : Z; ck_ok : TPK k ck_lo ck_hi }.

Arguments TPCK {k} _ _ _.
Arguments ck_lo {k} _.
Arguments ck_hi {k} _.
Arguments ck_ok {k} _.

(* [comment removed for export] *)

Fixpoint covers (ivs : list (Z * Z)) (lo hi : Z) : bool :=
  match ivs with
  | [] => Z.ltb hi lo
  | (a, b) :: rest => (Z.ltb hi lo) || (Z.leb a lo && covers rest (Z.max lo (b + 1)) hi)
  end.

Lemma covers_sound : forall ivs lo hi x,
  covers ivs lo hi = true -> lo <= x <= hi -> exists ab, In ab ivs /\ fst ab <= x <= snd ab.
Proof.
  induction ivs as [|[a b] rest IH]; intros lo hi x Hc Hx; cbn [covers] in Hc.
  - apply Z.ltb_lt in Hc. lia.
  - apply orb_prop in Hc. destruct Hc as [Hc|Hc]; [apply Z.ltb_lt in Hc; lia|].
    apply andb_prop in Hc as [Ha Hr]. apply Z.leb_le in Ha.
    destruct (Z.le_gt_cases x b) as [Hle|Hgt].
    + exists (a, b). split; [left; reflexivity | cbn; lia].
    + destruct (IH (Z.max lo (b + 1)) hi x Hr ltac:(lia)) as (ab & Hin & Hab).
      exists ab. split; [right; exact Hin | exact Hab].
Qed.

Definition ivs0 (cls : list tpc) : list (Z * Z) := map (fun c => (c_lo c, c_hi c)) cls.
Definition ivsk {k : Z} (cls : list (tpck k)) : list (Z * Z) := map (fun c => (ck_lo c, ck_hi c)) cls.

Theorem tp0_dispatch : forall (cls : list tpc) (lo hi : Z),
  covers (ivs0 cls) lo hi = true -> TP0 lo hi.
Proof.
  intros cls lo hi Hc HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV SM Hn.
  destruct (covers_sound (ivs0 cls) lo hi (hdr_paylen content) Hc Hn) as (ab & Hin & Hab).
  unfold ivs0 in Hin. apply in_map_iff in Hin as (c & <- & Hin). cbn [fst snd] in Hab.
  exact (c_ok c HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV SM Hab).
Qed.

Theorem tpk_dispatch : forall (k : Z) (cls : list (tpck k)) (lo hi : Z),
  covers (ivsk cls) lo hi = true -> TPK k lo hi.
Proof.
  intros k cls lo hi Hc HLIB sp0 B area brkv mas tid sec content R M VM model TP TV SM Hn.
  destruct (covers_sound (ivsk cls) lo hi (hdr_paylen content) Hc Hn) as (ab & Hin & Hab).
  unfold ivsk in Hin. apply in_map_iff in Hin as (c & <- & Hin). cbn [fst snd] in Hab.
  exact (ck_ok c HLIB sp0 B area brkv mas tid sec content R M VM model TP TV SM Hab).
Qed.

(* [comment removed for export] *)
Lemma paylen_range0 : forall sp0 gm area brkv mas tid sec content R M,
  target_pre sp0 gm area brkv mas tid sec content R M -> 0 <= hdr_paylen content <= 65529.
Proof.
  intros sp0 gm area brkv mas tid sec content R M TP.
  pose proof (tp_len _ _ _ _ _ _ _ _ _ _ TP) as HL.
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as CR.
  unfold hdr_paylen, hdr_cfglen in *. lia.
Qed.

(* [comment removed for export] *)
Lemma paylen_rangek : forall k sp0 B area brkv mas tid sec content R M (c1 c2 : Z),
  target_pre_k k sp0 B area brkv mas tid sec content R M ->
  capk (k - 1) = c1 -> capk k = c2 ->
  Z.max 0 (c1 - 32773) <= hdr_paylen content <= c2 - 7.
Proof.
  intros k sp0 B area brkv mas tid sec content R M c1 c2 TP <- <-.
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ _ TP) as HK.
  pose proof (Z.mod_pos_bound (hdr_cfg content) 32768 ltac:(lia)) as CR.
  unfold hdr_paylen, hdr_cfglen in *. lia.
Qed.

Lemma k_range_of_pre : forall k sp0 B area brkv mas tid sec content R M,
  target_pre_k k sp0 B area brkv mas tid sec content R M -> 1 <= k <= 10.
Proof. intros k sp0 B area brkv mas tid sec content R M TP. exact (wk_k _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ TP)). Qed.

Lemma k_cases : forall k : Z, 1 <= k <= 10 ->
  k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10.
Proof. intros k Hk. lia. Qed.

