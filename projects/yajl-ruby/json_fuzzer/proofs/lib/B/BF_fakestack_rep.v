(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanState AsanFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition kFsClasses : Z := 11.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kFsBytes : Z := 11571200.           (* [comment removed for export] *)
Definition fs_flags_total : Z := 2 ^ 15.       (* [comment removed for export] *)
Definition FS_SB : Z := 0x7fff8000.            (* [comment removed for export] *)
Definition fs_shadow (a : Z) : Z := FS_SB + a / 8.

(* [comment removed for export] *)
Definition aflagB (E : aenv) (fsbase N ff : Z) : Z := fs_flag_addr fsbase N (fs_pos_of_frame fsbase N ff).

(* [comment removed for export] *)
Record fs_plumb := mkFsPlumb {
  fp_ctx : Z;        (* [comment removed for export] *)
  fp_dtls : Z;       (* [comment removed for export] *)
  fp_dtv1 : Z;       (* [comment removed for export] *)
  fp_tlsb : Z; fp_tlse : Z   (* [comment removed for export] *)
}.
Section Plumbing.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Definition FS_TP : Z := 0x5e1550.
  (* [comment removed for export] *)
  Definition FS_CF : Z := 0x1400e8.
  Definition FS_VB : Z := 0x13e058.
  Definition FS_DTO : Z := 0x8.     (* [comment removed for export] *)
  Definition FSEnv (E : aenv) (fsbase : Z) (pl : fs_plumb) (m : mem) : Prop :=
       (* [comment removed for export] *)
       rw_cells segs m 0xa6280 [C8 (wz 1); C8 (wz 0xfffffffffffff800)]
       (* [comment removed for export] *)
    /\ rw_cells segs m 0xa7340 [C8 (wz 0x9f4c0)]
       (* [comment removed for export] *)
    /\ rw_cells segs m 0xaf298 [C1 (Z_to_bv 8 1)]
       (* [comment removed for export] *)
    /\ rw_cells segs m 0x5e1548 [C8 (wz 0x5e1570)]     (* [comment removed for export] *)
    /\ rw_cells segs m 0x5e1578 [C8 (wz 0x5e1d50)]
       (* [comment removed for export] *)
    /\ rw_cells segs m FS_TP [C8 (wz fsbase)]
       (* [comment removed for export] *)
    /\ rw_cells segs m 0xade20 [C1 (Z_to_bv 8 1)]
    /\ rw_cells segs m 0xade24 [C4 (wz 0)]
    /\ rw_cells segs m 0x5e14f8 [C8 (wz 0x6028f8)]
    /\ rw_cells segs m 0x6028f8 [C8 (wz (fp_ctx pl))]
    /\ rw_cells segs m (fp_ctx pl + 152) [C8 (wz (ae_thread E))]
    /\ rw_cells segs m (ae_thread E + 48) [C8 (wz (fp_tlsb pl)); C8 (wz (fp_tlse pl))]
       (* [comment removed for export] *)
    /\ (exists cf vb dto, rw_cells segs m 0xa5590 [C8 (wz cf)] /\ rw_cells segs m (cf + 137) [C1 (Z_to_bv 8 1)]
                      /\ rw_cells segs m 0xa55f0 [C8 (wz vb)] /\ rw_cells segs m vb [C4 (wz 0)]
                      /\ rw_cells segs m 0xa6290 [C8 (wz dto)] /\ rw_cells segs m (dto + FS_TP) [C8 (wz (fp_dtls pl))]
                      /\ 0x10000 <= cf /\ cf + 138 <= 0x603000 /\ 0x10000 <= vb /\ vb + 4 <= 0x603000
                      /\ 0 <= dto /\ FS_TP + dto + 8 <= 0x603000
                      /\ cf = FS_CF /\ vb = FS_VB /\ dto = FS_DTO   (* [comment removed for export] *))
    /\ rw_cells segs m (fp_dtls pl + 24) [C8 (wz (fp_dtv1 pl))] /\ fp_dtv1 pl <> 0 /\ 0 <= fp_dtv1 pl < 2^64
    /\ 0 < fp_dtls pl /\ fp_dtls pl + 4096 <= alloc_ceiling /\ fp_dtls pl mod 8 = 0
    /\ 0 < fp_ctx pl /\ fp_ctx pl + 160 <= alloc_ceiling /\ fp_ctx pl mod 8 = 0
    /\ 0 < ae_thread E /\ ae_thread E + 64 <= alloc_ceiling /\ ae_thread E mod 8 = 0
       (* [comment removed for export] *)
    /\ rw_cells segs m 0xa55a0 [C8 (wz 0xae5b8)] /\ rw_cells segs m 0xae5b8 [C8 (wz 0x7fff8000)].

  (* [comment removed for export] *)
  Definition fs_pos_ok (cid pos : Z) : Prop := 0 <= cid <= 1 /\ 0 <= pos < fs_nframes cid.
  (* [comment removed for export] *)
  Definition lf_mem (LF : list (Z * Z)) (cid ff : Z) : bool :=
    existsb (fun f => Z.eqb (fst f) cid && Z.eqb (snd f) ff) LF.
  Definition flag_byte (LF : list (Z * Z)) (fsbase cid pos : Z) : byte :=
    Z_to_bv 8 (Z.b2z (lf_mem LF cid (fs_frame_addr fsbase cid pos))).

  Definition FSRep (E : aenv) (fsbase : Z) (fs : fsstate) (LF : list (Z * Z)) (m : mem) : Prop :=
       (* [comment removed for export] *)
       fsbase mod 4096 = 0 /\ 0x603000 <= fsbase /\ fsbase + kFsBytes <= alloc_ceiling
    /\ (fsbase + kFsBytes <= FS_SB - 4096 \/ FS_SB + 2^44 <= fsbase)
       (* [comment removed for export] *)
    /\ (forall cid, 0 <= cid < kFsClasses -> exists h, rw_cells segs m (fsbase + 8 * cid) [C8 h])
    /\ rw_cells segs m (fsbase + 88) [C8 (wz kFsLog)]
    /\ rw_cells segs m (fsbase + 96) [C1 (Z_to_bv 8 0)]
       (* [comment removed for export] *)
    /\ (forall cid pos, fs_pos_ok cid pos -> rw_cells segs m (fs_flag_addr fsbase cid pos) [C1 (flag_byte LF fsbase cid pos)])
       (* [comment removed for export] *)
    /\ (forall cid pos, fs_pos_ok cid pos ->
          stk segs m (fs_frame_addr fsbase cid pos) (fs_frame_addr fsbase cid pos + fs_frame_bytes cid)
          /\ stk segs m (fs_shadow (fs_frame_addr fsbase cid pos)) (fs_shadow (fs_frame_addr fsbase cid pos) + fs_frame_bytes cid / 8))
       (* [comment removed for export] *)
    /\ List.NoDup LF
    /\ (forall N ff, In (N, ff) LF -> exists pos, fs_pos_ok N pos /\ ff = fs_frame_addr fsbase N pos).
End Plumbing.

(* [comment removed for export] *)
Definition in_fs_object (fsbase a : Z) : Prop :=        (* [comment removed for export] *)
  (fsbase <= a < fsbase + kFsBytes) \/ (fs_shadow fsbase <= a < fs_shadow fsbase + kFsBytes / 8).

Lemma rw_cells_agree_eq : forall segs m m' A cs,
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
  rw_cells segs m A cs -> rw_cells segs m' A cs.
Proof. aceil.
  intros segs m m' A cs HA [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - destruct HB as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (H2 i Hi). unfold mrd.
    rewrite cells_bytes_length in Hi by exact Hwf.
    destruct (HA (A + Z.of_nat i) ltac:(lia)) as [E _]. rewrite E. reflexivity.
  - destruct HW as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    destruct (HA (A + i) ltac:(lia)) as [_ W]. apply W. apply H2. exact Hi.
Qed.

(* [comment removed for export] *)
Definition fsenv_ranges (E : aenv) (fsbase : Z) (pl : fs_plumb) : list (Z * Z) :=
  [ (0xa6280, 0xa6290); (0xa7340, 0xa7348); (0xaf298, 0xaf299); (0x5e1548, 0x5e1550); (0x5e1578, 0x5e1580);
    (FS_TP, FS_TP + 8); (0xade20, 0xade21); (0xade24, 0xade28); (0x5e14f8, 0x5e1500); (0x6028f8, 0x602900);
    (fp_ctx pl + 152, fp_ctx pl + 160); (ae_thread E + 48, ae_thread E + 64);
    (0xa5590, 0xa5598); (FS_CF + 137, FS_CF + 138); (0xa55f0, 0xa55f8); (FS_VB, FS_VB + 4);
    (0xa6290, 0xa6590); (FS_DTO + FS_TP, FS_DTO + FS_TP + 8); (fp_dtls pl + 24, fp_dtls pl + 32);
    (0xa55a0, 0xa55a8); (0xae5b8, 0xae5c0) ].
Definition fsenv_fp (E : aenv) (fsbase : Z) (pl : fs_plumb) (a : Z) : Prop :=
  Exists (fun r => fst r <= a < snd r) (fsenv_ranges E fsbase pl).

Lemma FSEnv_frame : forall segs E fsbase pl m m',
  FSEnv segs E fsbase pl m -> Frame.wmono segs m m' ->
  (forall a, fsenv_fp E fsbase pl a -> m' (wa a) = m (wa a)) ->
  FSEnv segs E fsbase pl m'.
Proof. aceil.
  intros segs E fsbase pl m m' ENV WM AG.
  assert (RW : forall A cs, rw_cells segs m A cs ->
            Exists (fun r => fst r <= A /\ A + Z.of_nat (cells_size cs) <= snd r) (fsenv_ranges E fsbase pl) ->
            rw_cells segs m' A cs).
  { intros A cs H HE. apply (rw_cells_agree_eq segs m m'); [|exact H]. intros a Ha. split; [|apply WM].
    apply AG. unfold fsenv_fp. apply Exists_exists in HE as (r & Hr & R1 & R2). apply Exists_exists. exists r. split; [exact Hr | lia]. }
  Ltac fsr RW := apply RW; [assumption | unfold fsenv_ranges; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd];
                                        repeat (apply Exists_cons_hd; cbn [fst snd]; unfold FS_TP, FS_CF, FS_VB, FS_DTO; lia) || apply Exists_cons_tl].
  destruct ENV as (DESC & REAL & INI & DTV & DTV1 & TLS & KI & KEY & TSD & TSD0 & CTXT & THR
                   & (cf & vb & dto & GF & CF & GV & VB & GD & DT & CF1 & CF2 & VB1 & VB2 & DT1 & DT2 & -> & -> & ->) & DTVE & NZ & DVR & D0 & D1 & D8 & C0 & C1 & C8 & T0 & T1 & T8 & GSB & SBV).
  unfold FSEnv.
  repeat match goal with |- _ /\ _ => split end; try (fsr RW); try tauto.
  exists FS_CF, FS_VB, FS_DTO. repeat match goal with |- _ /\ _ => split end; try (fsr RW); try lia.
Qed.

Lemma stk_agree_eq : forall segs m m' lo hi,
  (forall a, lo <= a < hi -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
  stk segs m lo hi -> stk segs m' lo hi.
Proof. aceil.
  intros segs m m' lo hi HA (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H2 a Ha) as [W [b R]]. destruct (HA a Ha) as [E WW]. split; [exact (WW W)|]. exists b. unfold mrd in *. rewrite E. exact R.
Qed.

(* [comment removed for export] *)
Lemma FSRep_frame : forall segs E fsbase fs LF m m',
  (forall a, in_fs_object fsbase a -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
  FSRep segs E fsbase fs LF m -> FSRep segs E fsbase fs LF m'.
Proof. aceil.
  intros segs E fsbase fs LF m m' HA (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
  pose proof G4 as G4'. unfold FS_SB, kFsBytes in G4'.
  assert (NF : forall cid, 0 <= cid <= 1 -> 0 < fs_nframes cid <= 16384).
  { intros cid Hc. unfold fs_nframes, kFsLog, kFsMinFrameLog in *.
    split; [apply Z.pow_pos_nonneg; lia|].
    change 16384 with (2 ^ 14). apply Z.pow_le_mono_r; lia. }
  assert (FB : forall cid, 0 <= cid <= 1 -> 64 <= fs_frame_bytes cid <= 65536 /\ fs_frame_bytes cid * fs_nframes cid = 2 ^ 20).
  { intros cid Hc. unfold fs_frame_bytes, fs_nframes, kFsLog, kFsMinFrameLog in *. split.
    - split; [change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia | change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia].
    - rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
  split. { intros cid Hc. destruct (HH cid Hc) as [h Hh]. exists h. apply (rw_cells_agree_eq segs m m'); [| exact Hh]. intros a Ha. apply HA. unfold in_fs_object, kFsBytes, kFsClasses in *. cbn in Ha. lia. }
  split. { apply (rw_cells_agree_eq segs m m'); [| exact HL]. intros a Ha. apply HA. unfold in_fs_object, kFsBytes. cbn in Ha. lia. }
  split. { apply (rw_cells_agree_eq segs m m'); [| exact HG]. intros a Ha. apply HA. unfold in_fs_object, kFsBytes. cbn in Ha. lia. }
  split. { intros cid pos Hp. apply (rw_cells_agree_eq segs m m'); [| exact (HF cid pos Hp)]. intros a Ha. apply HA. cbn in Ha.
           destruct Hp as [Hc Hq]. pose proof (NF cid Hc).
           unfold in_fs_object, fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset, kFsBytes, kFsClasses in *.
           destruct (cid =? 0); unfold fs_nframes, kFsLog, kFsMinFrameLog in *; cbn in *; lia. }
  split. { intros cid pos Hp. destruct (HW cid pos Hp) as [W1 W2].
           destruct Hp as [Hc Hq]. pose proof (NF cid Hc) as N1. pose proof (FB cid Hc) as [F1 F2].
           assert (R : fsbase + 4096 <= fs_frame_addr fsbase cid pos /\ fs_frame_addr fsbase cid pos + fs_frame_bytes cid <= fsbase + kFsBytes).
           { unfold fs_frame_addr, fs_frames_base, kFsFlagsOffset, kFsBytes, kFsLog, kFsMinFrameLog.
             cbn [Z.pow Z.add Z.sub Pos.add Z.mul Pos.mul].
             assert (fs_frame_bytes cid * pos + fs_frame_bytes cid <= 2 ^ 20) by nia. nia. }
           split.
           - apply (stk_agree_eq segs m m'); [| exact W1]. intros a Ha. apply HA. left. unfold kFsBytes in *. lia.
           - apply (stk_agree_eq segs m m'); [| exact W2]. intros a Ha. apply HA. right.
             unfold fs_shadow, kFsBytes in *. Z.div_mod_to_equations. lia. }
  split; [exact ND| exact HLF].
Qed.

Lemma lf_mem_In : forall LF cid ff, lf_mem LF cid ff = true <-> In (cid, ff) LF.
Proof. aceil.
  intros LF cid ff. unfold lf_mem. rewrite existsb_exists. split.
  - intros ([c f] & Hin & Hb). cbn in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
  - intros Hin. exists (cid, ff). split; [exact Hin|]. cbn. rewrite !Z.eqb_refl. reflexivity.
Qed.
Lemma lf_mem_perm : forall LF LF' cid ff, Permutation LF LF' -> lf_mem LF cid ff = lf_mem LF' cid ff.
Proof. aceil.
  intros LF LF' cid ff PE. destruct (lf_mem LF cid ff) eqn:E1; destruct (lf_mem LF' cid ff) eqn:E2; try reflexivity.
  - apply lf_mem_In in E1. apply (Permutation_in _ PE) in E1. apply lf_mem_In in E1. congruence.
  - apply lf_mem_In in E2. apply (Permutation_in _ (Permutation_sym PE)) in E2. apply lf_mem_In in E2. congruence.
Qed.

Lemma FSRep_perm : forall segs E fsbase fs LF LF' m,
  FSRep segs E fsbase fs LF m -> Permutation LF LF' -> FSRep segs E fsbase fs LF' m.
Proof. aceil.
  intros segs E fsbase fs LF LF' m (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF) PE.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact HH|]. split; [exact HL|]. split; [exact HG|]. split.
  - intros cid pos Hp. unfold flag_byte. rewrite <- (lf_mem_perm LF LF' _ _ PE). exact (HF cid pos Hp).
  - split; [exact HW|]. split.
    + eapply Permutation_NoDup; [exact PE| exact ND].
    + intros N ff H. apply HLF. eapply Permutation_in; [apply Permutation_sym; exact PE| exact H].
Qed.

(* [comment removed for export] *)
Lemma FSRep_fs_irrel : forall segs E fsbase fs fs' LF m, FSRep segs E fsbase fs LF m -> FSRep segs E fsbase fs' LF m.
Proof. aceil. intros segs E fsbase fs fs' LF m H. exact H. Qed.

(* [comment removed for export] *)
Lemma fs_pos_of_frame_addr : forall fsbase cid pos, 0 <= cid -> 0 <= pos ->
  fs_pos_of_frame fsbase cid (fs_frame_addr fsbase cid pos) = pos.
Proof. aceil.
  intros fsbase cid pos Hc Hp. unfold fs_pos_of_frame, fs_frame_addr.
  assert (0 < fs_frame_bytes cid) by (unfold fs_frame_bytes, kFsMinFrameLog; apply Z.pow_pos_nonneg; lia).
  replace (fs_frames_base fsbase cid + fs_frame_bytes cid * pos - fs_frames_base fsbase cid) with (pos * fs_frame_bytes cid) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma aflagB_frame : forall E fsbase cid pos, 0 <= cid -> 0 <= pos ->
  aflagB E fsbase cid (fs_frame_addr fsbase cid pos) = fs_flag_addr fsbase cid pos.
Proof. aceil. intros. unfold aflagB. rewrite fs_pos_of_frame_addr by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint lf_remove (N ff : Z) (LF : list (Z * Z)) : list (Z * Z) :=
  match LF with [] => [] | f :: r => if (Z.eqb (fst f) N && Z.eqb (snd f) ff)%bool then r else f :: lf_remove N ff r end.

Lemma lf_remove_notin : forall N ff LF, ~ In (N, ff) LF -> lf_remove N ff LF = LF.
Proof. aceil.
  induction LF as [|[c f] r IH]; intros H; cbn; [reflexivity|].
  destruct (Z.eqb_spec c N); destruct (Z.eqb_spec f ff); cbn; try (rewrite IH; [reflexivity| intros X; apply H; right; exact X]).
  exfalso. apply H. left. subst. reflexivity.
Qed.

Lemma lf_remove_in : forall N ff LF, List.NoDup LF -> In (N, ff) LF ->
  exists l1 l2, LF = l1 ++ (N, ff) :: l2 /\ lf_remove N ff LF = l1 ++ l2 /\ ~ In (N, ff) (l1 ++ l2).
Proof. aceil.
  induction LF as [|[c f] r IH]; intros ND Hin; [destruct Hin|].
  inversion ND as [|x l Hx Hl]; subst. cbn.
  destruct (Z.eqb_spec c N) as [->|Hc]; destruct (Z.eqb_spec f ff) as [->|Hf]; cbn.
  - exists [], r. split; [reflexivity|]. split; [reflexivity|]. exact Hx.
  - destruct Hin as [E|Hin]; [congruence|]. destruct (IH Hl Hin) as (l1 & l2 & -> & E2 & NI). exists ((N, f) :: l1), l2.
    split; [reflexivity|]. split; [cbn; rewrite E2; reflexivity|]. intros [E|X]; [congruence| exact (NI X)].
  - destruct Hin as [E|Hin]; [congruence|]. destruct (IH Hl Hin) as (l1 & l2 & -> & E2 & NI). exists ((c, ff) :: l1), l2.
    split; [reflexivity|]. split; [cbn; rewrite E2; reflexivity|]. intros [E|X]; [congruence| exact (NI X)].
  - destruct Hin as [E|Hin]; [congruence|]. destruct (IH Hl Hin) as (l1 & l2 & -> & E2 & NI). exists ((c, f) :: l1), l2.
    split; [reflexivity|]. split; [cbn; rewrite E2; reflexivity|]. intros [E|X]; [congruence| exact (NI X)].
Qed.

Lemma lf_mem_remove_other : forall N ff LF c f, List.NoDup LF -> In (N, ff) LF -> (c, f) <> (N, ff) ->
  lf_mem (lf_remove N ff LF) c f = lf_mem LF c f.
Proof. aceil.
  intros N ff LF c f ND Hin NE. destruct (lf_remove_in N ff LF ND Hin) as (l1 & l2 & -> & -> & NI).
  destruct (lf_mem (l1 ++ l2) c f) eqn:E1; destruct (lf_mem (l1 ++ (N, ff) :: l2) c f) eqn:E2; try reflexivity.
  - apply lf_mem_In in E1. assert (X : In (c, f) (l1 ++ (N, ff) :: l2)) by (apply in_app_iff in E1; apply in_app_iff; cbn; tauto).
    apply lf_mem_In in X. congruence.
  - apply lf_mem_In in E2. apply in_app_iff in E2. cbn in E2.
    assert (X : In (c, f) (l1 ++ l2)) by (apply in_app_iff; destruct E2 as [A|[A|A]]; [tauto| congruence| tauto]).
    apply lf_mem_In in X. congruence.
Qed.

Section Release.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Lemma fs_flag_addr_inj : forall fsbase c p c' p', fs_pos_ok c p -> fs_pos_ok c' p' ->
    fs_flag_addr fsbase c p = fs_flag_addr fsbase c' p' -> c = c' /\ p = p'.
  Proof. aceil.
    intros fsbase c p c' p' [Hc Hp] [Hc' Hp'] E.
    unfold fs_flag_addr, fs_flags_base, fs_flags_off, fs_nframes, kFsLog, kFsMinFrameLog, kFsFlagsOffset in *.
    assert (C : c = 0 \/ c = 1) by lia. assert (C' : c' = 0 \/ c' = 1) by lia.
    destruct C as [-> | ->]; destruct C' as [-> | ->]; cbn in *; lia.
  Qed.

  Lemma fs_frame_addr_inj : forall fsbase c p c' p', fs_pos_ok c p -> fs_pos_ok c' p' ->
    fs_frame_addr fsbase c p = fs_frame_addr fsbase c' p' -> c = c' /\ p = p'.
  Proof. aceil.
    intros fsbase c p c' p' [Hc Hp] [Hc' Hp'] E.
    unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, fs_nframes, kFsLog, kFsMinFrameLog, kFsFlagsOffset in *.
    assert (C : c = 0 \/ c = 1) by lia. assert (C' : c' = 0 \/ c' = 1) by lia.
    destruct C as [-> | ->]; destruct C' as [-> | ->]; cbn in *; lia.
  Qed.

  Lemma FSRep_release : forall E fsbase fs LF m m' N ff,
    FSRep segs E fsbase fs LF m -> In (N, ff) LF ->
    munch [(aflagB E fsbase N ff, aflagB E fsbase N ff + 1)] m m' -> wmono segs m m' ->
    rw_cells segs m' (aflagB E fsbase N ff) [C1 (Z_to_bv 8 0)] ->
    FSRep segs E fsbase fs (lf_remove N ff LF) m'.
  Proof. aceil.
    intros E fsbase fs LF m m' N ff FS Hin MU WV FL.
    pose proof FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
    pose proof G4 as G4'. unfold FS_SB, kFsBytes in G4'.
    destruct (HLF N ff Hin) as (pos & POK & ->).
    rewrite (aflagB_frame E fsbase N pos) in FL, MU by (destruct POK; lia).
    assert (NF : forall cid, 0 <= cid <= 1 -> 0 < fs_nframes cid <= 16384).
    { intros cid Hc. unfold fs_nframes, kFsLog, kFsMinFrameLog. split; [apply Z.pow_pos_nonneg; lia|].
      change 16384 with (2 ^ 14). apply Z.pow_le_mono_r; lia. }
    assert (FLR : forall c p, fs_pos_ok c p -> fsbase + 4096 <= fs_flag_addr fsbase c p < fsbase + 4096 + 2^15).
    { intros c p [Hc Hp]. pose proof (NF c Hc). unfold fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset.
      assert (C : c = 0 \/ c = 1) by lia. destruct C as [-> | ->]; unfold fs_nframes, kFsLog, kFsMinFrameLog in *; cbn in *; lia. }
    pose proof (FLR N pos POK) as FLN. unfold kFsBytes in G3. aceil.
    assert (AG : forall a, 0 <= a < 2^64 -> a <> fs_flag_addr fsbase N pos ->
              m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)).
    { intros a Ha NE. split; [| apply WV]. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
    assert (AGR : forall lo hi, (hi <= fs_flag_addr fsbase N pos \/ fs_flag_addr fsbase N pos + 1 <= lo) -> 0 <= lo -> hi <= 2^64 ->
              forall a, lo <= a < hi -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)).
    { intros lo hi D Hlo Hhi a Ha. apply AG; lia. }
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split. { intros cid Hc. destruct (HH cid Hc) as [h Hh]. exists h. eapply rw_cells_agree_eq; [| exact Hh]. cbn. apply AGR; unfold kFsClasses in Hc; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HL]. cbn. apply AGR; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HG]. cbn. apply AGR; lia. }
    split.
    { intros cid p Hp. destruct (Z.eq_dec (fs_flag_addr fsbase cid p) (fs_flag_addr fsbase N pos)) as [EQ|NE].
      - destruct (fs_flag_addr_inj fsbase cid p N pos Hp POK EQ) as [-> ->].
        unfold flag_byte. replace (lf_mem (lf_remove N (fs_frame_addr fsbase N pos) LF) N (fs_frame_addr fsbase N pos)) with false; [exact FL|].
        symmetry. destruct (lf_remove_in N (fs_frame_addr fsbase N pos) LF ND Hin) as (l1 & l2 & _ & -> & NI).
        destruct (lf_mem (l1 ++ l2) N (fs_frame_addr fsbase N pos)) eqn:EE; [| reflexivity]. apply lf_mem_In in EE. contradiction.
      - pose proof (FLR cid p Hp). unfold flag_byte. rewrite lf_mem_remove_other; [| exact ND| exact Hin|].
        2: { intros EQ. injection EQ as E1 E2. subst cid. destruct (fs_frame_addr_inj fsbase N p N pos Hp POK E2) as [_ ->]. congruence. }
        eapply rw_cells_agree_eq; [| exact (HF cid p Hp)]. cbn. intros a Ha. apply AG; lia. }
    split.
    { intros cid p Hp. destruct (HW cid p Hp) as [W1 W2].
      pose proof (FLR cid p Hp) as FLC.
      assert (R : fsbase + 4096 + 2^15 <= fs_frame_addr fsbase cid p /\ fs_frame_addr fsbase cid p + fs_frame_bytes cid <= fsbase + kFsBytes).
      { destruct Hp as [Hc Hq]. pose proof (NF cid Hc) as N1.
        assert (FB : 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid * fs_nframes cid = 2 ^ 20).
        { unfold fs_frame_bytes, fs_nframes, kFsLog, kFsMinFrameLog in *. split.
          - change 64 with (2 ^ 6). apply Z.pow_le_mono_r; lia.
          - rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        unfold fs_frame_addr, fs_frames_base, kFsFlagsOffset, kFsBytes, kFsLog, kFsMinFrameLog.
        cbn [Z.pow Z.add Z.sub Pos.add Z.mul Pos.mul].
        assert (fs_frame_bytes cid * p + fs_frame_bytes cid <= 2 ^ 20) by nia. nia. }
      unfold kFsBytes in R.
      split; (eapply stk_agree_eq; [| eassumption]); intros a Ha; apply AG; try lia.
      all: unfold fs_shadow, FS_SB in *; Z.div_mod_to_equations; lia. }
    split.
    { destruct (lf_remove_in N _ LF ND Hin) as (l1 & l2 & EL & -> & _). rewrite EL in ND. exact (List.NoDup_remove_1 _ _ _ ND). }
    intros c f H. apply HLF. destruct (lf_remove_in N _ LF ND Hin) as (l1 & l2 & EL & ER & _). rewrite ER in H. rewrite EL.
    apply in_app_iff in H. apply in_app_iff. cbn. tauto.
  Qed.
End Release.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff1 (fsbase pos : Z) : Z := fsbase + 1085440 + 128 * pos.
Definition fl1 (fsbase pos : Z) : Z := fsbase + 20480 + pos.
Definition sh1 (fsbase pos : Z) : Z := 2147450880 + ff1 fsbase pos / 8.

Lemma ff1_eq : forall fsbase pos, fs_frame_addr fsbase 1 pos = ff1 fsbase pos.
Proof. aceil. intros. unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, kFsFlagsOffset, kFsLog, kFsMinFrameLog, ff1. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add]. lia. Qed.
Lemma fl1_eq : forall fsbase pos, fs_flag_addr fsbase 1 pos = fl1 fsbase pos.
Proof. aceil. intros. unfold fs_flag_addr, fs_flags_base, fs_flags_off, fs_nframes, kFsFlagsOffset, kFsLog, kFsMinFrameLog, fl1. cbn. lia. Qed.
Lemma sh1_eq : forall fsbase pos, fs_shadow (fs_frame_addr fsbase 1 pos) = sh1 fsbase pos.
Proof. aceil. intros. unfold fs_shadow, FS_SB, sh1. rewrite ff1_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition sm1_W (sp : word) (fsbase pos : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 208, bv_unsigned sp); (fsbase + 8, fsbase + 16);
   (fl1 fsbase pos, fl1 fsbase pos + 1); (ff1 fsbase pos, ff1 fsbase pos + 128); (sh1 fsbase pos, sh1 fsbase pos + 16)].

Section Alloc1.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma FSRep_alloc1 : forall E fsbase fs fs' LF m m' (sp : word) pos (hv v w : word) j1 j2,
    FSRep segs E fsbase fs LF m -> fs_pos_ok 1 pos ->
    lf_mem LF 1 (fs_frame_addr fsbase 1 pos) = false ->
    alloc_ceiling <= bv_unsigned sp - 208 ->
    munch (sm1_W sp fsbase pos) m m' -> wmono segs m m' ->
    rw_cells segs m' (fsbase + 8) [C8 hv] ->
    rw_cells segs m' (fl1 fsbase pos) [C1 (Z_to_bv 8 1)] ->
    rw_cells segs m' (ff1 fsbase pos) [CB 24 j1; C8 v; CB 88 j2; C8 w] ->
    rw_cells segs m' (sh1 fsbase pos) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    FSRep segs E fsbase fs' ((1, fs_frame_addr fsbase 1 pos) :: LF) m'.
  Proof. aceil.
    intros E fsbase fs fs' LF m m' sp pos hv v w j1 j2 FS KP FRESH CEIL MU WV HI FLp FRp SHp.
    pose proof FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
    pose proof G4 as G4'. unfold FS_SB, kFsBytes in G4'. unfold kFsBytes in G3. aceil.
    destruct (proj1 (Z.mod_divide fsbase 8 ltac:(lia)) ltac:(Z.div_mod_to_equations; lia)) as [q Q8].
    assert (DP : forall p, ff1 fsbase p / 8 = q + 135680 + 16 * p) by (intros; unfold ff1; rewrite Q8; Z.div_mod_to_equations; lia).
    assert (NF1 : fs_nframes 1 = 8192) by reflexivity. assert (NF0 : fs_nframes 0 = 16384) by reflexivity.
    pose proof KP as [_ KPr]. rewrite NF1 in KPr.
    (* [comment removed for export] *)
    assert (AG : forall a, 0 <= a < 2^64 -> outside (sm1_W sp fsbase pos) a ->
              m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)).
    { intros a Ha Ho. split; [| apply WV]. apply MU. rewrite wa_unsigned by lia. exact Ho. }
    assert (OUTW : forall a, (fsbase <= a < fsbase + 11571200 \/ 2147450880 + q <= a < 2147450880 + q + 1446400 + 1) ->
              ~ (fsbase + 8 <= a < fsbase + 16) -> a <> fl1 fsbase pos ->
              ~ (ff1 fsbase pos <= a < ff1 fsbase pos + 128) -> ~ (sh1 fsbase pos <= a < sh1 fsbase pos + 16) ->
              outside (sm1_W sp fsbase pos) a).
    { intros a Ha N1 N2 N3 N4. unfold sm1_W, outside. unfold sh1 in *. rewrite !DP in *. unfold fl1, ff1 in *.
      repeat split; first [lia | Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (FLR : forall c p, fs_pos_ok c p -> fsbase + 4096 <= fs_flag_addr fsbase c p < fsbase + 4096 + 2^15).
    { intros c p [Hc Hp]. unfold fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset.
      assert (C : c = 0 \/ c = 1) by lia. destruct C as [-> | ->]; cbn [Z.eqb]; rewrite ?NF0, ?NF1 in *; lia. }
    assert (FRR : forall c p, fs_pos_ok c p -> fsbase + 4096 + 2^15 <= fs_frame_addr fsbase c p /\ fs_frame_addr fsbase c p + fs_frame_bytes c <= fsbase + 11571200
                /\ 0 < fs_frame_bytes c).
    { intros c p [Hc Hp]. unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, kFsFlagsOffset, kFsLog, kFsMinFrameLog.
      assert (C : c = 0 \/ c = 1) by lia. destruct C as [-> | ->]; rewrite ?NF0, ?NF1 in *; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add]; lia. }
    split; [exact G1|]. split; [exact G2|]. split; [unfold kFsBytes; aceil; lia|]. split; [exact G4|].
    split.
    { (* [comment removed for export] *) intros cid Hc. destruct (Z.eq_dec cid 1) as [->|NE1]; [exists hv; exact HI|].
      destruct (HH cid Hc) as [h Hh]. exists h. eapply rw_cells_agree_eq; [| exact Hh]. cbn. intros a Ha. apply AG; [unfold kFsClasses in Hc; lia|].
      apply OUTW; unfold sh1 in *; rewrite ?DP in *; unfold fl1, ff1, kFsClasses in *; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HL]. cbn. intros a Ha. apply AG; [lia|]. apply OUTW; unfold sh1 in *; rewrite ?DP in *; unfold fl1, ff1 in *; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HG]. cbn. intros a Ha. apply AG; [lia|]. apply OUTW; unfold sh1 in *; rewrite ?DP in *; unfold fl1, ff1 in *; lia. }
    split.
    { (* [comment removed for export] *) intros cid p Hp.
      assert (NEWFB : forall c' p', fs_pos_ok c' p' -> (c', p') <> (1, pos) ->
                flag_byte ((1, fs_frame_addr fsbase 1 pos) :: LF) fsbase c' p' = flag_byte LF fsbase c' p').
      { intros c' p' Hp' NE. unfold flag_byte, lf_mem. cbn [existsb fst snd].
        destruct (Z.eqb_spec 1 c') as [<-|Hc]; cbn [andb]; [| reflexivity].
        destruct (Z.eqb_spec (fs_frame_addr fsbase 1 pos) (fs_frame_addr fsbase 1 p')) as [EQ|Hf]; cbn [orb]; [| reflexivity].
        exfalso. destruct (fs_frame_addr_inj fsbase 1 pos 1 p' KP Hp' EQ) as [_ ->]. apply NE. reflexivity. }
      destruct (Z.eq_dec cid 1) as [->|NC].
      - destruct (Z.eq_dec p pos) as [->|NP].
        { unfold flag_byte, lf_mem. cbn [existsb fst snd]. rewrite !Z.eqb_refl. cbn. rewrite fl1_eq. exact FLp. }
        rewrite NEWFB by (try exact Hp; congruence).
        eapply rw_cells_agree_eq; [| exact (HF 1 p Hp)]. cbn. intros a Ha. pose proof (FLR 1 p Hp).
        rewrite fl1_eq in Ha. unfold fl1 in Ha. destruct Hp as [_ Hpp]. rewrite NF1 in Hpp. apply AG; [lia|].
        apply OUTW; unfold sh1 in *; rewrite ?DP in *; unfold fl1, ff1 in *; lia.
      - rewrite NEWFB by (try exact Hp; congruence).
        eapply rw_cells_agree_eq; [| exact (HF cid p Hp)]. cbn. intros a Ha. pose proof (FLR cid p Hp).
        destruct Hp as [Hc Hpp]. assert (cid = 0) by lia. subst cid. rewrite NF0 in Hpp.
        unfold fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset in Ha. cbn [Z.eqb] in Ha.
        apply AG; [lia|]. apply OUTW; unfold sh1 in *; rewrite ?DP in *; unfold fl1, ff1 in *; lia. }
    split.
    { (* [comment removed for export] *) intros cid p Hp. pose proof (FRR cid p Hp) as (R1 & R2 & R3).
      destruct (Z.eq_dec cid 1) as [->|NC].
      - assert (FB : fs_frame_bytes 1 = 128) by reflexivity. rewrite FB in *. rewrite sh1_eq, ff1_eq.
        destruct (Z.eq_dec p pos) as [->|NP].
        { split; [| change (128 / 8) with 16].
          - pose proof (stk_of_rw_cells segs m' _ _ FRp) as X. cbn in X. exact X.
          - pose proof (stk_of_rw_cells segs m' _ _ SHp) as X. cbn in X. exact X. }
        destruct (HW 1 p Hp) as [W1 W2]. rewrite ?FB in W1, W2. rewrite sh1_eq in W2. rewrite ff1_eq in W1. change (128 / 8) with 16 in W2 |- *.
        assert (pos + 1 <= p \/ p + 1 <= pos) by lia.
        destruct Hp as [_ Hpp]. rewrite NF1 in Hpp.
        unfold sh1 in *. rewrite ?DP in *. unfold ff1, fl1 in *.
        split; (eapply stk_agree_eq; [| eassumption]); intros a Ha; (apply AG; [lia|]); apply OUTW; lia.
      - destruct Hp as [Hc Hpp]. assert (cid = 0) by lia. subst cid. rewrite NF0 in Hpp.
        assert (FB : fs_frame_bytes 0 = 64) by reflexivity. rewrite FB in *.
        destruct (HW 0 p (conj Hc Hpp)) as [W1 W2]. rewrite FB in W1, W2.
        unfold fs_frame_addr, fs_frames_base, kFsFlagsOffset, kFsLog, kFsMinFrameLog, fs_shadow, FS_SB in *.
        cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add] in W1, W2 |- *.
        unfold sh1 in *. rewrite ?DP in *. unfold ff1, fl1 in *.
        split; (eapply stk_agree_eq; [| eassumption]); intros a Ha; (apply AG; [lia|]); apply OUTW; try lia.
        all: Z.div_mod_to_equations; lia. }
    split.
    { constructor; [| exact ND]. intros Hin. apply lf_mem_In in Hin. congruence. }
    intros N ff [EQ|Hin]; [| exact (HLF N ff Hin)]. injection EQ as <- <-. exists pos. split; [exact KP| reflexivity].
  Qed.
End Alloc1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff0 (fsbase pos : Z) : Z := fsbase + 36864 + 64 * pos.
Definition fl0 (fsbase pos : Z) : Z := fsbase + 4096 + pos.
Definition sh0 (fsbase pos : Z) : Z := 2147450880 + ff0 fsbase pos / 8.

Lemma ff0_eq : forall fsbase pos, fs_frame_addr fsbase 0 pos = ff0 fsbase pos.
Proof. aceil. intros. unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, kFsFlagsOffset, kFsLog, kFsMinFrameLog, ff0. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add]. lia. Qed.
Lemma fl0_eq : forall fsbase pos, fs_flag_addr fsbase 0 pos = fl0 fsbase pos.
Proof. aceil. intros. unfold fs_flag_addr, fs_flags_base, fs_flags_off, fs_nframes, kFsFlagsOffset, kFsLog, kFsMinFrameLog, fl0. cbn. lia. Qed.
Lemma sh0_eq : forall fsbase pos, fs_shadow (fs_frame_addr fsbase 0 pos) = sh0 fsbase pos.
Proof. aceil. intros. unfold fs_shadow, FS_SB, sh0. rewrite ff0_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition sm0_W (sp : word) (fsbase pos : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 208, bv_unsigned sp); (fsbase, fsbase + 8);
   (fl0 fsbase pos, fl0 fsbase pos + 1); (ff0 fsbase pos, ff0 fsbase pos + 64); (sh0 fsbase pos, sh0 fsbase pos + 8)].

Section Alloc0.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Lemma FSRep_alloc0 : forall E fsbase fs fs' LF m m' (sp : word) pos (hv v w : word) j1 j2,
    FSRep segs E fsbase fs LF m -> fs_pos_ok 0 pos ->
    lf_mem LF 0 (fs_frame_addr fsbase 0 pos) = false ->
    alloc_ceiling <= bv_unsigned sp - 208 ->
    munch (sm0_W sp fsbase pos) m m' -> wmono segs m m' ->
    rw_cells segs m' fsbase [C8 hv] ->
    rw_cells segs m' (fl0 fsbase pos) [C1 (Z_to_bv 8 1)] ->
    rw_cells segs m' (ff0 fsbase pos) [CB 24 j1; C8 v; CB 24 j2; C8 w] ->
    rw_cells segs m' (sh0 fsbase pos) [C8 (Z_to_bv 64 0)] ->
    FSRep segs E fsbase fs' ((0, fs_frame_addr fsbase 0 pos) :: LF) m'.
  Proof. aceil.
    intros E fsbase fs fs' LF m m' sp pos hv v w j1 j2 FS KP FRESH CEIL MU WV HI FLp FRp SHp.
    pose proof FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
    pose proof G4 as G4'. unfold FS_SB, kFsBytes in G4'. unfold kFsBytes in G3. aceil.
    destruct (proj1 (Z.mod_divide fsbase 8 ltac:(lia)) ltac:(Z.div_mod_to_equations; lia)) as [q Q8].
    assert (DP : forall p, ff0 fsbase p / 8 = q + 4608 + 8 * p) by (intros; unfold ff0; rewrite Q8; Z.div_mod_to_equations; lia).
    assert (NF1 : fs_nframes 1 = 8192) by reflexivity. assert (NF0 : fs_nframes 0 = 16384) by reflexivity.
    pose proof KP as [_ KPr]. rewrite NF0 in KPr.
    (* [comment removed for export] *)
    assert (AG : forall a, 0 <= a < 2^64 -> outside (sm0_W sp fsbase pos) a ->
              m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)).
    { intros a Ha Ho. split; [| apply WV]. apply MU. rewrite wa_unsigned by lia. exact Ho. }
    assert (OUTW : forall a, (fsbase <= a < fsbase + 11571200 \/ 2147450880 + q <= a < 2147450880 + q + 1446400 + 1) ->
              ~ (fsbase <= a < fsbase + 8) -> a <> fl0 fsbase pos ->
              ~ (ff0 fsbase pos <= a < ff0 fsbase pos + 64) -> ~ (sh0 fsbase pos <= a < sh0 fsbase pos + 8) ->
              outside (sm0_W sp fsbase pos) a).
    { intros a Ha N1 N2 N3 N4. unfold sm0_W, outside. unfold sh0 in *. rewrite !DP in *. unfold fl0, ff0 in *.
      repeat split; first [lia | Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (FLR : forall c p, fs_pos_ok c p -> fsbase + 4096 <= fs_flag_addr fsbase c p < fsbase + 4096 + 2^15).
    { intros c p [Hc Hp]. unfold fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset.
      assert (C : c = 0 \/ c = 1) by lia. destruct C as [-> | ->]; cbn [Z.eqb]; rewrite ?NF0, ?NF1 in *; lia. }
    assert (FRR : forall c p, fs_pos_ok c p -> fsbase + 4096 + 2^15 <= fs_frame_addr fsbase c p /\ fs_frame_addr fsbase c p + fs_frame_bytes c <= fsbase + 11571200
                /\ 0 < fs_frame_bytes c).
    { intros c p [Hc Hp]. unfold fs_frame_addr, fs_frames_base, fs_frame_bytes, kFsFlagsOffset, kFsLog, kFsMinFrameLog.
      assert (C : c = 0 \/ c = 1) by lia. destruct C as [-> | ->]; rewrite ?NF0, ?NF1 in *; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add]; lia. }
    split; [exact G1|]. split; [exact G2|]. split; [unfold kFsBytes; aceil; lia|]. split; [exact G4|].
    split.
    { (* [comment removed for export] *) intros cid Hc. destruct (Z.eq_dec cid 0) as [->|NE0]; [exists hv; rewrite Z.mul_0_r, Z.add_0_r; exact HI|].
      destruct (HH cid Hc) as [h Hh]. exists h. eapply rw_cells_agree_eq; [| exact Hh]. cbn. intros a Ha. apply AG; [unfold kFsClasses in Hc; lia|].
      apply OUTW; unfold sh0 in *; rewrite ?DP in *; unfold fl0, ff0, kFsClasses in *; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HL]. cbn. intros a Ha. apply AG; [lia|]. apply OUTW; unfold sh0 in *; rewrite ?DP in *; unfold fl0, ff0 in *; lia. }
    split. { eapply rw_cells_agree_eq; [| exact HG]. cbn. intros a Ha. apply AG; [lia|]. apply OUTW; unfold sh0 in *; rewrite ?DP in *; unfold fl0, ff0 in *; lia. }
    split.
    { (* [comment removed for export] *) intros cid p Hp.
      assert (NEWFB : forall c' p', fs_pos_ok c' p' -> (c', p') <> (0, pos) ->
                flag_byte ((0, fs_frame_addr fsbase 0 pos) :: LF) fsbase c' p' = flag_byte LF fsbase c' p').
      { intros c' p' Hp' NE. unfold flag_byte, lf_mem. cbn [existsb fst snd].
        destruct (Z.eqb_spec 0 c') as [<-|Hc]; cbn [andb]; [| reflexivity].
        destruct (Z.eqb_spec (fs_frame_addr fsbase 0 pos) (fs_frame_addr fsbase 0 p')) as [EQ|Hf]; cbn [orb]; [| reflexivity].
        exfalso. destruct (fs_frame_addr_inj fsbase 0 pos 0 p' KP Hp' EQ) as [_ ->]. apply NE. reflexivity. }
      destruct (Z.eq_dec cid 0) as [->|NC].
      - destruct (Z.eq_dec p pos) as [->|NP].
        { unfold flag_byte, lf_mem. cbn [existsb fst snd]. rewrite !Z.eqb_refl. cbn. rewrite fl0_eq. exact FLp. }
        rewrite NEWFB by (try exact Hp; congruence).
        eapply rw_cells_agree_eq; [| exact (HF 0 p Hp)]. cbn. intros a Ha. pose proof (FLR 0 p Hp).
        rewrite fl0_eq in Ha. unfold fl0 in Ha. destruct Hp as [_ Hpp]. rewrite NF0 in Hpp. apply AG; [lia|].
        apply OUTW; unfold sh0 in *; rewrite ?DP in *; unfold fl0, ff0 in *; lia.
      - rewrite NEWFB by (try exact Hp; congruence).
        eapply rw_cells_agree_eq; [| exact (HF cid p Hp)]. cbn. intros a Ha. pose proof (FLR cid p Hp).
        destruct Hp as [Hc Hpp]. assert (cid = 1) by lia. subst cid. rewrite NF1 in Hpp.
        unfold fs_flag_addr, fs_flags_base, fs_flags_off, kFsFlagsOffset in Ha. cbn [Z.eqb] in Ha. rewrite NF0 in Ha.
        apply AG; [lia|]. apply OUTW; unfold sh0 in *; rewrite ?DP in *; unfold fl0, ff0 in *; lia. }
    split.
    { (* [comment removed for export] *) intros cid p Hp. pose proof (FRR cid p Hp) as (R1 & R2 & R3).
      destruct (Z.eq_dec cid 0) as [->|NC].
      - assert (FB : fs_frame_bytes 0 = 64) by reflexivity. rewrite FB in *. rewrite sh0_eq, ff0_eq.
        destruct (Z.eq_dec p pos) as [->|NP].
        { split; [| change (64 / 8) with 8].
          - pose proof (stk_of_rw_cells segs m' _ _ FRp) as X. cbn in X. exact X.
          - pose proof (stk_of_rw_cells segs m' _ _ SHp) as X. cbn in X. exact X. }
        destruct (HW 0 p Hp) as [W1 W2]. rewrite ?FB in W1, W2. rewrite sh0_eq in W2. rewrite ff0_eq in W1. change (64 / 8) with 8 in W2 |- *.
        assert (pos + 1 <= p \/ p + 1 <= pos) by lia.
        destruct Hp as [_ Hpp]. rewrite NF0 in Hpp.
        unfold sh0 in *. rewrite ?DP in *. unfold ff0, fl0 in *.
        split; (eapply stk_agree_eq; [| eassumption]); intros a Ha; (apply AG; [lia|]); apply OUTW; lia.
      - destruct Hp as [Hc Hpp]. assert (cid = 1) by lia. subst cid. rewrite NF1 in Hpp.
        assert (FB : fs_frame_bytes 1 = 128) by reflexivity. rewrite FB in *.
        destruct (HW 1 p (conj Hc Hpp)) as [W1 W2]. rewrite FB in W1, W2.
        unfold fs_frame_addr, fs_frames_base, kFsFlagsOffset, kFsLog, kFsMinFrameLog, fs_shadow, FS_SB in *.
        cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add Z.sub Pos.add] in W1, W2 |- *.
        unfold sh0 in *. rewrite ?DP in *. unfold ff0, fl0 in *.
        split; (eapply stk_agree_eq; [| eassumption]); intros a Ha; (apply AG; [lia|]); apply OUTW; try lia.
        all: Z.div_mod_to_equations; lia. }
    split.
    { constructor; [| exact ND]. intros Hin. apply lf_mem_In in Hin. congruence. }
    intros N ff [EQ|Hin]; [| exact (HLF N ff Hin)]. injection EQ as <- <-. exists pos. split; [exact KP| reflexivity].
  Qed.
End Alloc0.
End RC__1.
