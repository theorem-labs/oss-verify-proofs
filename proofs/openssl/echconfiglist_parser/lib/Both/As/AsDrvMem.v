(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame HeapCeil SymExec2 SymExec2Sound SymRun RefPrintfLib MemSplit LibTail MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsPrintfFirst.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amem_grows_wmono : forall m m', mem_grows m m' -> wmono asegs m m'.
Proof.
  intros m m' Hg x Hw. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - assert (m' x <> None) as H' by (apply Hg; congruence). destruct (m' x); [discriminate|contradiction].
  - destruct (m' x); [discriminate|]. exact Hw.
Qed.
Lemma aframe_mod_wmono : forall m m' rs, frame_mod m m' rs -> wmono asegs m m'.
Proof. intros m m' rs [_ Hg]. apply amem_grows_wmono. exact Hg. Qed.

Lemma find_segment_asegs : forall (x : Z),
  find_segment asegs x 1 =
    if ((0x10000 <=? x) && (x + 1 <=? 0x195000))%Z then Some AsanUbsan.AsanUbsan_segment_000
    else if ((0x195000 <=? x) && (x + 1 <=? 0x571000))%Z then Some AsanUbsan.AsanUbsan_segment_001
    else if ((0x571000 <=? x) && (x + 1 <=? 0x5ea000))%Z then Some AsanUbsan.AsanUbsan_segment_002
    else if ((0x5ea000 <=? x) && (x + 1 <=? 0xc04000))%Z then Some AsanUbsan.AsanUbsan_segment_003
    else None.
Proof. intros x. reflexivity. Qed.

Lemma aro_addr_true : forall (a : word), 0x10000 <= bv_unsigned a < 0x571000 -> ro_addr asegs a = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x195000); cbn [andb]; [reflexivity| | lia | lia].
  destruct (Z.leb_spec 0x195000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x571000); cbn [andb]; [reflexivity| lia | lia | lia].
Qed.

Lemma aro_addr_false : forall (a : word), (bv_unsigned a < 0x10000 \/ 0x571000 <= bv_unsigned a) -> ro_addr asegs a = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x195000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x195000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x571000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x571000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x5ea000); cbn [andb]; try lia; try reflexivity;
  destruct (Z.leb_spec 0x5ea000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xc04000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_ro_none : forall m, mem_inv asegs m -> forall i, 0x10000 <= i < 0x195000 -> m (Z_to_bv 64 i) = None.
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite aro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_text_none : forall m, mem_inv asegs m -> forall i, 0x195000 <= i < 0x571000 -> m (Z_to_bv 64 i) = None.
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite aro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_frame : forall m m' rs,
  mem_inv asegs m -> frame_mod m m' rs ->
  Forall (fun r => bv_unsigned (fst r) + snd r <= 2 ^ 64 /\ (bv_unsigned (fst r) + snd r <= 0x10000 \/ 0x571000 <= bv_unsigned (fst r))) rs ->
  mem_inv asegs m'.
Proof.
  intros m m' rs Hinv [Hout Hg] Hrs a b Hab.
  destruct (ro_addr asegs a) eqn:Ero; [|reflexivity]. exfalso.
  assert (Hcase : OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Frame.outside a rs \/ (bv_unsigned a < 0x10000 \/ 0x571000 <= bv_unsigned a)).
  { clear Hab Ero Hout Hg Hinv. induction rs as [|[r n] rs IH]; [left; exact I|].
    inversion Hrs as [|x l [Hnw Hr] Hl]; subst. cbn [fst snd] in Hnw, Hr.
    destruct (IH Hl) as [Ho|Hx]; [|right; exact Hx].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r)) as [Hlt|Hge]; [left; cbn; split; [unfold in_rng; lia|exact Ho]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r + n)) as [Hin|Hout']; [|left; cbn; split; [unfold in_rng; lia|exact Ho]].
    right. lia. }
  destruct Hcase as [Ho|Hx].
  - rewrite (Hout a Ho) in Hab. pose proof (Hinv a b Hab). congruence.
  - rewrite aro_addr_false in Ero by exact Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_wbytes_high : forall m (A : Z) bs,
  mem_inv asegs m -> AIMG_TOP <= A -> A < 2 ^ 64 -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  mem_inv asegs (wbytes m (Z_to_bv 64 A) bs).
Proof.
  intros m A bs Hinv HA HA64 Hl a b Hab. pose proof (u64_range a) as Ha. unfold AIMG_TOP in HA.
  destruct (Z_lt_le_dec (bv_unsigned a) A) as [Hlt|Hge].
  - rewrite wbytes_below in Hab by (rewrite ?u_small by lia; lia). exact (Hinv a b Hab).
  - destruct (Z_lt_le_dec (bv_unsigned a) (A + Z.of_nat (length bs))) as [Hin|Hout].
    + apply aro_addr_false. lia.
    + rewrite wbytes_above in Hab by (rewrite u_small by lia; lia). exact (Hinv a b Hab).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma astore_ok_of_wview : forall m (n : nat) (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64) ->
  (forall i, 0 <= i < Z.of_nat n -> wview asegs m (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  store_ok RSEGS m a n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hn Hw; [reflexivity|].
  cbn [store_ok]. pose proof (u64_range a) as Ha.
  assert (W0 : wview asegs m a <> None).
  { pose proof (Hw 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0. }
  unfold asegs, RefMemImage.Ref.loaded_segments in W0.
  destruct (wview RSEGS m a); [|contradiction].
  apply IH; [rewrite u_add1 by lia; lia|]. intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hw. lia.
Qed.

Lemma astk_stk_ok : forall m lo hi (sp : word) K,
  stk asegs m lo hi -> lo <= bv_unsigned sp - K -> bv_unsigned sp <= hi -> 0 <= K -> hi < 2 ^ 64 ->
  stk_ok RSEGS m sp K.
Proof.
  intros m lo hi sp K (H1 & H2 & H) Hlo Hhi HK Hhi2 a n Ha Hn. pose proof (u64_range a).
  apply astore_ok_of_wview; [lia|]. intros i Hi. rewrite <- wa_eq. apply (H (bv_unsigned a + i)). lia.
Qed.

Lemma aseg_rom_high : forall x : word, 0xc04000 <= bv_unsigned x -> seg_rom RSEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  change AsanUbsan.M.loaded_segments with asegs. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x195000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x195000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x571000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x571000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x5ea000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x5ea000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0xc04000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma astk_grows : forall m m' l h, stk asegs m l h -> 0xc04000 <= l -> h <= 2 ^ 64 -> mem_grows m m' -> stk asegs m' l h.
Proof.
  intros m m' l h (S1 & S2 & S3) Hl Hh Hg. split; [exact S1|]. split; [exact S2|].
  intros x Hx. destruct (S3 x Hx) as [Hw [b Hb]].
  assert (E0 : exists b0, m (wa x) = Some b0).
  { unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E; [exists b0; reflexivity|].
    rewrite seg_rom_same in Hb. change asegs with RSEGS in Hb.
    rewrite aseg_rom_high in Hb; [discriminate|]. rewrite wa_eq, u_small by lia. lia. }
  destruct E0 as [b0 E0].
  assert (E1 : exists b1, m' (wa x) = Some b1).
  { destruct (m' (wa x)) as [b1|] eqn:E; [exists b1; reflexivity|]. exfalso. apply (Hg (wa x)); congruence. }
  destruct E1 as [b1 E1]. split.
  - unfold wview. rewrite E1. discriminate.
  - exists b1. unfold mrd. rewrite E1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acells_ok_frame : forall m m' rs cs,
  forallb cell_wf_b cs = true -> cells_ok m cs -> frame_mod m m' rs ->
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall r, In r rs ->
     a + Z.of_nat w <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a end) cs ->
  cells_ok m' cs.
Proof.
  intros m m' rs cs Hwf Hc FM Hd. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_ok in *. rewrite <- Hok. apply (frame_mod_rdn RSEGS m m' rs w (Z_to_bv 64 a) FM); rewrite u_small by lia; [|lia].
  intros i Hi. apply outside_of_disjoint. intros r0 Hr0. pose proof (Hx r0 Hr0) as D. rewrite u_small by lia. lia.
Qed.

Lemma arange_none_frame : forall m m' rs lo hi,
  (forall i, lo <= i < hi -> m (Z_to_bv 64 i) = None) -> frame_mod m m' rs ->
  (forall r, In r rs -> hi <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= lo) -> 0 <= lo -> hi <= 2 ^ 64 ->
  forall i, lo <= i < hi -> m' (Z_to_bv 64 i) = None.
Proof.
  intros m m' rs lo hi Hn [Hout _] Hrs Hlo Hhi i Hi. rewrite Hout; [apply Hn; exact Hi|].
  apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.
(* [comment removed for export] *)
Lemma arange_none_frame_hole : forall m m' rs lo hi hlo hhi,
  (forall i, lo <= i < hi /\ ~ (hlo <= i < hhi) -> m (Z_to_bv 64 i) = None) -> frame_mod m m' rs ->
  (forall r, In r rs -> hi <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= lo) -> 0 <= lo -> hi <= 2 ^ 64 ->
  forall i, lo <= i < hi /\ ~ (hlo <= i < hhi) -> m' (Z_to_bv 64 i) = None.
Proof.
  intros m m' rs lo hi hlo hhi Hn [Hout _] Hrs Hlo Hhi i Hi. rewrite Hout; [apply Hn; exact Hi|].
  apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.

Lemma ardn_frame : forall m m' rs (a : Z) n bs,
  frame_mod m m' rs -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall r, In r rs -> a + Z.of_nat n <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a) ->
  rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros m m' rs a n bs FM HD Ha Hn Hrs. rewrite <- HD.
  apply (frame_mod_rdn RSEGS m m' rs n (Z_to_bv 64 a) FM); rewrite u_small by lia; [|lia].
  intros i Hi. apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.

(* [comment removed for export] *)
Lemma arw_cells_frame : forall m m' rs A cs,
  rw_cells asegs m A cs -> frame_mod m m' rs ->
  (forall r, In r rs -> A + Z.of_nat (cells_size cs) <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= A) ->
  rw_cells asegs m' A cs.
Proof.
  intros m m' rs A cs RC FM Hrs.
  eapply rw_cells_transport; [exact RC | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
  clear RC FM. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
  - destruct (Hrs (r, k) (or_introl eq_refl)); cbn [fst snd] in *; lia.
  - apply IH. intros r' Hr'. apply Hrs. right. exact Hr'.
Qed.
