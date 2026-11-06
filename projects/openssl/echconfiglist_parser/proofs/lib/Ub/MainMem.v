(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec StoreOk AgentLib Frame SymExec2 SymExec2Sound SymRun SymDrive MemSplit UbLibDiagKn LibTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import MainDefs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Image.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma rsegs_eq : usegs = RSEGS. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma seg_rom_same : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.seg_rom = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.seg_rom.
Proof. reflexivity. Qed.
Lemma rdn_same : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.rdn.
Proof. reflexivity. Qed.
Lemma getr_same : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.getr = OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.getr.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wbytes_eq : forall bs m a, wbytes m a bs = write_to_mem m a bs.
Proof. induction bs as [|b bs IH]; intros m a; cbn; [reflexivity | apply IH]. Qed.

Lemma wa_eq : forall z, wa z = Z_to_bv 64 z. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivls (rs : list (word * Z)) : list ivl := map (fun r => (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)) rs.

Lemma outside_ivls : forall rs (x : word), Lib.Frame.outside (ivls rs) (bv_unsigned x) -> OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Frame.outside x rs.
Proof.
  induction rs as [|[b n] rs IH]; intros x H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [|apply IH; exact H2]. unfold in_rng. lia.
Qed.

Lemma frame_mod_munch : forall m m' rs, frame_mod m m' rs -> munch (ivls rs) m m'.
Proof. intros m m' rs [H _] x Hx. apply H. apply outside_ivls. exact Hx. Qed.

Lemma mem_grows_wmono : forall m m', mem_grows m m' -> wmono usegs m m'.
Proof.
  intros m m' Hg x Hw. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - assert (m' x <> None) as H' by (apply Hg; congruence). destruct (m' x); [discriminate|contradiction].
  - destruct (m' x); [discriminate|]. exact Hw.
Qed.

Lemma frame_mod_wmono : forall m m' rs, frame_mod m m' rs -> wmono usegs m m'.
Proof. intros m m' rs [_ Hg]. apply mem_grows_wmono. exact Hg. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma store_ok_of_wview : forall m (n : nat) (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64) ->
  (forall i, 0 <= i < Z.of_nat n -> wview RSEGS m (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  store_ok RSEGS m a n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hn Hw; [reflexivity|].
  cbn [store_ok]. pose proof (u64_range a) as Ha.
  assert (W0 : wview RSEGS m a <> None).
  { pose proof (Hw 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0. }
  destruct (wview RSEGS m a); [|contradiction].
  apply IH; [rewrite u_add1 by lia; lia|]. intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hw. lia.
Qed.

Lemma stk_stk_ok : forall m lo hi (sp : word) K,
  stk usegs m lo hi -> lo <= bv_unsigned sp - K -> bv_unsigned sp <= hi -> 0 <= K -> hi < 2 ^ 64 ->
  stk_ok RSEGS m sp K.
Proof.
  intros m lo hi sp K (H1 & H2 & H) Hlo Hhi HK Hhi2 a n Ha Hn. pose proof (u64_range a).
  apply store_ok_of_wview; [lia|]. intros i Hi. rewrite <- wa_eq. apply (H (bv_unsigned a + i)). lia.
Qed.

Lemma wr_at_store_ok : forall m A n (k : Z) (j : nat),
  wr_at usegs m A n -> 0 <= k -> k + Z.of_nat j <= n -> A + n < 2 ^ 64 ->
  store_ok RSEGS m (Z_to_bv 64 (A + k)) j = true.
Proof.
  intros m A n k j (H1 & H2 & H) Hk Hj HAn. apply store_ok_of_wview; [rewrite u_small by lia; lia|].
  intros i Hi. rewrite u_small by lia. rewrite <- wa_eq. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_rsegs : forall (x : Z),
  find_segment usegs x 1 =
    if ((0x10000 <=? x) && (x + 1 <=? 0xe2000))%Z then Some Ubsan.Ubsan_segment_000
    else if ((0xe2000 <=? x) && (x + 1 <=? 0x2c5000))%Z then Some Ubsan.Ubsan_segment_001
    else if ((0x2c5000 <=? x) && (x + 1 <=? 0x322000))%Z then Some Ubsan.Ubsan_segment_002
    else if ((0x322000 <=? x) && (x + 1 <=? 0x358000))%Z then Some Ubsan.Ubsan_segment_003
    else None.
Proof. intros x. reflexivity. Qed.

Lemma ro_addr_true : forall (a : word), 0x10000 <= bv_unsigned a < 0x2c5000 -> ro_addr usegs a = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_rsegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xe2000); cbn [andb]; [reflexivity| | lia | lia].
  destruct (Z.leb_spec 0xe2000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x2c5000); cbn [andb]; [reflexivity| lia | lia | lia].
Qed.

Lemma ro_addr_false : forall (a : word), (bv_unsigned a < 0x10000 \/ 0x2c5000 <= bv_unsigned a) -> ro_addr usegs a = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_rsegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xe2000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0xe2000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x2c5000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x2c5000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x322000); cbn [andb]; try lia; try reflexivity;
  destruct (Z.leb_spec 0x322000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x358000); cbn [andb]; try lia; reflexivity.
Qed.

Lemma mem_inv_ro_none : forall m, mem_inv usegs m -> ro_none m.
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite ro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_inv_frame : forall m m' rs,
  mem_inv usegs m -> frame_mod m m' rs ->
  Forall (fun r => bv_unsigned (fst r) + snd r <= 2 ^ 64 /\ (bv_unsigned (fst r) + snd r <= 0x10000 \/ 0x2c5000 <= bv_unsigned (fst r))) rs ->
  mem_inv usegs m'.
Proof.
  intros m m' rs Hinv [Hout Hg] Hrs a b Hab.
  destruct (ro_addr usegs a) eqn:Ero; [|reflexivity]. exfalso.
  assert (Hcase : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Frame.outside a rs \/ (bv_unsigned a < 0x10000 \/ 0x2c5000 <= bv_unsigned a)).
  { clear Hab Ero Hout Hg Hinv. induction rs as [|[r n] rs IH]; [left; exact I|].
    inversion Hrs as [|x l [Hnw Hr] Hl]; subst. cbn [fst snd] in Hnw, Hr.
    destruct (IH Hl) as [Ho|Hx]; [|right; exact Hx].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r)) as [Hlt|Hge]; [left; cbn; split; [unfold in_rng; lia|exact Ho]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r + n)) as [Hin|Hout']; [|left; cbn; split; [unfold in_rng; lia|exact Ho]].
    right. lia. }
  destruct Hcase as [Ho|Hx].
  - rewrite (Hout a Ho) in Hab. pose proof (Hinv a b Hab). congruence.
  - rewrite ro_addr_false in Ero by exact Hx. discriminate.
Qed.

(* [comment removed for export] *)
Section HCW.
Context {HCEIL : HeapCeil}.
Lemma mem_inv_wbytes_block : forall m A n (k : Z) bs,
  mem_inv usegs m -> rblock_range A n -> 0 <= k -> k + Z.of_nat (length bs) <= n ->
  mem_inv usegs (wbytes m (Z_to_bv 64 (A + k)) bs).
Proof.
  intros m A n k bs Hinv (R1 & R2 & R3 & R4 & R5) Hk Hl a b Hab. clear R2.
  pose proof (u64_range a) as Ha. hcb.
  destruct (Z_lt_le_dec (bv_unsigned a) (A + k)) as [Hlt|Hge].
  - rewrite wbytes_below in Hab by (rewrite ?u_small by lia; lia). exact (Hinv a b Hab).
  - destruct (Z_lt_le_dec (bv_unsigned a) (A + k + Z.of_nat (length bs))) as [Hin|Hout].
    + apply ro_addr_false. lia.
    + rewrite wbytes_above in Hab by (rewrite u_small by lia; lia). exact (Hinv a b Hab).
Qed.
End HCW.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outside_of_disjoint : forall (x : word) (rs : list (word * Z)),
  (forall r, In r rs -> bv_unsigned x < bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= bv_unsigned x) ->
  OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Frame.outside x rs.
Proof.
  intros x rs H. induction rs as [|[r n] rs IH]; [exact I|]. cbn. split.
  - pose proof (H (r, n) (or_introl eq_refl)) as H1. cbn [fst snd] in H1. unfold in_rng. lia.
  - apply IH. intros r' Hr'. apply H. right. exact Hr'.
Qed.

Lemma cells_ok_frame : forall m m' rs cs,
  forallb cell_wf_b cs = true -> cells_ok m cs -> frame_mod m m' rs ->
  Forall (fun c => match c with (a, w, _) => forall r, In r rs ->
     a + Z.of_nat w <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= a end) cs ->
  cells_ok m' cs.
Proof.
  intros m m' rs cs Hwf Hc [Hout _] Hd. eapply cells_ok_agree; [exact Hwf| |exact Hc].
  clear Hc. induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  intros i Hi. apply Hout. apply outside_of_disjoint. intros r0 Hr0.
  pose proof (Hx r0 Hr0) as D. rewrite u_small by lia. lia.
Qed.

Lemma rdn_frame : forall m m' rs (a : word) n bs,
  frame_mod m m' rs -> rdn RSEGS m a n = Some bs -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall r, In r rs -> bv_unsigned a + Z.of_nat n <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= bv_unsigned a) ->
  rdn RSEGS m' a n = Some bs.
Proof.
  intros m m' rs a n bs [Hout _] Hr Hnw Hd. rewrite (rdn_ext RSEGS n m' m a); [exact Hr | exact Hnw |].
  intros x Hx. apply Hout. apply outside_of_disjoint. intros r0 Hr0. pose proof (Hd r0 Hr0). lia.
Qed.

Lemma ro_none_frame : forall m m' rs,
  ro_none m -> frame_mod m m' rs ->
  (forall r, In r rs -> 0x2c5000 <= bv_unsigned (fst r)) -> ro_none m'.
Proof.
  intros m m' rs Hro [Hout _] Hd i Hi. rewrite Hout; [apply Hro; exact Hi|].
  apply outside_of_disjoint. intros r0 Hr0. pose proof (Hd r0 Hr0). rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : forall m (wad : word) bs (a : word) n v,
  rdn RSEGS m a n = Some v ->
  bv_unsigned wad + Z.of_nat (length bs) <= 2 ^ 64 -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned wad \/ bv_unsigned wad + Z.of_nat (length bs) <= bv_unsigned a) ->
  rdn RSEGS (wbytes m wad bs) a n = Some v.
Proof.
  intros m wad bs a n v Hr H1 H2 Hd. rewrite (rdn_ext RSEGS n (wbytes m wad bs) m a); [exact Hr | exact H2 |].
  intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma cells_ok_wbytes_out : forall m (wad : word) bs cs,
  forallb cell_wf_b cs = true -> cells_ok m cs -> bv_unsigned wad + Z.of_nat (length bs) <= 2 ^ 64 ->
  Forall (fun c => match c with (a, w, _) => a + Z.of_nat w <= bv_unsigned wad \/ bv_unsigned wad + Z.of_nat (length bs) <= a end) cs ->
  cells_ok (wbytes m wad bs) cs.
Proof.
  intros m wad bs cs Hwf Hc Hnw Hd. eapply cells_ok_agree; [exact Hwf| |exact Hc].
  clear Hc. induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  intros i Hi. apply wbytes_outside; rewrite ?u_small by lia; lia.
Qed.

Lemma ro_none_wbytes_out : forall m (wad : word) bs,
  ro_none m -> bv_unsigned wad + Z.of_nat (length bs) <= 2 ^ 64 ->
  (0x2c5000 <= bv_unsigned wad \/ bv_unsigned wad + Z.of_nat (length bs) <= 0x10000) ->
  ro_none (wbytes m wad bs).
Proof.
  intros m wad bs Hro Hnw Hd i Hi. rewrite wbytes_outside; [apply Hro; exact Hi | lia | rewrite u_small by lia; lia].
Qed.

(* [comment removed for export] *)
Lemma diag_cells_range : Forall (fun c => match c with (a, w, _) => 0x2c5c00 <= a /\ a + Z.of_nat w <= 0x356768 end) diag_cells.
Proof. unfold diag_cells. repeat constructor; cbn; lia. Qed.
Lemma pf1_cells_range : Forall (fun c => match c with (a, w, _) => 0x2c5c00 <= a /\ a + Z.of_nat w <= 0x356768 end) pf1_cells.
Proof. unfold pf1_cells. repeat constructor; cbn; lia. Qed.
Lemma pf1_cells_wf : forallb cell_wf_b pf1_cells = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Forall_cells_weaken : forall (P Q : Z * nat * Z -> Prop) cs,
  (forall a w v, P (a, w, v) -> Q (a, w, v)) -> Forall P cs -> Forall Q cs.
Proof. intros P Q cs H HP. eapply Forall_impl; [|exact HP]. intros [[a w] v]. apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_S : forall m (a : word) n bs,
  rdn RSEGS m a (S n) = Some bs ->
  exists b r, bs = b :: r /\ mrd usegs m a = Some b /\ rdn RSEGS m (a + 1)%bv n = Some r.
Proof.
  intros m a n bs H. change (rdn RSEGS) with (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn usegs) in H |- *.
  rewrite rdn_unfold in H. destruct (mrd usegs m a) as [b|]; [|discriminate].
  destruct (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn usegs m (a + 1)%bv n) as [r|]; [|discriminate].
  injection H as <-. exists b, r. auto.
Qed.

Lemma rdn_bytes_at : forall bs m (a : Z),
  rdn RSEGS m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at usegs m a bs.
Proof.
  induction bs as [|b bs IH]; intros m a H Ha Hn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in H, Hn. destruct (rdn_S m _ _ _ H) as (b' & r & E & Hm & Hr). injection E as <- <-.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. rewrite wa_eq. exact Hm.
    + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne].
      { cbn [length] in Hi. lia. }
      assert (IHr := IH m (a + 1)).
      assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
      { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
      rewrite Ea in Hr. specialize (IHr Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)).
      destruct IHr as (_ & _ & IH3). rewrite <- (IH3 i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_rw_any : forall m, exists e : word, rw_cells usegs m (0x336098 - 164) [C4 e].
Proof.
  intros m.
  assert (RD : forall i, 0 <= i < 4 -> exists b, mrd usegs m (wa (0x335ff4 + i)) = Some b).
  { intros i Hi. unfold mrd. destruct (m (wa (0x335ff4 + i))) as [b|]; [exists b; reflexivity|].
    rewrite seg_rom_same. change usegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; eexists; reflexivity. }
  destruct (RD 0 ltac:(lia)) as [b0 H0]. destruct (RD 1 ltac:(lia)) as [b1 H1].
  destruct (RD 2 ltac:(lia)) as [b2 H2]. destruct (RD 3 ltac:(lia)) as [b3 H3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split.
  - split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app].
    change (le4 ?v) with (word_to_le_bytes 4 v). rewrite word_to_le_bytes_of_lez by (reflexivity || (cbn; lia)).
    rewrite app_nil_r. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; [ | | | | lia].
    + rewrite Z.add_0_r in H0. exact H0. + exact H1. + exact H2. + exact H3.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    replace (0x336098 - 164 + i)%Z with (0x335ff4 + i)%Z by lia.
    unfold wview. destruct (m (wa (0x335ff4 + i))) as [b|]; [discriminate|].
    change usegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; discriminate.
Qed.
