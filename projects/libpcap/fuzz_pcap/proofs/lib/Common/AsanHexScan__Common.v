(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common.
From LinuxProcessSemantics.LinuxProcessSem Require Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Fs OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require MustExit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanHexScan.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
End AsanHexScan.

(* [comment removed for export] *)
Module AsanCeil.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.Footprint__Common.PlacementSearch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)














(* [comment removed for export] *)


(* [comment removed for export] *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(* [comment removed for export] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
End AsanCeil.

(* [comment removed for export] *)
Module AsanPlacement.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Footprint__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanCeil OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.Footprint__Common.PlacementSearch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fg_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. exact Hz.
Qed.

Lemma fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

Lemma fg_u64_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.

(* [comment removed for export] *)
Lemma page_multiple_eq : forall z, z mod page_size = 0 -> z = z / 4096 * 4096.
Proof.
  intros z Hz. unfold page_size in Hz.
  pose proof (Z.div_mod z 4096 ltac:(lia)). lia.
Qed.

Lemma fg_region_free_false : forall maps lo n,
  region_free maps lo n = false ->
  exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov).
    exists b', s'. split; [now right|exact Hov].
Qed.

(* [comment removed for export] *)
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_app : forall nZ l1 l2,
  gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2.
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

(* [comment removed for export] *)
Definition live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
  gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
  gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095)
  <= gap_weight nZ (List.filter (live_at c) l)
  /\ (length (List.filter (live_at c') l) < length (List.filter (live_at c) l))%nat.
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
  { intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gap.
  Variable L : list (word * word).
  Variable nZ : Z.
  Hypothesis HnZ : 0 <= nZ.

  (* [comment removed for export] *)
  Definition scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c
    /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.

  Definition gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ bottomup_floor <= c /\ c + nZ <= alloc_ceiling
    /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  

  

  (* [comment removed for export] *)
  
End Gap.

(* [comment removed for export] *)
Lemma gap_weight_bound : forall nZ N l,
  0 <= nZ ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  gap_weight nZ l <= Z.of_nat (length l) * (N + nZ + 4095).
Proof.
  intros nZ N l HnZ H. induction H as [|[b s] l Hs _ IH]; cbn -[Z.of_nat]; [lia|].
  cbn in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Fixpoint gw_sizes (l : list (word * word)) : Z :=
  match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.

Lemma gap_weight_sizes : forall nZ l,
  gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop :=
  forall b s, In (b, s) l -> bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b.

Lemma ledger_split_nil : forall K Y, ledger_split [] K Y.
Proof. intros K Y b s []. Qed.

Lemma ledger_split_mono : forall l K Y Y',
  ledger_split l K Y -> Y' <= Y -> ledger_split l K Y'.
Proof. intros l K Y Y' H HY b s Hin. destruct (H b s Hin); [left|right]; lia. Qed.

Lemma ledger_split_cons : forall l K Y b s,
  ledger_split l K Y ->
  bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b ->
  ledger_split ((b, s) :: l) K Y.
Proof.
  intros l K Y b s H Hbs b' s' [Heq|Hin]; [injection Heq as <- <-; exact Hbs|].
  exact (H b' s' Hin).
Qed.

Lemma ledger_split_app : forall l1 l2 K Y,
  ledger_split l1 K Y -> ledger_split l2 K Y -> ledger_split (l1 ++ l2) K Y.
Proof.
  intros l1 l2 K Y H1 H2 b s Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto.
Qed.

Lemma ledger_split_app_inv : forall l1 l2 K Y,
  ledger_split (l1 ++ l2) K Y -> ledger_split l1 K Y /\ ledger_split l2 K Y.
Proof.
  intros l1 l2 K Y H. split; intros b s Hin; apply H; apply in_app_iff; auto.
Qed.

(* [comment removed for export] *)
Lemma ledger_split_incl : forall l l' K Y,
  ledger_split l K Y -> incl l' l -> ledger_split l' K Y.
Proof. intros l l' K Y H Hincl b s Hin. apply H. apply Hincl. exact Hin. Qed.

Lemma ledger_split_filter : forall f l K Y,
  ledger_split l K Y -> ledger_split (List.filter f l) K Y.
Proof.
  intros f l K Y H. apply (ledger_split_incl l); [exact H|].
  intros x Hx. apply filter_In in Hx. tauto.
Qed.

(* [comment removed for export] *)
Lemma ledger_split_window_free : forall l K Y nZ,
  0 <= K -> 0 < nZ -> K + 2 * nZ <= Y -> Y < 2 ^ 64 ->
  ledger_split l K Y ->
  region_free l (Z_to_bv 64 (Y - nZ)) (Z_to_bv 64 nZ) = true.
Proof.
  intros l K Y nZ HK HnZ HY HY64 Hsplit.
  apply region_free_intro. intros b s Hin.
  unfold iv_overlap. rewrite !fg_u64_lit by lia.
  pose proof (bv_unsigned_in_range 64 s).
  destruct (Hsplit b s Hin) as [Hlow|Hhigh].
  - apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition kHighMemBeg : Z := 0x10007fff8000.

Lemma kHighMemBeg_below_mmap_base_min :
  kHighMemBeg + 0x544d555f000 = mmap_base_min /\ mmap_base_min < bottomup_floor.
Proof. unfold kHighMemBeg, mmap_base_min. rewrite bottomup_floor_val. split; reflexivity. Qed.

(* [comment removed for export] *)

End AsanPlacement.

(* [comment removed for export] *)
Module SimInv.
(* [comment removed for export] *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(* [comment removed for export] *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

(* [comment removed for export] *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
  cofix CH. intros c HInv.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
    + intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.

(* [comment removed for export] *)
Lemma no_error_run_corun :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
  apply no_error_coexec, H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_error_run_modeled :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H.
  apply modeled_iff. cbn [img_segments].
  eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.
End SimInv.

(* [comment removed for export] *)
Module ExitSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.SimInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

#[using="Type"] Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
  induction fuel as [|fuel IH]; intros ms H; [discriminate|].
  cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in H as [Hx8 Hgpr].
    apply bv_eqb_eq in Hgpr.
    eapply te_here; eauto.
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left|right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    eapply te_step; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma sim_step : forall fuel ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sim_c fuel ms' = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms ms' Hsvc Hstep Hrec.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sim_c_exit_now : forall fuel ms x8,
  ms_svc_pending ms = Some x8 ->
  ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms x8 Hsvc Hx8 Hcode.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sim_ecall_exit : forall fuel ms,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some 0x73 ->
  ((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S (S fuel)) ms = true.
Proof.
  intros fuel ms Hsvc Hfetch Hcheck Hcode.
  set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  apply (sim_step (S fuel) ms ms1 Hsvc).
  - change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
    unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
  - apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
    + subst ms1. reflexivity.
    + exact Hcheck.
    + exact Hcode.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

#[using="Type"] Lemma to_exit_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* [comment removed for export] *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_exit_star_only : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
  intros ms model Hh Hlazy Hte tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
    as (tr' & o & _ & HQ).
  unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
  destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.

#[using="Type"] Lemma to_exit_star_admits : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  exists c, star segs (mkCfg ms model)
              [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
  intros ms model Hh Hlazy Hte.
  destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

#[using="Type"] Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* [comment removed for export] *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* [comment removed for export] *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* [comment removed for export] *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

#[using="Type"] Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.

#[using="Type"] Lemma to_exit_no_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
  (i < length bytes)%nat ->
  bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
  stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
  intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
  destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
  2: { apply Z.leb_gt in E1; lia. }
  replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
  destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma build_stack_starts_with_argc :
  forall ph sp argv envp uid hw rnd,
  exists rest,
    build_stack_bytes ph sp argv envp uid hw rnd =
    word_le8 (nat_to_word (length argv)) ++ rest.
Proof.
  intros ph sp argv envp uid hw rnd. unfold build_stack_bytes, len_word, nat_to_word.
  destruct (string_addrs _ argv) as [? ?]. destruct (string_addrs _ envp) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.

Lemma build_stack_min_length : forall ph sp argv envp uid hw rnd,
  (8 <= length (build_stack_bytes ph sp argv envp uid hw rnd))%nat.
Proof.
  intros ph sp argv envp uid hw rnd.
  destruct (build_stack_starts_with_argc ph sp argv envp uid hw rnd) as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(* [comment removed for export] *)
Lemma init_first8 :
  forall segs init_pc ph init_sp init_rnd argv envp addr i uid hw, (i < 8)%nat ->
  bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
  ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr =
  nth_error (word_le8 (nat_to_word (length argv))) i.
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp addr i uid hw Hi Haddr.
  assert (Hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length argv))) i).
  { rewrite stack_to_mem_image_in_block
      by (pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd);
          unfold entry_block_top; lia).
    rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr)
    with (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (bv_unsigned init_sp - stack_max_size)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length argv))) i) eqn:E; [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay :
  forall segs init_pc ph init_sp init_rnd argv envp uid hw,
  ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) =
  overlay_argc_bytes init_sp (length argv)
    (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)).
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : forall ms : machine_state,
  ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
          ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
          ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argc : nat)
    (base : word -> option byte) (uid : word)
    (hw : word) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.

(* [comment removed for export] *)
Lemma init_eq_enum_state :
  forall segs init_pc ph init_sp init_rnd argv envp uid hw,
  init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw =
  enum_state segs init_pc ph init_sp init_rnd (length argv)
    (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) uid hw.
Proof.
  intros segs init_pc ph init_sp init_rnd argv envp uid hw. unfold enum_state.
  rewrite (machine_state_eta (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (exit_post code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec segs code
           (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
           (init_model (segments_reserved segs) brk0 mb sp lim inp)
           eq_refl eq_refl (sim_c_to_exit segs code F _ Hsim)).
Qed.

Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
  sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = bv_and code (Z_to_bv 64 255).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma exit_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
  sim_c source_segs code FR
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  sim_c target_segs code FA
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(* [comment removed for export] *)
Lemma exit_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
  sim_c source_segs code FR
    (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  sim_c target_segs code FA
    (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
End ExitSim.
