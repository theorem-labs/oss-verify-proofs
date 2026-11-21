(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  StartupTac ArgvEnv RefLayout RefStartupDefs RefStartup RefMemcpyLib RefStartup4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* LPS 75d69e00: written explicitly over the ProcInput (was zQ statements + KReplay terms).
   Definitions and constants are boost-json's own (decoded old text: D_main_cells,
   D_main_missb bound 1232896, tid 1095184, guard 1226488; plain old text for pagesize/self/
   canary/hwcap); proofs follow boost-beast's RefStartupFacts (a donor branch, not compiled by
   me, rule 15), with boost-json's D_cxx and in_hwcap. *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Plain.M.phdrs.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition D_main_cells : list (Z * nat) :=
  [(1095144%Z, 8%nat); (1227088%Z, 8%nat); (1227184%Z, 8%nat); (1227128%Z, 8%nat); (1227072%Z, 8%nat); (1227064%Z, 8%nat); (1226464%Z, 8%nat); (1226480%Z, 8%nat); (1226472%Z, 8%nat); (1227104%Z, 8%nat); (1227112%Z, 8%nat); (1095368%Z, 8%nat); (1095344%Z, 8%nat); (1095152%Z, 8%nat); (1227080%Z, 1%nat); (1095192%Z, 4%nat); (1095184%Z, 4%nat); (1095304%Z, 8%nat); (1095272%Z, 8%nat); (1095160%Z, 8%nat); (1095168%Z, 8%nat); (1095176%Z, 8%nat); (1226488%Z, 4%nat); (1226492%Z, 4%nat); (1226489%Z, 1%nat); (1095336%Z, 8%nat); (1022896%Z, 1%nat); (1089256%Z, 4%nat); (1088608%Z, 4%nat); (1088612%Z, 4%nat); (1088616%Z, 4%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 1232896)%Z.

Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
End FPX1.

Section Facts.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variable rnd : EntryDraw.
  Variable tid : word.
  Local Notation av := (in_argv inp) (only parsing).
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main inp sp0 rnd tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main inp sp0 rnd tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid).
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 1095184) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 1226488) 8 = Some (canary_bytes rnd).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    match goal with |- rdn _ (wbytes (wbytes (wbytes ?DD _ _) _ _) _ _) _ _ = _ =>
      exact (rd_guard8_gen rnd segs DD 1226488 [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3] [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]
               eq_refl eq_refl ltac:(lia) ltac:(lia)) end.
  Qed.

  Lemma canary_bytes_w : canary_bytes rnd = word_to_le_bytes 8 (canary_w rnd).
  Proof.
    unfold canary_w, word_to_le_bytes.
    pose proof (lez_bound_len (canary_bytes rnd) 8 eq_refl) as B. change (8 * Z.of_nat 8)%Z with 64%Z in B.
    rewrite u_Z2bv by lia. symmetry. exact (Z_to_le_bytes_lez (canary_bytes rnd)).
  Qed.

  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x12b978) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x10b5f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10b5f0)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x10b6a8) 8 = Some (word_to_le_bytes 8 (canary_w rnd)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* LPS 75d69e00: the hwcap cell holds the input's hwcap (was the ambient a_hwcap). *)
  Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x12b9b0) 8 = Some (word_to_le_bytes 8 (in_hwcap inp)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 1232896)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 1095184) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 1226488) 8 = Some (canary_bytes rnd).
  Proof.
    intros segs. rewrite (main_entry_rdn_data inp mbase entry sp0 rnd tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
