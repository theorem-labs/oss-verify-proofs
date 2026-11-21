(* reloc-zl14c *)
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ArgvEnv OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefLayout OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.DrawDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8StartupDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8Startup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := TgtO_zlib_uncompress3_fuzzer_ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x74230%Z, 8%nat); (0x94590%Z, 8%nat); (0x945f0%Z, 8%nat); (0x945b8%Z, 8%nat); (0x94580%Z, 8%nat); (0x94578%Z, 8%nat); (0x94328%Z, 8%nat); (0x94338%Z, 8%nat); (0x94330%Z, 8%nat); (0x945a0%Z, 8%nat); (0x945a8%Z, 8%nat); (0x74310%Z, 8%nat); (0x742f8%Z, 8%nat); (0x74238%Z, 8%nat); (0x94588%Z, 1%nat); (0x74260%Z, 4%nat); (0x74258%Z, 4%nat); (0x742d0%Z, 8%nat); (0x742b0%Z, 8%nat); (0x74240%Z, 8%nat); (0x74248%Z, 8%nat); (0x74250%Z, 8%nat); (0x94568%Z, 4%nat); (0x9456c%Z, 4%nat); (0x94569%Z, 1%nat); (0x742f0%Z, 8%nat); (0x241b0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x95000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Variable sp0 : word.
  (* a worker port727 (): the launch input; av / hw are notations of it. *)
  Variable inp : ProcInput.
  Variable mbase : word.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 inp rdraw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 inp rdraw tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid). pose proof (u64_range hw).
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
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x74258) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x94568) 8 = Some (canary_bytes rdraw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_guard; [reflexivity | reflexivity | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_w : forall segs,
    rdn segs D (Z_to_bv 64 0x94568) 8 = Some (word_to_le_bytes 8 (canary_w rdraw)).
  Proof. intros segs. rewrite w8_canary. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x945b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x74238) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x74238)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x742f0) 8 = Some (word_to_le_bytes 8 (canary_w rdraw)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 inp mbase rdraw tid regs mem.

  (* [comment removed for export] *)

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x74258) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 inp mbase rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  (* [comment removed for export] *)
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
