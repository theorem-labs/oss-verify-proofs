(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb StartupTac ArgvEnv Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup_defs U_startup.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_startup_facts () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "range_disjoint_b"; "Corelib.Init.Datatypes.true"; "djw"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "D_main_missb"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_main"; "RocqVerifyHarness.AgentSubmission.BB.Amb.a_hwcap"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"].


Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) := ltac2:(CDefT.buildp (gd_tbl_P_startup_facts ()) "(0.(1.$2.$3.)(4.$2.$3.+5<??8.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=358.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=3;8.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=380.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=348.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=340.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=0?0.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=100.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=0?8.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=368.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=370.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=0=8.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=0<0.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=000.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=350.#1.)(0.(1.$2.$3.)(4.$2.$3.+5=028.#4.)(0.(1.$2.$3.)(4.$2.$3.+5=020.#4.)(0.(1.$2.$3.)(4.$2.$3.+5=098.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=078.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=008.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=010.#8.)(0.(1.$2.$3.)(4.$2.$3.+5=018.#8.)(0.(1.$2.$3.)(4.$2.$3.+7=330.#4.)(0.(1.$2.$3.)(4.$2.$3.+7=334.#4.)(0.(1.$2.$3.)(4.$2.$3.+7=331.#1.)(0.(1.$2.$3.)(4.$2.$3.+5=0;8.#8.)(0.(1.$2.$3.)(4.$2.$3.+4<?20.#1.)(5.(1.$2.$3.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x7e000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : ltac2:(CDefT.buildp (gd_tbl_P_startup_facts ()) "Pa,$2.Pn,$3.Pc,(1.$2.$3.)P,(6.$7.(8.R3.R2.R1.)$9.)(:.(;.(<.(=.R4.(>.R3.))(?.$2.$3.R2.))(<.(=.(?.$2.$3.R2.)(>.(10.$2.$3.R2.)))R4.)))")
(* [comment removed for export] *).
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev a_hwcap rd tid.

  #[using="Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_miss : ltac2:(CDefT.buildp (gd_tbl_P_startup_facts ()) "Psegs,(11.$12.)Pa,$2.Pn,$3.P,(6.$7.(13.R2.R1.)$9.)(6.(14.(11.(15.&8.)))(16.R4.(17.Vsp0,Vav,Vev,(18.VAMB,)Vrd,Vtid,)(19.&40.R3.)R2.)(16.R4.L,(15.&40.)(1:.(15.&8.))(19.&40.R3.)R2.))")
(* [comment removed for export] *).
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
  #[using="Type"] Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x7d330) 8 = Some (canary_bytes rd).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply guard_read.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x7d380) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_self : ltac2:(CDefT.buildp (gd_tbl_P_startup_facts ()) "Psegs,(11.$12.)(6.(14.(11.(15.&8.)))(16.R1.VD,(19.&40.+5=000.)#8.)(1;.(11.(15.&8.))(1<.#8.(19.&40.+5=000.))))")
(* [comment removed for export] *).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x5d0b8) 8 = Some (word_to_le_bytes 8 (canary_w rd)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  #[using="Hva"] Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0x7d3b8) 8 = Some (word_to_le_bytes 8 a_hwcap).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid rd regs mem.

  #[using="AMB sp0 av ev tid rd Hlo regs ME"] Lemma main_entry_rdn_image : ltac2:(CDefT.buildp (gd_tbl_P_startup_facts ()) "Psegs,(11.$12.)Pa,$2.Pn,$3.P,(6.$7.(13.R2.R1.)$9.)(6.(14.(11.(15.&8.)))(16.R4.Vmem,(19.&40.R3.)R2.)(16.R4.L,(15.&40.)(1:.(15.&8.))(19.&40.R3.)R2.))")
(* [comment removed for export] *).
  Proof.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x7e000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid rd regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  #[using="AMB sp0 av ev rd Hlo D regs ME"] Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x5d020) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid rd regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  #[using="AMB sp0 av ev tid Hlo D regs ME"] Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x7d330) 8 = Some (canary_bytes rd).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid rd regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
