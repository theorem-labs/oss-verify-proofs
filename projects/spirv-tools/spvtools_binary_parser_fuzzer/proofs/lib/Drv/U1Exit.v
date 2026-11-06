(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk MemSplit ShapeAlg Nodes RefNodes SymExec3 SymExec3Sound SymRun3 SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA SymExecASound Overlay RunsLib U1CxxTable U1Statics U1ExitKn U1ExitDefs U1StartInit U1_code_d1054_d2138 U1_code_d6138_d7138.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S. Import SXA. Import SXAS.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_small64 : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. Qed.

Lemma byte_list_eq : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x t IH]; intros [|y u] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Ht. f_equal; [apply bv_eq; exact Hx | apply IH; exact Ht].
Qed.

Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, (lo <= i < hi)%Z -> M (Z_to_bv 64 i) = None.

Section KnFacts.
  Variable E : env.
  Variable M : word -> option byte.

  Lemma kimg_intro : forall lo hi, (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z -> img_clear M lo hi ->
    kentry_ok SEGS E M (KImg lo hi).
  Proof. intros lo hi H0 H1 HC. cbn [kentry_ok]. repeat split; try lia. exact HC. Qed.

  Lemma kword_lit_intro : forall (a : Z) (w : nat) (v : Z) bs,
    (w <= 8)%nat -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat w <= 2 ^ 64)%Z ->
    rdn SEGS M (Z_to_bv 64 a) w = Some bs ->
    map bv_unsigned bs = map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 v)) ->
    kentry_ok SEGS E M (KWord (SA (ELit 0) a) w (ELit v)).
  Proof.
    intros a w v bs Hw Ha Hn HR HB. cbn [kentry_ok a_base a_off edenot]. split; [exact Hw|].
    unfold flat, estart, adenot. cbn [a_base a_off edenot]. rewrite (u_small64 0) by lia.
    split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. rewrite Z.add_0_l.
    rewrite HR. f_equal. apply byte_list_eq. exact HB.
  Qed.

  Lemma kword_rdn_intro : forall (a : Z) (w : nat) (v : Z),
    (w <= 8)%nat -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat w <= 2 ^ 64)%Z ->
    rdn SEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) ->
    kentry_ok SEGS E M (KWord (SA (ELit 0) a) w (ELit v)).
  Proof. intros. eapply kword_lit_intro; try eassumption. reflexivity. Qed.

  Definition cells_ok (cells : list (Z * nat * Z)) : Prop :=
    Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
      rdn SEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end) cells.
  Definition cells_wf (cells : list (Z * nat * Z)) : bool :=
    forallb (fun c : Z * nat * Z => match c with (a, w, v) =>
      (Nat.leb w 8 && (0 <=? a)%Z && (a + Z.of_nat w <=? 2 ^ 64)%Z && (a <? 2 ^ 64)%Z)%bool end) cells.
  Definition kn_of_cells (cells : list (Z * nat * Z)) : list kentry :=
    map (fun c : Z * nat * Z => match c with (a, w, v) => KWord (SA (ELit 0) a) w (ELit v) end) cells.

  Lemma kn_cells_ok : forall cells, cells_wf cells = true -> cells_ok cells -> know_ok SEGS E M (kn_of_cells cells).
  Proof.
    induction cells as [|[[a w] v] rest IH]; intros Hwf Hc; [constructor|].
    cbn [cells_wf forallb] in Hwf. apply andb_prop in Hwf as [Hwf Hrest].
    apply andb_prop in Hwf as [Hwf H3]. apply andb_prop in Hwf as [Hwf H2]. apply andb_prop in Hwf as [H0 H1].
    apply Nat.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    apply Forall_cons_iff in Hc as [Hc1 Hc2].
    constructor; [apply kword_rdn_intro; try assumption; lia | apply IH; assumption].
  Qed.

  Definition cxx_cells_ok : Prop := cells_ok exit_cxx_cells.
  Lemma kn_cxx_exit_eq : kn_cxx_exit = kn_of_cells exit_cxx_cells.
  Proof. reflexivity. Qed.
  Lemma kn_cxx_ok : cxx_cells_ok -> know_ok SEGS E M kn_cxx_exit.
  Proof. intros H. rewrite kn_cxx_exit_eq. apply kn_cells_ok; [vm_compute; reflexivity | exact H]. Qed.

  Definition cxx_cells_t_ok : Prop := cells_ok exit_cxx_cells_t.
  Lemma kn_cxx_exit_t_eq : kn_cxx_exit_t = kn_of_cells exit_cxx_cells_t.
  Proof. reflexivity. Qed.
  Lemma kn_cxx_t_ok : cxx_cells_t_ok -> know_ok SEGS E M kn_cxx_exit_t.
  Proof. intros H. rewrite kn_cxx_exit_t_eq. apply kn_cells_ok; [vm_compute; reflexivity | exact H]. Qed.

  Lemma kword_pins_intro : forall (a : Z) (w : nat) (v : Z) zs,
    pins D_SX M -> (w <= 8)%nat -> (0 <= a < 2 ^ 64)%Z -> (a + Z.of_nat w <= 2 ^ 64)%Z ->
    lookup_runs D_SX a w = Some zs ->
    map bv_unsigned (map (Z_to_bv 8) zs) = map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 v)) ->
    kentry_ok SEGS E M (KWord (SA (ELit 0) a) w (ELit v)).
  Proof.
    intros a w v zs HP Hw Ha Hn HL HB. eapply kword_lit_intro; try eassumption.
    eapply rdn_of_pins; try eassumption. lia.
  Qed.
End KnFacts.

Record exit_pre_u (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (code : word) : Prop := {
  eu_sp    : (0x100010000 <= bv_unsigned (getr regs 2) <= 0x800000000000)%Z;
  eu_sp16  : (bv_unsigned (getr regs 2) mod 16 = 0)%Z;
  eu_stack : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (getr regs 2) - EXIT_STACK)) (Z.to_nat EXIT_STACK) = true;
  eu_tp    : getr regs 4 = Z_to_bv 64 0x102418;
  eu_a0    : getr regs 10 = code;
  eu_tid   : exists tid, (1 <= tid < 4194304)%Z /\
               rdn SEGS mem (Z_to_bv 64 0x102370) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  eu_locale : rdn SEGS mem (Z_to_bv 64 0x1023e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0));
  eu_nlocks : rdn SEGS mem (Z_to_bv 64 0x1226ab) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0));
  eu_cxx   : cxx_cells_ok mem;
  eu_clear : Forall (fun iv => img_clear mem (fst iv) (snd iv)) (exit_clear_common ++ exit_clear_u);

  eu_e_flags : rdn SEGS mem (Z_to_bv 64 0xeff08) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  eu_e_wend  : rdn SEGS mem (Z_to_bv 64 0xeff28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  eu_e_buf   : rdn SEGS mem (Z_to_bv 64 0xeff60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x122bf8));
  eu_e_bsz   : rdn SEGS mem (Z_to_bv 64 0xeff68) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  eu_e_mode  : rdn SEGS mem (Z_to_bv 64 0xeff90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));

  eu_halt  : m_halted model = None;
  eu_lazy  : m_vm_lazy model = []
}.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.
Lemma sr_val : forall E sr R (r : reg) e, regs_ok E sr R -> sr_get sr r = e -> getr R r = edenot E e.
Proof. intros E sr R r e HR He. rewrite (HR r), He. reflexivity. Qed.

Section ExitU.
  Context {fx : FPState}.

  Definition EX (regs : bvmap 5 word) (tid : Z) : env :=
    Env (fun n => match n with
                  | 0%N => getr regs 2
                  | 1%N => Z_to_bv 64 tid
                  | 2%N => getr regs 10
                  | _ => getr regs (Z_to_bv 5 (Z.of_N n - 3))
                  end) (fun _ => []).

  Ltac kw_cxx HP := eapply (kword_pins_intro _ _ _ _ _ _ HP); [cbn; lia | lia | cbn; lia | reflexivity | vm_compute; reflexivity].
  Ltac kw_lit H := eapply (kword_lit_intro _ _ _ _ _ _ ); [cbn; lia | lia | cbn; lia | exact H | vm_compute; reflexivity].

  Theorem u1_exit_u : forall regs mem model code,
    exit_pre_u regs mem model code ->
    srealizes SEGS (mkCfg (mkst regs (0xd1e54 : word) mem (seg_rom SEGS)) model)
             (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
  Proof.
    intros regs mem model code PRE.
    destruct (eu_tid _ _ _ _ PRE) as (tid & Htid & Hrtid).
    pose proof (eu_sp _ _ _ _ PRE) as Hsp. pose proof (eu_sp16 _ _ _ _ PRE) as Hal.
    set (E := EX regs tid).

    assert (HR : regs_ok E sr_exit regs).
    { apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_exit all_regs]; subst E; cbn [edenot ev EX];
        first [ reflexivity | exact (eu_tp _ _ _ _ PRE) ]. }

    assert (HK : know_ok SEGS E mem kn_exit_u).
    { pose proof (eu_clear _ _ _ _ PRE) as HC. unfold exit_clear_common, exit_clear_u in HC. cbn [app] in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      cbn [fst snd] in *.
      pose proof (kn_cxx_ok E mem (eu_cxx _ _ _ _ PRE)) as HKC.
      unfold kn_exit_u, kn_exit_common0, kn_u_extra.
      unfold know_ok. rewrite !Forall_app. split; [|split; [exact HKC|]].
      all: repeat apply Forall_cons; try apply Forall_nil.
      all: try (apply kimg_intro; [lia | lia | assumption]).
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX]. lia.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX]. split; [lia | exact Hal].
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off]. subst E; cbn [edenot ev EX].
        unfold EXIT_STACK. rewrite (u_small64 1024) by lia. split; [lia|]. intros d m Hd Hm.
        eapply store_ok_sub; [ | exact (eu_stack _ _ _ _ PRE) | | ]; unfold EXIT_STACK; rewrite ?u_small64 by lia;
          rewrite ?Z2Nat.id by lia; lia.
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        rewrite (u_small64 0) by lia. rewrite (u_small64 217088) by lia. split; [lia|]. intros d m Hd Hm.
        apply store_ok_of_all; [rewrite u_small64 by lia; lia|]. intros x Hx. rewrite u_small64 in Hx by lia.
        apply rw_wview. lia.
      -   cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off edenot ev]. subst E; cbn [ev EX].
        rewrite (u_small64 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. exact Hrtid.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX]. rewrite u_small64 by lia. lia.
      - kw_lit (eu_locale _ _ _ _ PRE).
      - kw_lit (eu_nlocks _ _ _ _ PRE).
      - kw_lit (eu_e_flags _ _ _ _ PRE).
      - kw_lit (eu_e_wend _ _ _ _ PRE).
      - kw_lit (eu_e_buf _ _ _ _ PRE).
      - kw_lit (eu_e_bsz _ _ _ _ PRE).
      - kw_lit (eu_e_mode _ _ _ _ PRE). }

    destruct (runA_sound SEGS 3000 [] (SCR [] [] []) EXIT sr_exit kn_exit_u 40
                (fst (fst cert_u)) cert_u_scs (snd cert_u) E mem (seg_rom SEGS) regs
                ltac:(rewrite cert_u_eq; reflexivity) HR HK ltac:(rewrite cert_u_scs_nil; constructor))
      as (R' & HR' & _ & Hms).
    replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) in Hms by (apply bv_eq; reflexivity).
    change (s_pc (fst (fst cert_u))) with cert_u_pc in Hms. rewrite cert_u_pc_ok in Hms.
    replace (Z_to_bv 64 EXIT_ECALL) with (0xd1b64 : word) in Hms by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact (eu_halt _ _ _ _ PRE) | exact (eu_lazy _ _ _ _ PRE) | exact Hms |].
    eapply (srz_exit_at SEGS); [exact F_d1b30 | exact E_d1b30 | exact (eu_halt _ _ _ _ PRE) | exact (eu_lazy _ _ _ _ PRE) | |].
    - left. change (s_regs (fst (fst cert_u))) with cert_u_sr in HR'.
      rewrite (sr_val E cert_u_sr R' 17 (ELit 94) HR' eq_refl). reflexivity.
    - change (s_regs (fst (fst cert_u))) with cert_u_sr in HR'.
      rewrite (sr_val E cert_u_sr R' 10 (EVar 2) HR' eq_refl). subst E; cbn [edenot ev EX]. exact (eu_a0 _ _ _ _ PRE).
  Qed.
End ExitU.

Record exit_pre_u1 (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (code : word) : Prop := {
  eu1_sp    : (0x100010000 <= bv_unsigned (getr regs 2) <= 0x800000000000)%Z;
  eu1_sp16  : (bv_unsigned (getr regs 2) mod 16 = 0)%Z;
  eu1_stack : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (getr regs 2) - EXIT_STACK)) (Z.to_nat EXIT_STACK) = true;
  eu1_tp    : getr regs 4 = Z_to_bv 64 0x102418;
  eu1_a0    : getr regs 10 = code;
  eu1_tid   : exists tid, (1 <= tid < 4194304)%Z /\
               rdn SEGS mem (Z_to_bv 64 0x102370) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  eu1_locale : rdn SEGS mem (Z_to_bv 64 0x1023e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0));
  eu1_nlocks : rdn SEGS mem (Z_to_bv 64 0x1226ab) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0));
  eu1_cxx   : cxx_cells_ok mem;
  eu1_clear : Forall (fun iv => img_clear mem (fst iv) (snd iv)) (exit_clear_common ++ exit_clear_u1);

  eu1_e_flags : rdn SEGS mem (Z_to_bv 64 0xeff08) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  eu1_e_rpos  : rdn SEGS mem (Z_to_bv 64 0xeff10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  eu1_e_rend  : rdn SEGS mem (Z_to_bv 64 0xeff18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  eu1_e_wend  : rdn SEGS mem (Z_to_bv 64 0xeff28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x122bf8));
  eu1_e_wpos  : rdn SEGS mem (Z_to_bv 64 0xeff30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x122bf8));
  eu1_e_wbase : rdn SEGS mem (Z_to_bv 64 0xeff40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x122bf8));
  eu1_e_mode  : rdn SEGS mem (Z_to_bv 64 0xeff90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));

  eu1_halt  : m_halted model = None;
  eu1_lazy  : m_vm_lazy model = []
}.

Section ExitU1.
  Context {fx : FPState}.

  Definition EX1 (regs : bvmap 5 word) (tid : Z) : env :=
    Env (fun n => match n with
                  | 0%N => getr regs 2
                  | 1%N => Z_to_bv 64 tid
                  | 2%N => getr regs 10
                  | _ => getr regs (Z_to_bv 5 (Z.of_N n - 3))
                  end) (fun _ => []).

  Ltac kw_cxx HP := eapply (kword_pins_intro _ _ _ _ _ _ HP); [cbn; lia | lia | cbn; lia | reflexivity | vm_compute; reflexivity].
  Ltac kw_lit H := eapply (kword_lit_intro _ _ _ _ _ _ ); [cbn; lia | lia | cbn; lia | exact H | vm_compute; reflexivity].

  Theorem u1_exit_u1 : forall regs mem model code,
    exit_pre_u1 regs mem model code ->
    srealizes SEGS (mkCfg (mkst regs (0xd1e54 : word) mem (seg_rom SEGS)) model)
             (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
  Proof.
    intros regs mem model code PRE.
    destruct (eu1_tid _ _ _ _ PRE) as (tid & Htid & Hrtid).
    pose proof (eu1_sp _ _ _ _ PRE) as Hsp. pose proof (eu1_sp16 _ _ _ _ PRE) as Hal.
    set (E := EX1 regs tid).

    assert (HR : regs_ok E sr_exit regs).
    { apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_exit all_regs]; subst E; cbn [edenot ev EX1];
        first [ reflexivity | exact (eu1_tp _ _ _ _ PRE) ]. }

    assert (HK : know_ok SEGS E mem kn_exit_u1).
    { pose proof (eu1_clear _ _ _ _ PRE) as HC. unfold exit_clear_common, exit_clear_u1 in HC. cbn [app] in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      cbn [fst snd] in *.
      pose proof (kn_cxx_ok E mem (eu1_cxx _ _ _ _ PRE)) as HKC.
      unfold kn_exit_u1, kn_exit_common0, kn_u1_extra.
      unfold know_ok. rewrite !Forall_app. split; [|split; [exact HKC|]].
      all: repeat apply Forall_cons; try apply Forall_nil.
      all: try (apply kimg_intro; [lia | lia | assumption]).
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX1]. lia.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX1]. split; [lia | exact Hal].
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off]. subst E; cbn [edenot ev EX1].
        unfold EXIT_STACK. rewrite (u_small64 1024) by lia. split; [lia|]. intros d m Hd Hm.
        eapply store_ok_sub; [ | exact (eu1_stack _ _ _ _ PRE) | | ]; unfold EXIT_STACK; rewrite ?u_small64 by lia;
          rewrite ?Z2Nat.id by lia; lia.
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        rewrite (u_small64 0) by lia. rewrite (u_small64 217088) by lia. split; [lia|]. intros d m Hd Hm.
        apply store_ok_of_all; [rewrite u_small64 by lia; lia|]. intros x Hx. rewrite u_small64 in Hx by lia.
        apply rw_wview. lia.
      -   cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off edenot ev]. subst E; cbn [ev EX1].
        rewrite (u_small64 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. exact Hrtid.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EX1]. rewrite u_small64 by lia. lia.
      - kw_lit (eu1_locale _ _ _ _ PRE).
      - kw_lit (eu1_nlocks _ _ _ _ PRE).
      - kw_lit (eu1_e_flags _ _ _ _ PRE).
      - kw_lit (eu1_e_rpos _ _ _ _ PRE).
      - kw_lit (eu1_e_rend _ _ _ _ PRE).
      - kw_lit (eu1_e_wend _ _ _ _ PRE).
      - kw_lit (eu1_e_wpos _ _ _ _ PRE).
      - kw_lit (eu1_e_wbase _ _ _ _ PRE).
      - kw_lit (eu1_e_mode _ _ _ _ PRE). }

    destruct (runA_sound SEGS 3000 [] (SCR [] [] []) EXIT sr_exit kn_exit_u1 40
                (fst (fst cert_u1)) cert_u1_scs (snd cert_u1) E mem (seg_rom SEGS) regs
                ltac:(rewrite cert_u1_eq; reflexivity) HR HK ltac:(rewrite cert_u1_scs_nil; constructor))
      as (R' & HR' & _ & Hms).
    replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) in Hms by (apply bv_eq; reflexivity).
    change (s_pc (fst (fst cert_u1))) with cert_u1_pc in Hms. rewrite cert_u1_pc_ok in Hms.
    replace (Z_to_bv 64 EXIT_ECALL) with (0xd1b64 : word) in Hms by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact (eu1_halt _ _ _ _ PRE) | exact (eu1_lazy _ _ _ _ PRE) | exact Hms |].
    eapply (srz_exit_at SEGS); [exact F_d1b30 | exact E_d1b30 | exact (eu1_halt _ _ _ _ PRE) | exact (eu1_lazy _ _ _ _ PRE) | |].
    - left. change (s_regs (fst (fst cert_u1))) with cert_u1_sr in HR'.
      rewrite (sr_val E cert_u1_sr R' 17 (ELit 94) HR' eq_refl). reflexivity.
    - change (s_regs (fst (fst cert_u1))) with cert_u1_sr in HR'.
      rewrite (sr_val E cert_u1_sr R' 10 (EVar 2) HR' eq_refl). subst E; cbn [edenot ev EX1]. exact (eu1_a0 _ _ _ _ PRE).
  Qed.
End ExitU1.

Record exit_pre_t0 (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (code : word) : Prop := {
  et0_sp    : (0x100010000 <= bv_unsigned (getr regs 2) <= 0x800000000000)%Z;
  et0_sp16  : (bv_unsigned (getr regs 2) mod 16 = 0)%Z;
  et0_stack : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (getr regs 2) - EXIT_STACK)) (Z.to_nat EXIT_STACK) = true;
  et0_tp    : getr regs 4 = Z_to_bv 64 0x102418;
  et0_a0    : getr regs 10 = code;
  et0_tid   : exists tid, (1 <= tid < 4194304)%Z /\
               rdn SEGS mem (Z_to_bv 64 0x102370) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  et0_locale : rdn SEGS mem (Z_to_bv 64 0x1023e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0));
  et0_nlocks : rdn SEGS mem (Z_to_bv 64 0x1226ab) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0));
  et0_cxx   : cxx_cells_t_ok mem;
  et0_clear : Forall (fun iv => img_clear mem (fst iv) (snd iv)) (exit_clear_common ++ exit_clear_t0);

  et0_o_flags : rdn SEGS mem (Z_to_bv 64 0xf00e8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  et0_o_rpos  : rdn SEGS mem (Z_to_bv 64 0xf00f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  et0_o_rend  : rdn SEGS mem (Z_to_bv 64 0xf00f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  et0_o_wend  : rdn SEGS mem (Z_to_bv 64 0xf0108) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123408));
  et0_o_wpos  : rdn SEGS mem (Z_to_bv 64 0xf0110) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123008));
  et0_o_wbase : rdn SEGS mem (Z_to_bv 64 0xf0120) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123008));
  et0_o_write : rdn SEGS mem (Z_to_bv 64 0xf0130) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd70d4));
  et0_o_mode  : rdn SEGS mem (Z_to_bv 64 0xf0170) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));
  et0_o_lbf   : rdn SEGS mem (Z_to_bv 64 0xf0178) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));

  et0_halt  : m_halted model = None;
  et0_lazy  : m_vm_lazy model = []
}.

Section ExitT0.
  Context {fx : FPState}.

  Definition EXT0 (regs : bvmap 5 word) (tid : Z) : env :=
    Env (fun n => match n with
                  | 0%N => getr regs 2
                  | 1%N => Z_to_bv 64 tid
                  | 2%N => getr regs 10
                  | _ => getr regs (Z_to_bv 5 (Z.of_N n - 3))
                  end) (fun _ => []).

  Ltac kw_cxx HP := eapply (kword_pins_intro _ _ _ _ _ _ HP); [cbn; lia | lia | cbn; lia | reflexivity | vm_compute; reflexivity].
  Ltac kw_lit H := eapply (kword_lit_intro _ _ _ _ _ _ ); [cbn; lia | lia | cbn; lia | exact H | vm_compute; reflexivity].

  Theorem u1_exit_t0 : forall regs mem model code,
    exit_pre_t0 regs mem model code ->
    srealizes SEGS (mkCfg (mkst regs (0xd1e54 : word) mem (seg_rom SEGS)) model)
             (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
  Proof.
    intros regs mem model code PRE.
    destruct (et0_tid _ _ _ _ PRE) as (tid & Htid & Hrtid).
    pose proof (et0_sp _ _ _ _ PRE) as Hsp. pose proof (et0_sp16 _ _ _ _ PRE) as Hal.
    set (E := EXT0 regs tid).

    assert (HR : regs_ok E sr_exit regs).
    { apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_exit all_regs]; subst E; cbn [edenot ev EXT0];
        first [ reflexivity | exact (et0_tp _ _ _ _ PRE) ]. }

    assert (HK : know_ok SEGS E mem kn_exit_t0).
    { pose proof (et0_clear _ _ _ _ PRE) as HC. unfold exit_clear_common, exit_clear_t0 in HC. cbn [app] in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      cbn [fst snd] in *.
      pose proof (kn_cxx_t_ok E mem (et0_cxx _ _ _ _ PRE)) as HKC.
      unfold kn_exit_t0, kn_exit_common0, kn_t0_extra.
      unfold know_ok. rewrite !Forall_app. split; [|split; [exact HKC|]].
      all: repeat apply Forall_cons; try apply Forall_nil.
      all: try (apply kimg_intro; [lia | lia | assumption]).
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EXT0]. lia.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EXT0]. split; [lia | exact Hal].
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off]. subst E; cbn [edenot ev EXT0].
        unfold EXIT_STACK. rewrite (u_small64 1024) by lia. split; [lia|]. intros d m Hd Hm.
        eapply store_ok_sub; [ | exact (et0_stack _ _ _ _ PRE) | | ]; unfold EXIT_STACK; rewrite ?u_small64 by lia;
          rewrite ?Z2Nat.id by lia; lia.
      -   cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        rewrite (u_small64 0) by lia. rewrite (u_small64 217088) by lia. split; [lia|]. intros d m Hd Hm.
        apply store_ok_of_all; [rewrite u_small64 by lia; lia|]. intros x Hx. rewrite u_small64 in Hx by lia.
        apply rw_wview. lia.
      -   cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off edenot ev]. subst E; cbn [ev EXT0].
        rewrite (u_small64 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. exact Hrtid.
      -   cbn [kentry_ok]. subst E; cbn [edenot ev EXT0]. rewrite u_small64 by lia. lia.
      - kw_lit (et0_locale _ _ _ _ PRE).
      - kw_lit (et0_nlocks _ _ _ _ PRE).
      - kw_lit (et0_o_flags _ _ _ _ PRE).
      - kw_lit (et0_o_rpos _ _ _ _ PRE).
      - kw_lit (et0_o_rend _ _ _ _ PRE).
      - kw_lit (et0_o_wend _ _ _ _ PRE).
      - kw_lit (et0_o_wpos _ _ _ _ PRE).
      - kw_lit (et0_o_wbase _ _ _ _ PRE).
      - kw_lit (et0_o_write _ _ _ _ PRE).
      - kw_lit (et0_o_mode _ _ _ _ PRE).
      - kw_lit (et0_o_lbf _ _ _ _ PRE). }

    destruct (runA_sound SEGS 3000 [] (SCR [] [] []) EXIT sr_exit kn_exit_t0 40
                (fst (fst cert_t0)) cert_t0_scs (snd cert_t0) E mem (seg_rom SEGS) regs
                ltac:(rewrite cert_t0_eq; reflexivity) HR HK ltac:(rewrite cert_t0_scs_nil; constructor))
      as (R' & HR' & _ & Hms).
    replace (Z_to_bv 64 EXIT) with (0xd1e54 : word) in Hms by (apply bv_eq; reflexivity).
    change (s_pc (fst (fst cert_t0))) with cert_t0_pc in Hms. rewrite cert_t0_pc_ok in Hms.
    replace (Z_to_bv 64 EXIT_ECALL) with (0xd1b64 : word) in Hms by (apply bv_eq; reflexivity).
    eapply srz_msteps; [exact (et0_halt _ _ _ _ PRE) | exact (et0_lazy _ _ _ _ PRE) | exact Hms |].
    eapply (srz_exit_at SEGS); [exact F_d1b30 | exact E_d1b30 | exact (et0_halt _ _ _ _ PRE) | exact (et0_lazy _ _ _ _ PRE) | |].
    - left. change (s_regs (fst (fst cert_t0))) with cert_t0_sr in HR'.
      rewrite (sr_val E cert_t0_sr R' 17 (ELit 94) HR' eq_refl). reflexivity.
    - change (s_regs (fst (fst cert_t0))) with cert_t0_sr in HR'.
      rewrite (sr_val E cert_t0_sr R' 10 (EVar 2) HR' eq_refl). subst E; cbn [edenot ev EXT0]. exact (et0_a0 _ _ _ _ PRE).
  Qed.
End ExitT0.

