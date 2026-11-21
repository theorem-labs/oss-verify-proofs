(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (impl_post_evt, impl_epost_evt, rw_cells_app and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun STRW_tac.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Startup_kit () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;Startup_kit=impl_post_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic8eq_ind_rC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes6option01I47Corelib4Init5Peano2le00C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib3Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib3Arr:u64s_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib6Common;Startup_kit6rd_u64C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mul".
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt : forall segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q Q' ms,
  impl segs atn t Q' ms -> (forall r ms', Q' r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
  intros segs atn R t; induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma impl_epost_evt : forall segs (atn : node -> machine_state -> Prop) {A} (t : itree node (exc A)) Q Q' ms,
  impl segs atn t (epost Q') ms -> (forall a ms', Q' a ms' -> evt segs (Q a) ms') -> impl segs atn t (epost Q) ms.
Proof.
  intros segs atn A t Q Q' ms H HQ. eapply impl_post_evt; [exact H|].
  intros [|a] ms' Hp; cbn in *; [apply evt_done; exact I | apply HQ; exact Hp].
Qed.

(* [comment removed for export] *)
Ltac astep := lstep; try (first [if_true | if_false]).
(* [comment removed for export] *)
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
Tactic Notation "icallk" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  eapply impl_epost_evt; [ eapply SPEC | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition td_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 32 (repeat (Z_to_bv 8 0) 32);
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition rtd_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale canary dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 24 (repeat (Z_to_bv 8 0) 24); C8 canary;
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition libc_cells (can_do : byte) (auxv tls_size tls_align page_size : word) : list cell :=
  [C1 can_do; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 auxv;
   C8 z64; C8 tls_size; C8 tls_align; C8 z64; C8 page_size; CB 48 (repeat (Z_to_bv 8 0) 48)].

(* [comment removed for export] *)
Definition auxv18 (uid rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
   Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_u64 : forall segs m A (w : word) rest a,
  bytes_at segs m A (le8 w ++ rest) -> a = wa A -> ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros segs m A w rest a B ->.
  assert (L : (0 + 8 <= length (le8 w ++ rest))%nat) by (rewrite app_length, length_le8; lia).
  pose proof (bytes_at_ov_read segs m A (le8 w ++ rest) 0 8 B L) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal; reflexivity.
Qed.

(* [comment removed for export] *)
Ltac exact_evt H :=
  lazymatch type of H with evt _ _ ?s1 =>
    lazymatch goal with |- evt _ _ ?s2 =>
      replace s2 with s1; [exact H|];
      cbv delta [mkR]; repeat first [reflexivity | lia | progress f_equal]
    end
  end.

(* [comment removed for export] *)
Lemma rd_u64s_g : forall segs mm A ws (i : nat) w a,
  bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
  ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
  intros segs mm A ws i w a B Hn ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E1 & Hlen & Eu & Hlu).
  rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
  eapply rd_u64; [exact B|]. unfold wa. f_equal. lia.
Qed.

(* [comment removed for export] *)
Ltac ldaux AUXB i :=
  let a := cur_mem_addr in
  let RD := fresh "RD" in
  pose proof (rd_u64s_g _ _ _ _ i _ a AUXB eq_refl ltac:(addr_tac)) as RD;
  zstep; clear RD.

(* [comment removed for export] *)
Ltac join2 H1 H2 :=
  lazymatch type of H2 with rw_cells ?segs ?mm ?A2 ?cs2 =>
  lazymatch type of H1 with rw_cells _ _ ?A ?cs1 =>
    let H := fresh "J" in
    assert (H : rw_cells segs mm A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app segs mm A cs1 cs2)); split;
            [ exact H1
            | replace (A + Z.of_nat (cells_size cs1))%Z with A2 by (simpl; lia); exact H2 ]);
    clear H1 H2; cbn [app] in H; rename H into H1
  end end.

(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StackAddrs.
  Variables (sp0 : word) (argv envp : list (list byte)).
  Notation usp0 := (bv_unsigned sp0).
  (* [comment removed for export] *)
  Definition envp_addr : Z := (usp0 + 8 * (argc argv + 2))%Z.
  (* [comment removed for export] *)
  Definition auxv_addr : Z := (usp0 + 8 * (argc argv + envc envp + 3))%Z.
End StackAddrs.
