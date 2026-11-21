(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (disjoint_from_sub, dc_split, dc_merge and 6 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FsKit () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5BothW5FsKit5dc_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib5BothW5FsKit8dc_splitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib5BothW5FsKit7dc_takeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes8c8_of_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes:c8c8_of_CBC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImgAref_wview_overlayC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List>nth_error_app2C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib5Lists4List>nth_error_app1C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5BothW5FsKit:dc_at_any2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib5BothW4BImgDref_memory_read_noneC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib5BothW5FsKit<seg_rom_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib5BothW5FsKit8mrd_highC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_in H :=
  repeat match type of H with
  | context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v in H
  end.
Ltac lit_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  end.

(* [comment removed for export] *)
Ltac addr_diff_g E A :=
  let k := addr_diff E A in
  let ok := eval vm_compute in (Z.ltb k 65536) in
  lazymatch ok with true => k end.

Ltac solve_load_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_g :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Definition dc_at (m : word -> option byte) (A n : Z) : Prop :=
  exists bs, rw_cells bsegs m A [CB (Z.to_nat n) bs].

Lemma dc_split : forall m A a b, dc_at m A (a + b) -> 0 <= a -> 0 <= b ->
  dc_at m A a /\ dc_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app bsegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

Lemma dc_merge : forall m A a b, dc_at m A a -> dc_at m (A + a) b -> 0 <= a -> 0 <= b -> dc_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  assert (H : rw_cells bsegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exists (bs1 ++ bs2). rewrite Z2Nat.inj_add by lia. exact M.
Qed.

Lemma dc_take : forall m A n k, dc_at m A n -> 0 <= k <= n -> dc_at m A k /\ dc_at m (A + k) (n - k).
Proof. intros m A n k H Hk. apply dc_split; [replace (k + (n - k)) with n by lia; exact H| lia| lia]. Qed.
(* [comment removed for export] *)
Lemma dc_sub : forall m A n B k, dc_at m A n -> A <= B -> 0 <= k -> B + k <= A + n -> dc_at m B k.
Proof.
  intros m A n B k H H1 H2 H3.
  destruct (dc_take m A n (B - A) H ltac:(lia)) as [_ D]. replace (A + (B - A)) with B in D by lia.
  destruct (dc_take m B (n - (B - A)) k D ltac:(lia)) as [D' _]. exact D'.
Qed.

Lemma c8_of_dc : forall m A, dc_at m A 8 -> exists w : word, rw_cells bsegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
Lemma c8c8_of_dc : forall m A, dc_at m A 16 -> exists w1 w2 : word, rw_cells bsegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
Lemma c1_of_dc : forall m A, dc_at m A 1 -> exists b : byte, rw_cells bsegs m A [C1 b].
Proof.
  intros m A [bs H]. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
Lemma dc_of_cells : forall m A cs, rw_cells bsegs m A cs -> dc_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. exists (cells_bytes cs). rewrite Nat2Z.id.
  pose proof H as H0. destruct H0 as [[WF _] _].
  eapply rw_cells_recast; [exact H | cbn; split; [symmetry; symmetry; apply cells_bytes_length; exact WF| exact I]
    | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono bsegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x60f000 <= A) -> dc_at m' A n.
Proof.
  intros m m' A n [bs [[[WF _] [B0 [B1 BR]]] [W0 [W1 WR]]]] WM HA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in *.
  rewrite app_nil_r in B1, BR. cbn in WF. rewrite Nat.add_0_r in W1, WR.
  assert (RD : forall i, 0 <= i < Z.of_nat (length bs) -> exists b, m' (wa (A + i)) = Some b).
  { intros i Hi. specialize (WR i ltac:(lia)). apply WM in WR.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia).
    destruct (m' (wa (A + i))) as [b|]; [exists b; reflexivity| congruence]. }
  assert (BS : forall k, (k <= length bs)%nat -> exists bs' : list byte, length bs' = k /\
            forall i, (i < k)%nat -> m' (wa (A + Z.of_nat i)) = nth_error bs' i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (bs' & L & E). destruct (RD (Z.of_nat k) ltac:(lia)) as [b Hb].
      exists (bs' ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
      + rewrite nth_error_app1 by lia. apply E. lia. }
  destruct (BS (length bs) ltac:(lia)) as (bs' & L & E).
  exists bs'. split; [split; [cbn; destruct WF as [WF _]; split; [lia| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. unfold mrd. rewrite (E i ltac:(lia)).
    destruct (nth_error bs' i) eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply WM. apply WR. lia.
Qed.
Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono bsegs m m' -> 0x60f000 <= A -> dc_at m' A n.
Proof. intros m m' A n D W H. eapply dc_at_any2; [exact D | exact W | right; exact H]. Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall a : word, 0x60f000 <= bv_unsigned a -> seg_rom bsegs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite ref_memory_read_none; [reflexivity| cbn; lia| lia]. Qed.
Lemma mrd_high : forall m a, 0x60f000 <= a < 2^64 -> mrd bsegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. apply seg_rom_high. rewrite wa_unsigned by lia. lia.
Qed.
Lemma rw_C1_high : forall m a (b : byte), rw_cells bsegs m a [C1 b] -> 0x60f000 <= a -> m (wa a) = Some b.
Proof.
  intros m a b [[WF [B0 [B1 BR]]] _] Ha. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR, B1.
  rewrite Z.add_0_r in BR. rewrite <- mrd_high by lia. exact BR.
Qed.
End CANSEC1.
