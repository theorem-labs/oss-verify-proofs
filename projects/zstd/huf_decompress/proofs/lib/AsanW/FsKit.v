(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (disjoint_from_sub, dc_split, dc_merge and 6 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FsKit () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5AsanW5FsKit5dc_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib5AsanW5FsKit8dc_splitC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib5AsanW5FsKit7dc_takeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ABytes8c8_of_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6ABytes:c8c8_of_CBC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib7InitMem?rw_cells_recastC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImgAref_wview_overlayC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List>nth_error_app2C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib5Lists4List>nth_error_app1C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_NoneC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5AsanW5FsKit:dc_at_any2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib5AsanW4AImgDref_memory_read_noneC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib5AsanW5FsKit<seg_rom_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rc59OSSVerify5KrLib5AsanW5FsKit8mrd_highC1?~~~~~~~~~~~~~~~".
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
  exists bs, rw_cells asegs m A [CB (Z.to_nat n) bs].

Lemma dc_split : forall m A a b, dc_at m A (a + b) -> 0 <= a -> 0 <= b ->
  dc_at m A a /\ dc_at m (A + a) b.
Proof.
  intros m A a b [bs H] Ha Hb.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat (a + b)) bs [] [Z.to_nat a; Z.to_nat b] H ltac:(cbn; lia)) as H2.
  cbn [app mk_CB_cells] in H2. apply (proj1 (rw_cells_app asegs m A [_] [_])) in H2. destruct H2 as [H1 H2].
  cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia.
  split; [eexists; exact H1 | eexists; exact H2].
Qed.

Lemma dc_merge : forall m A a b, dc_at m A a -> dc_at m (A + a) b -> 0 <= a -> 0 <= b -> dc_at m A (a + b).
Proof.
  intros m A a b [bs1 H1] [bs2 H2] Ha Hb.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2]) [] ) as M.
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

Lemma c8_of_dc : forall m A, dc_at m A 8 -> exists w : word, rw_cells asegs m A [C8 w].
Proof. intros m A [bs H]. destruct (c8_of_CB m A bs H) as [w [H' _]]. exists w. exact H'. Qed.
Lemma c8c8_of_dc : forall m A, dc_at m A 16 -> exists w1 w2 : word, rw_cells asegs m A [C8 w1; C8 w2].
Proof. intros m A [bs H]. exact (c8c8_of_CB m A bs H). Qed.
Lemma c1_of_dc : forall m A, dc_at m A 1 -> exists b : byte, rw_cells asegs m A [C1 b].
Proof.
  intros m A [bs H]. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  destruct bs as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity].
Qed.
Lemma dc_of_cells : forall m A cs, rw_cells asegs m A cs -> dc_at m A (Z.of_nat (cells_size cs)).
Proof.
  intros m A cs H. exists (cells_bytes cs). rewrite Nat2Z.id.
  pose proof H as H0. destruct H0 as [[WF _] _].
  eapply rw_cells_recast; [exact H | cbn; split; [symmetry; symmetry; apply cells_bytes_length; exact WF| exact I]
    | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x60d000 <= A) -> dc_at m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01ih14__x1h24__x2h37__arithh44cstrh52W2h63WF0h74__ffh88__varmaph95__with:2H2h;3bs'h<2z2h=5cstr0h>2L0h?1Hh@1ni001nhA2WRhB4__x3hC1bi011bhD4__x4hE2HihF3Hi0hG3Hk0hH5cstr1hI1xi021xhJ4__p1hK1oi031ohL1NhM1lhN2W1hO6__sat4hP6__sat5hQ4__x5hR1ei041ehS1khT1AhU2bshV1yhW2B1hX2BRhY1EhZ2H3h[2Hah\2Hkh]3IH0h^1Lh_3NE0h`4__p2ha4__p3hb5cstr2hc1mhd2z3he2B0hf2BShg2HAhh2Hbhi3Heqhj2IHhk2N0hl2NEhm2RDhn2W0ho2WFhp2WMhq2_Hhr6__sat3hs2m'ht2n0hu1si051shv1zp%0p%1p%2p&0p&1p;1p;3p;4p;2p;6p;5p;7p;<p;Bp;8g00;oj1RTg00MQk10UTg00Mok10RTg00NRS00k10JTg00O4j3TTg001bk10?Tg0047k10BTg00_Ek40@Tg00nnj1yTg00=7j1rTg013\k40<Tg015Ek108Tg00h_j1QTg016<j4|Tg0171k10VTg01=Nk20rTg017gj22Tg01=kR0j25Tg00QVR1j10Tg0061S01j2@Tg00=\k103Tg003>R2j28Tg00Y]j3bTg00iYk20KTg000Mk600Tg01>Cj3JTg00?fS02j33k10XTg00OjR3j1?Tg00\jR4k20HTg00]Jk10GTg00acR5j2=Tg00>`j2eTg01>ak30[Tg01?Gk10ETg01?ek60ATg003ZR6j24Tg01@Nk40xTg00R6k20uTg00RYk30tTg019nj1<Tg006LR7j1ATg006kk20TTg008ij2{Tg009ek10qTg00:Ck10pTg00:ak10oTg00Uej2zTg00;Lk20STg00>>k20nTg00?:k20mTg00@@k30lTg00@_k40QTg00VHj4XTg01A1k104Tg01A`k20kTg01BHk30jTg01Blk20iTg01CMk20eTg01D7k30dTg01DZk20cTg000ij6^k717Tg01ERk30bTg01FSk20LTg00gJS03j2NTg00^kk40:Tg01G5j1lTg01GNk21GTg01GmR8j2DTg018Gj4BTg00AQj4gTg004Wj3_Tg00Q?k20_Tg00T=k11CTg00T[k21BTg00U<k30^Tg01HGk31?Tg01Hfk21>Tg01IIS04k21=Tg01Iik20]Tg01J@k21<Tg01J`k11;Tg01KEk518Tg01Khk316Tg01LQk615Tg01M;k514Tg01M^k413Tg01N?k20FTg01O8k311Tg00PJk20CTg01O[k310Tg005Wj2}Tg00ZXk10~Tg014Sk40}Tg01POk312Tg01Q?k30ZTg00`;k20|Tg00`Xm<0DTg00S6l<pTg00a=mB0`Tg00S[k20{Tg007Tk319Tg008=k20zTg009Gk41:Tg00BNj4uTg00C9k707Tg00b?k70yTg00DAk805Tg00mRk60wTg00C]k71@Tg00<Tk31ATg01R<k60vTf0R9#R#Rp>0ag00cXR:f2R;#?f1R<+0C;_9p=>g00bcR=@10<9p=`%R9#R#R#Rp=wg00H[R>f5R?'8f4R@f3RA'4/8;'@18<9'}p=m&0~9#0p=KP=P;P<P9H0}p=k%?<00C9p>0WA_:<9p>0s18>9p=;12<9#0p=V14;</89p=714<9$04p=6B12=<9p=oAJ;<993@Ap=P1=<9,@;p=M14;<$04:0Z=A=3@9#lp=i14A;/8<,@@/}9p>0M20|>9p=:g00DeRB/e9p=1PBg00dMRCPBPBP3P@P1PAg00dlP;P<P9N<0Dp=EPCPBPBPBP1P1P?P@PAP;P<P9N<0Dp=HPBPBP5f7R3P5f6RDP?P@PAP;P<P9M<pp>0IPBPBPBPBPBPBP6P9P<P;P6PAP@P?PDP3f8REf9RFNB0`p=SA3B<9p=9PBPBP2P3P2PDP?P@PAP;P<P9M<pp=U18@AP;P<P9CBp=fA3C<9p=FPCPBP9P1P<P;PAP@P?PDP3PEM<pp=CA3C@AP;P<P9CBp=L%09,8>p=W20{>9p=\1=>@A3BA;'@18<>A3B9>'@'}p=[20TB9p=vB19B<9p=Ig00K@-0z9p=jg00J5RG?_<9p=]PBP;P<P9H1:p=G20SB9p=tP;g00EjRHg00FIRIPIg00FiRJPBP<g00fcRKP9Cug00GIRLK07p=cP;PHPIPIPJPBP<g00ECRMP9CuPLK07p=YP;PHPIPIPJPBP<g00f<RNP9CuPLK07p>06P;PHPIPIPJP<P9K0yp=nPDPHPIPIPJP?P@PAPHPIPIPJP;P<P9L05L05p=h18></@9p>0PB0Z=<9p>0>A3;<9#lp=~18<9,};p>0O1=>9p>0=P<PHPIPIPJP9J0wp>01P;PHPIPIPJP<P9K1@p>0;B1AB<9p=sA3B9>,@<p>0h1@;</}9p>0g189>p>0fPBP<PKP9Cup>0NPBP<PMP9Cup>02P@PHPIPIPJPAPHPIPIPJP;PLK07P<P9L05p=ZPCPBP0P1P5g01R`RLPAP;P<g00JaRMP>P9M<pp>1FPCPBP8P1P2g01SBRKPMP>PAP;P<P9M<pp>1EPBP<PNP9Cup>09PCPBP8P1P2PKP?P@PAP;P<P9M<pp=dPCPCPBPBP7P1P1PAg01:SP;P<P9N<0Dp=xPAPHPIPIPJP;P<P9L05p=aA3C;</@9p=OPCPCPCPBPBPBP4P1P1P1P6g00eYP?P@PAP;P<P9NB0`p>1DPCPBP0P1P5PLP?P@PAP;P<P9M<pp=qP<PHPIPIPJP9J0vp>0\20C;<=_:9p>0Yg00KlS05#RRH#RRL#RR5#R$0aR1$0US06$0R&0U5$0RR5$0JR0[S07Q07ATA<9Q03&0?5R6P=P?PA&0B:R:9>;9H0@XU61`?@P@P@PA&0a1#w#w#yR4Q05#r#R#w#r#r#R#r#w#w#w#yR7P@EmATD?@[[P9P=P3P?A>@9:H0@Q01P=PEPDA>?<:RKH0<%KK9kED1`FEPEPEP3P4P7PEEmf:RK?TFE[[P9P=PKPEA>3A:H0<Q01A>E@:R2$08P=f;R8PF%Q2C|f<R2A>F?:#K7kKf=RN/`2P2P2P8P4P7P2Emf>S08?TN2[[[P9A>KD:$08Q0120W83$0V&08:S09P=f?ROPNA>2E:#QC|f@RPQ0820WNFRQ00s:#K3kfARR/`PPPPPPOP4P7PPEmfBRS?TRP[[[[P9&0VQQ09P=PSPPA>O8:#QC|Q01%;RA>P2:#Q,V5%yHRQ%y1R1+0rRT57RA>RN:RU#Q,25,59P0fERVfCS0:%0<RW'6'oP5Q08=>S:#QP<DP[^0C'@fDRX%KU7kS1`VXPXPXQ0:P4P7PXEmfFRU?TVX[[[P9Q0:#;Q0:?>O:#Q,V5=7XTA>XP:#Q,25RY,59P0fHRZ16UW'oP5A>VR:R[#QR\P<DP[^0C'@Q01%0Y=7VT125\,59P0fIR\fGS0;/6W'oP5A>US:#QRYP<DP[^0C%K[9kZU1`\ZPZPZQ0;P4P7PZEmfJR[?T\Z[[[P9Q0;1V5Y;7TA>ZX:RY#Q,25,59P0fLR]16[W'oP5A>\V:R^#QP<DP[^0CfKR_%KY7k\Q01%;[%K^=7[T%;9R^A>[U:#K7M9P0fNS0<P]P<&035RYDi[^0B'@fMR`/`]%;]S0=P]P_P4187]I0MQ0<?T`][[P9Q0=A>]Z:#K=7`TA>`\:#KRa9M^9P0fQS0>fORbP<PYDi[^0B'@Q01Q0<?7aTQ0<?>[:#K9M^9P0fRRafPRcP<PYDi[^0BQ0>/`cPcPcPbP4P7PcEmQ0>=Tac[[P9A>b_:#K=7cTQ0>?>`:#K9M^9P0fUS0?fSS0@P<PYDi[^0BfTS0AQ0@'`Q0@Q0@PaP4P7Q0@EmP6&0B5Rd9b5bQ0?1259Re#0;7TXM6P2Pb20K5bJ00Q0A1V5b;7TP6Ab5cd125<S0B,59fZRbfXRf/6W'oAJ5;<Rg530[^0CXM6P2Pc20K5cJ00Q0>,25,59P0fYRhfWS0C/6W'oP5PaP<DP[^0CPCQ0?#?Ra00HMQ0C%09S0D;7TX@CP?Pa&0GaJ00fVS0E%0a;7TPCQ0E#?Ra00HMAM^9WP0f\RiPbP<PYDiRj[^0BX@CP?Pa&0GaJ00Q0C#?#09M^9P0f[RaPhP<PYDi[^0BQ0A,V59M^9S0FP;P<%;<Rk%?hRl#0Rm,=<Rn'@%:hRo,=<Rp,@kPkPnPkPpp-0Rp/ekS0G:0[kkS0HP9XIBRn1=<9S0I$0EXVBXIBS0JP<P<%1<S0KPmPoPnPnQ0D#1XICRqPlPoPn%:9XIBRrPhPh%1hDERsEHL0IJ0A14bmRtPTA7boTS0LPn18<9$0EXVBXIBS0MPtPnPrPhO1RtO1Ro,4bPnPnPnPBPBg01Sd14<9H0x#1XcBX@BS0NPbPb%1bRuPmPoPnPnPqPlPtPsEHM:SPTPT%1TS0O19TTeS0PGUPADfS0QQ0LQ0E,25S0R%?bRsQ0R#0Rt%:b'9S0S&0XCRl&0XBRoQ0D,9W1F<920u<940tXVCXICRmQ0RPt%1tPsPrPbO1PnPrPbPbPuDEM9CP]DLS0TQ0SQ0C,25S0U#<S0VQ0U#WS0W%\iS0XPi%:iRuPiPiPuD[S0Yf]Rs#:S0ZPB%AMS0[#AS0\#AS0]#vS0^Q0[#vS0_20TBMS0`'IS0a'I#jS0b&0BGRt']&0?GRG1{BAS0c&0qBRv7G;S0d?G<v&0pBRw&0oBRx%tLRL%tHRy5cxS0e&03IRIPx1zB>RzQ05-0SBR{5YxS0fB06x{LS0g5nxPIQ0fB06x{yS0h5nxS0iFh20nxJRJP9P;g00LQR|g00M1R}'eS0j20m9;=3|}dB0lB><S0kH0QR}b7b8b9X1BX2BXBB19;<AMk<A1=;AS0l-0P;S0m[[^1B^2B^BBP9125aS0n#0S0oP<P3P@PDO5b3b<b:b4b6b5CXO2PjPE16a;S0pP9O2Q0p-0>i=~0YP014iAS0q$04Rj-0>sA~09YS0rXK0P9PsPjO1S0sPBQ0qQ05#yR|,49S0t/84@0O79XvB%?aS0u#0S0v,4iR~PT%:a=7iTS0wPnQ0MP~PnPrPaO1S0xO1R~,4iPnPnPnQ0NPiPi%1iS0yQ0vP~PnPnPqQ0uQ0xPnPrPaPa%1aDEEHM:SPTPTQ0PGUP?DfS0xQ0w125fS0u%?iRfQ0u#0R~/9uS0vPlPoPmQ0uP~%1~S0zPfPrPiO1PnPrPiPiQ0yDEM9CQ0<DLS0yQ0v125hS0{#<S0|Q0{#0S0}#;S0~f^Rf#\S10Pf%:fS11PfPfQ11D[S12f_Ru#:S13PB20kQ1S14&0=QS15%;1&0=T[S16[S17%;QS18g01;7S19B0jQ1<UW[S1:Q18Q19%;T[][S18P<g01TH20i>Q'eQ15eO1S15Q16Q0]#AR1#vS0]Q0\#vS0\Q0`'I'IS1;#jS1<%A1R1#A#vS1=%v1R1Q0]Q0^'I'I'I#jQ1=Q0^Q0\Q0_'I'I,I1'I#jQ1</]t']']']PG1{B@S1<?G;vS1=1{B?S0]?GAv7G<PwPx201x3%rH#tS1>=cxL5nx201xEQ1>=cxz5nx60;xPIPxQ05#rS1?#tS1@Q1>5cxPIPxAYxzyQ1@:06xy5nxS1APIPx201xF1s{LS1B1zB4S1C5Yx5nx1zB7RH=Yx{60;xPI1s{yS1D1zB|S1E'sQ1C5YxQ1D9YxH60;xFhFhPJP}b7b8b9X1BX2BXBBXDBXQBXJpX`pXap19@AS1C20hD@60g?19A?S1F%;AS1G?MA@S1HPKPAPDP4187AI0M14@?RH?7|4@0O7H[[[[^1B^2B^BB^DB^QB^Jp^`p^apP9feR7#;fdR4$0f&0=4P@P4f`S1I,25S1J#0S1KP2P7P?P3P8PRO<b3bObrbOb<b:b4b6b5Q0600ejQ0qQ0xQ0wQ0yQ0vQ0|Q0~Q10Q12Q13PBQ0bQ1;,I1#j/]t']PGQ1=Q0c7G<PwPxPxQ1@00NLPIPxPxQ1B1zBQQ0660dBS06+02PIPxQ1APIPxQ0fPIQ1D9YxzQ1DQ06606x5nxFhDZDZPJP}b7b8b9X1BX2BXBBXDB19;AA7<@TQ1HQ1G1=HT-0PH[[[[^1B^2B^BB^DBP9P<1V5sPFfbS1HP@P?PEPVO8b3b<b:b4b6b5+0cE^:0bsjJ00Q0s=~0YPf16s@O1P0Q00P5Q0r20L59Rj930;XC5,N5]AP9A~0jYP520L5;=30jXC5P<20L5<,e0S0rH0:WAXC5P9O1A30YYRH#l1e0YPHA30YjXC5,N5P<P9O1+1GbiWAn10110300021010100P<O1bKbAbAbAWEX0BQ0FPiQ0pO1=30jXC5,N5[^0BQ0R,D91Fe;S0F159AS0pQ1I16uWO1=30g[^0C'@X;6,N6[S0sXSCQ0?,25S0q,DMP6A3CeM159MRHPu16fWO1=30gS1G[^0C'@X;6Pd125d=3CMP0Pf16sWO1S1AP5PdP<DP\H^0C1eCM15<M1=W>RQP<PW%1WS1B1eB>R1H1FP9CBPQQ0{,DMQ0~P1Q0{Q0}Q0}#1H1EPACBQ0~%?fR1#0S0~,4uRQPTQ11=7uTS0}PnQ0MPQPnPrPfO1RQO1S1=,4uPnPnPnQ0NPuPu%1uS0bQ0~Q1=PnPnPqP1PQPnPrPfPf%1fS1=DES0~EHM:SPTPTQ0PGUPEDfQ0}Q0n%?uS0}Q0oQ13'9S13PlPoPmQ0nQ0oQ0o#1Q0}PrPuO1PnPrPuPuQ0bDEM9CQ0>DLQ13%<?S13%0?S0b#;S0}faS1;#\S12Q1;Q1;#:S10Q1;Q1;Q10D[S10Q1H#:S0|PBPtPG1{B<S0v9Gv<PwPxPxQ1@-02zPIPxPxQ1@009zPI201xADZDZPJP}b7b8b9X1BXJp1=<>PA[\^^1B^JpP9P0ffR>%0FRz,67O1P5PdPFDPPzPAP3O4b3b<b:b4b6b5bGbFXEHX0CCgH0:W\Q0s%A<Q0U'DP<Q0u,D;%0;S0y/8~P;Q0yQ0y#1S0wQ0uP~Q0zEd%A;RHQ0u'DQ0y?7|~RzPHQ0tXIBS0xQ0yO1Q0xP;Q0yQ0wCxQ0uP~Q0zEdP9CBPz%?sS0z#0Rz,4fR~PTQ0Z=7fTS0wPnQ0MP~PnPrPsO1R~O1RH,4fPnPnPnQ0NPfPfQ1=PzPHPnPnPqQ0zP~PnPrPsPs%1sDEEHM:SPTPTQ0PGUP3DfQ0w125bS0wP1Q0w#0R~Q11'9RHPlPoPmQ0wP~%1~P1PQQ0~M9CPcDLPHQ13Q0}125iS0~#<Q0~#WQ12Q10Q0|PBPtPG1{B;S10?G<vS12PwPxQ1E,s{S11=YxyS0zPIAYx{yS1=CaPJP}b7b8b9X1BX2BQ0t/8<18<;S0t[^1B^2BP9Q1K%0KP3O3b3b<b:b=b4b6b5bGCXO1159@Q1;Q1I/6WO1=30gS1L[^0C9OeAX;6,N6Q03P6159?Q1HQ1;/6WO1S1M=30g[^0C9Oe@X;6%A?%AD,59fcRHQ1H/6WO1=30g[^0C5OeX;6,N6P91593P416HWO1=30g[^0C9OeDQ01Q0B/F3159EP7164WO1S1NAJ5A<S1O530[^0C%AF%AK,59fgRQ14>WS1P$04O1=30g[^0C5OeX;6,N6P9125AS1Q/FF1598fhR116QWO1AJ5D<S1R530[^0CPN%08S1S125?S1TP8Q1T#0S1UQ1S'9R~PlPoPmQ1TQ1UQ1U#1S1VP8Q1SQ1S#1M9CP<DLP~%A2R~Q1H,25S1W'D%02S1XQ1W#0S1Y77|RzP~Q0xQ1XO1Q0xP2Q1XQ1X#1CxQ1WQ1YQ1Y#1EdPKCBPz%?QS1Z#0Rz,41R~PT%:QS1[=71TS1\PnQ0MP~PnPrPQO1S1]O1R~,41PnPnPnQ0NP1P1%11S1^PzP~PnPnPqQ1ZQ1]PnPrPQPQ%1QS1_DES1`EHM:SPTPTQ0PGUPRDfQ1\1254S1\%?1R~Q1\#0S1a%:1S1b'9RzPlPoPmQ1\Q1aQ1a#1P~PrP1O1PnPrP1P1Q1^DEM9CPbDLPz%<O%0OS1^#;125>Rz#<%0zS1c#;1258S1d#<Q1d#WflRz#\Pz%:zS1ePzPzQ1eD[fmRb#:S1fPBPtPGQ12PwPxQ0fPIPxQ0zPIQ0iFhPJP}b7b8b9X1BX2B14<|S0z/8;Q0m[\^^1B^2BP9fkR~,25S0m#0S1g%0VS1hP?PEO4b3b<b:bHb=b4b6b5bGb>O2P1Q1X,6QO1=30jXC5,N5Q03P5fiS1X%0N,61O1=30jXC5Q08#A%AO,59Pz16~WO1=30g[^0C5OeX;6,N6P9P~fjS1iQ1^'6O1=30jP6%ARS1^%AS,59foS1jfnS1k/6WO1=30g[^0C5OeX;6A_5<dS1l9b5KR11251S1m%APS1n'FQ1^,59S1oP0Q1k16bWO1P5A_5Ad9b52P<DP[^0CPC125KR1Q1l,25+0_S1pQ1^,F9X@CQ0[-0_1S1qQ1n'F%01S1r/4|S1s%0PS1t/4|S1u'9PlPoPmQ1qQ1sP1Q1rQ1r#1S1sQ0[P|%1|J1DQ1nQ1uQ0xPPQ1tQ1t#1S1uCxM9CP1PPQ1rQ1t'9S0[PlPoPmP1Q1rQ1sPPQ1tQ1uM9CPDDLQ0[Q1^125QS0['D%0RS1uQ0[#0S1t77|S1sQ1^Q0xQ1uO1Q0xPRQ1uQ1u#1CxQ0[Q1tQ1t#1S1^EdPOCBQ1s%?zS1s#0S1q,4bS1vPTQ1e=7bTS1wPnQ0MQ1vPnPrPzO1S1vO1S1x,4bPnPnPnQ0NPbPb%1bS1yQ1qQ1xPnPnPqQ1sQ1vPnPrPzPz%1zDEEHM:SPTPTQ0PGUPUDfS1vQ1wQ1X,25S1s%?bS1xQ1s#0RzQ1f'9S1fPlPoPmQ1sPz%1zQ1xPrPbO1PnPrPbPbQ1yDEM9CPuDLS1yQ1f%<X%WXQ0m#<S0mQ1g#;S1g125PS1x#<Q1x#0S1s#;fqRb#\S1qPb%:bRzPbPbPzD[S1zfrS1{#:S1|PBQ05$1C-1BBS05Q0_60^BQ0`'I#j/]tS0`PGQ12PwPxAcx{yS0_PIQ11Q1E,syS1}5cxCaPJP}b7b8b9X1BX2B199<S11Q0z14;|'9[^1B^2BP9%0[1V5XPFO3b3b<b:bHb=b4b6b5bGb>CXQ1pQ1n'FeQ1mQ1l:1?5KE^Q1o21><S1F<SRz%lz+1=Q04Q0:,F;Rz%lzP0fpS04Q1j%0AS1l'6O1P5Q08A_5?d5b5PADPP91FAXS1mPCPV%AUS1p,59P0fsRXQ1{/6WO1P5A_5EdS1n9b5RP<DP]EX0C%AV,5VP0A_53dS1~Q1x-0]U5J5PXQ1{Q0;#0S20'6O1Rz=309XK0PCPUP0PzP5Q1nQ0;00]9DPX@CPCPMP0PzP5Q1nP9DPX@CPDP0Q1{%0URz,6bO1P5Q1~PMDPe21<UU&1;UE^Q1xP2E^Q1~9b5P=J5UP5PPQ1~PUQ1x/DUQ1s/8zQ1xQ1sQ1s#1PUPz%1zS1sEdQ1p,5U14z|S1x,=zS1~PUPzQ1sQ1pQ0xPzO1S1nQ0xPUPzQ1sCxS1sEqP9CBQ1~125RRRQ0;%0RS1~Q20'9S21PlPoPmPRQ1~Q1~#1Q0;Q20Q20#1M9CPNDLS20Q21%AZS22Q1k,25S1k'D%0ZRRQ1k#0Rz77|S23Q22Q0xPRO1Q0xPZPR%1RCxQ1kPz%1zEdPUCBS1kQ23ftRz%?XS0x#0S22'4RRPT%:X=7zTS24PnQ0MPRPnPrPXO1S25O1RR,4zPnPnPnQ0NPzPz%1zS26Q22PRPnPnPqQ0xQ25PnPrPXPX%1XDEEHM:SPTPTQ0PGUP`DfQ24Q04,25RX%?zS04%0XRR%:zS24'9S25PlPoPmPXPR%1RQ04PrPzO1S0xPnPrPzPzQ26DES26M9CP>DLQ25%<_%W_Q1{,25RR#<%WRQ0;,25RR#<%0RS0;#;fxRR#\PR%:RRXPRPRPXD[fyS25#:PBPtPGQ12PwPxQ0_PIQ1=CaPJP}b7b8b9X1BX2BQ11Q0t[^1B^2BP9Q0>#01V5_PFO3b3b<b:bHb=b4b6b5bGb>bFCXI18E^WEP@P9PAK17WRP9O1Q1m#lP0AJ5O@Q1{Q0b,6bO1=309XK0PKP@15@V%0@RXQ1h'=P@PX%1XS1{PVQ1hQ1h#1S1mEq1F@VS0>#lQ1h,9XS1=#lS22Q0>Q1=PlPoPmP@PXQ1{PVQ1hQ1mM9C416P9CBS1=Q22Q1p,5?Q0bQ1x'=S1xP?Q0bQ0b#1Q1pQ1nQ1sEqP@CBS1sQ1xQ20Q21Q1kQ23Q1j,25S1j,D\S1n159]Q2516RWO1=30g[^0C9Oe_X;6,N6S25[%0\R]Q1j#0RV'8S1pQ25[S25Q1n159_PRfw/6WO1=30g[^0C9Oe[X;6,N6R[Q1pP[P\P]%1]Q1jPV%1VEd&0E[J15PZCBS1jQ25fuRZQ04#0R['4RVPTQ24=7ZTR]PnQ0MPVPnQ0xO1RV,4ZPnPnPnQ0NPZPZ%1ZRRP[PVPnPnPqQ04Q0xQ26EHM:SPTPTQ0PGUQ0<DfS0<P]125bRb%?ZRV%0bR[%:Z'9R_PlPoPmPbP[%1[PVPrPZO1PnPrPZPZPRDEM9CPQDLS26P_%<8S0xQ1S#;S04%<`S24%W`S1p125zRz#<S1n%WzS0>125\R\#<Rz%W\R\fzR`#\RRP`%:`RVP`P`PVD[RVf{#:R`PBQ14Q17Q1:Q18Q15Q16PtPGQ12PwPxPxQ1}-09{PIPxQ0_-0\xPIQ0hCaDZPJP}b7b8b9X1BX2BQ0z,=919<;S0zg01TnS1}[Q0l[[^1B^2BP9Q0E#0S0lQ1hPOPPO4b3bPbObPbdbZbbbHb=b4b6b5b]bGb>bFb_CXO2A_5DdR[9b5O=J5@P5POP[P@125OR[,5@%0[Rb,=XP@PXQ1{P[Pb%1bEqQ1=Q22Q1sQ1xQ20Q21Q1kQ23Q1jQ25Q0<P]Q26P_Q0xQ04Q24Q1pQ1nQ0>PzP\PRPVP`PBQ14Q17Q1:Q18Q15Q16Q05Q0^60^BQ0a'I#j/]tPGQ0cQ1<7G;Q0]9Gv?7G<PwPxQ0fPIPxQ1?#r#t9cxLPIPxPxQ1?#R#tR`Q1E'sRV002LPIPxPx20Ny`PIPxPx209{VPIPxAcx{`-0\xPIQ0hCaDZDZDZFhPJP}b7b8b9X1BX2BXBBXDBXQBQ1FA7?|@19@D143|,=@19?EQ1}[1=D3[[[[[\^^1B^2B^BB^DB^QBP9P@Q0lf|,V51V5cQ1hPFPKPNQ08POPPO;b3bPbObPbdbZbbbHb=b4b6b5b]bGb>bFb_CXI14E^WlP9O1n200110500021110411100buWEX0CCgH0:WhXC5P<P9O2n2001000000121102000bRWYW^P<P9O2n2001000000121000000W?X;6P<P9O2n2001000000121102000bRW\WjXSCP9H13XSCQ0q,D9Q0FQ0pQ1G[^0C'@X;6,N6[^SCP9Q0qQ0qQ0q'DQ0q#0RO/8OQ0qPO%1ORcQ0qPOPcEdQ0QQ0LQ0TQ0SQ0VQ0WQ0XQ0YQ0ZPBPtPGQ0vPwAYx{{PJP}b7b8b9X1B1899^1BP9Q0oO1b3b<b:b4b6b5CXO2Q0RQ0U,59Q1A=30g[^0C5OeX;6,N6Q03P6Q0UQ0u,59Q1G[^0C5OeX;6ATsiaP9Q0{Q0w,59Q1L[^0C5OeQ01Q0BQ0w'FQ0n,59Q1MQ1O530[^0CQ1;Q1I;TuP9Q1QQ0~'F125fRf,59Q1NQ1R530[^0CP6P=P7P4%?HRe@0Y9:H0@XU6P?P=P4PHQ1H#?Rs@0Y?:R:H0<%K:9k4HS1R&08:RaP=P4PH%Q:C|S1NPsPCQ02PC125uRuQ1P/8TQ1l9M^9P0P~Q1XP<PYDi[^0BQ199O1A]A]NQ0?%0u=74TQ1;,25Ru#0R:9M^9P0Q1XPQP<PYDi[^0B125ERi/FuRgQ19Pg%0iR{/9:RcPlPoPmPiP{%1{PuP:%1:M9CR{PgPcP{P@CBS19PcQ1W#<Q1Y#;%<1Q1r#;Q0`PGQ12PwPxQ0_PIQ0_CaPJP}b7b8b9X1BX2BQ11Q0z[^1B^2BP91257R1#0R{1252Rg#0RiPAO3b3b=b4b>CXg00I9CgWAWNn2002100000000101PNP2O2btPaeP6P?P=P7P4P9C|XM6%;HS11Q1U=7HTS0z125D,59Ra167WS0_,o>AJ53<R2530S0`[^0CS1r'@Q1TPfQ1U%0fRO'9R|PlPoPmQ1TQ1UQ1VPfPO%1OM9CP<DLROP|%0eR`,44RVPT%:H=74TRRPnQ0MPVPnPrPHO1RVO1R\,44PnPnPnQ0NP4P4%14RzP`P\PnPnPqPePVPnPrPHPH%1HS1VDEEHM:SPTPTQ0PGUPNDfRVPRQ1J%?4ReQ1K%:4R\'9R_PlPoPmQ1JQ1KQ1K#1S1UPePrP4O1S1YPnPrP4P4PzDES1WM9CQ0EDLRzP_%<uRu%;:R:125FR]#<Rb%W]R]%\QR[PQQ1[PQPQQ1[D[RXQ1bPBPtPGQ0vPwPxQ0fPIQ0fCaPJP}b7b8b9X1BPk\^^1BP9P~Q0CO2b3b<b:b=b4b6b5b>S0CQ0zQ1rPCPfQ0D=74TX@CPOP|PVPRPzP_PuP:PbP]P[PXQ1bPBPtPGQ12PwPxQ1DQ065YxRfPIPfCaPJP}b7b8b9X1BX2BS06A79<TA7<;T[^1B^2BS1DP9Q1cP~PUO3b3b<b:b=b4b6b5b>Q1TP<E^P0P2Q00P5P0P9PjQ0y,6>-0F=n10110200021010100AJ5E;RU530XK0P2P01e09A30U9Q00P5AJ5K@=309Q00P5P0P<PjQ1XQ0b'6-0F=n10110200021010100=30<]LP<AJ58?=30jQ0rWLXC5P9O1AJ5FA=30Yg001Gp4p710Rj&0?9RUQ01&0J;AJ;<9&03;3312A;/D<[R212;</D9&0JAAJA;<&03A33Rf[12@A/D;\fB11;<9P<n2001000000120000000X@CWMWTP2^@C^MU^TjP9P5P8P?P<O4Q1d/D?1DgD%0DR8,8iRjPgPi%1iPDP8%18EdP9CBPj125NRj,53%03R8%0jRU'=R2P3P8%18PjPU%1UEqPDCBP2Q08,25R2Q0[%02R8Q1t'9RfPlPoPmP2P8%18Q0[Q1tQ1^M9CPKDLPfQ1vQ1wQ1yQ1fQ0xQ04Q0mQ1gQ0:,25Rf#<%WfQ1qQ1zQ1|PBPtPGQ10?G;vQ0v7G;PwPxPxQ1@-09LPIPxPxQ1@002LPI201x@DZDZPJP}b7b8b9X1BX2BXJpQ0IQ0tP@[[^1B^2B^JpP9Q1u,6Z-0F==30YQ1uQ0;PFPKO5b3b<b:bHb=b4b6b5b>bFbkbLb?WLn10110300021010101P9O1bLbKP>Q0_O1P;P<Q1J,5<Q1K,=WP<PWQ1BQ1JQ1KQ1UEq1253R3,5<%03R=,=WRZP<PWQ1BP3P=%1=EqP9CBPZQ19Pc%?>RZ#0R=,4QR3/8TS1B%:>RW,4QRL/8TRfPnQ0MP3PLPnPnPnQ0NPQPQQ1_P=PWPnPnPqPZPWPnPrP>P>%1>DES1UEHM:SPTPTQ0OGUPPCBPf125HRWQ1Z'FS1K%0WRLQ1['9R8PlPoPmPWPL%1LR2Q1ZQ1[Q1`M9CPhCBP8Q13Q0}%<1%;{%<j%;U%\~P~%:~RUP~P~PUD[Q1ePBQ0\Q0a'I#j/]tPGQ0dQ1<?G@v7G<PwPxQ0fPIPxQ1>9cxyPIPxQ0ePIPxQ0gPIQ0hFhFhPJP9P;Q0jQ0kH0Qb7b8b9X1BX2BXBBXDB19;@Q1C1=A?1=@?[[[\^^1B^2B^BB^DBP9P<Q1~Q1i,V5Q1SP?PDPEPFO8b3b<b:bHb=b4b6b5b>bFCXO2E^Q0`eXEaX0CCgCgAb5?d20K5?E^Q1NeCgPCPsQ0D9k74X@CQ11%0sRC,4HR4/8TR5AM^9`R`167<R7-0>>=~0Y[^0BRY'@Q0CP5PYP5Q0|,4HR5/8TPnQ0MP4P5PnPnPnQ0NPHPHQ1VPCQ0|PnPnPqPsQ0|PnPrQ1HQ1HQ1H#1DEEHM:SPTPTQ0OGUPOP|PVPRPzP_PuP:PbP]P[PXQ1bPBQ06Q1DP9P<P~PDO3b3b<b:b=b4b6b5b>CXPSP7PNP<%0eRN,=<R7,@kRS1=<\RD,@kR~PkP7PkPDQ0HPnQ0JP<P<Q0KPNP\PnPnPqPeP\Q1WEHL0IJ0APSP~PkP7PkPnQ1YO1R7,=<Q0GA3pkke:0[kkPnQ0JP<P<Q0KPNP7PnPnPqPeQ1YQ1WEHL0IJ0AP9CBP~Q19PcQ1BPfPnQ0MP3PnPrP>O1R>O1Rr,4QPnPnPnQ0NPQPQQ1_P=PrPnPnPqPZP>Q1UEHM:SPTPTQ0PGUPPCBPfQ1KP8PlPoPmPWPLP2Q1ZQ1]Q1`M9CPhCBP8Q1\#<Q1a#;%<g%;iQ1i#\Q1iQ1i#:RiQ1iQ1iPiD[PUPBPtPGQ12PwPxQ0iPIQ0iCaPJP}b7b8b9X1BX2BAM^9<AMk<;[^1B^2BP9P<PKPEO3b3b<b:b=b4b6b5b>bFCXO2O2XE`X0BCgCg20HsM&0GsE^Q1ReCgH0:WYW^P<P9O2n2001000000121000000W?X;6P<P9O2n2001000000121102000bRbfbmbAbNbXbWQ0?Q0AQ0@3TeWgWpWAWNP<P9O2n2001000000121000000W?WnP<P9O2n2001000000121000000W?WXWWP<P9O2n2001000000121000000W?WeP<P9O2n2001000000121000000W?WqWoP<P9O2n2001000000121000000W?P<P9O2n2001000000121000000W?P<P9O2n2001000000121000000W?XU6P<P9O2n2001000000121102000W?X@BXTBWsWco"). Qed.
Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> 0x60d000 <= A -> dc_at m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "h01Ah11Dh21Hh31Wh41mh52m'h61np;1p;3p;2p;7g00;oj10Tg00MQj16Tg00Moj17Tg00NRj1>Tg00O4j3;Tg01O[j3:Tg00=7j13Tg00nnj15Tg003>j22Tg003Zj28Tg0061j29Tg01UKj3=Tg01Uej7<Tf0R0#0#0p=4%00#0#0#0p=1g00KlR1#0#4R2#0#4R3#6#7%62#7#>[R2g00DeR4f3R5f1R6;;0g00bcf4R7;:5%31#0#1#3#3#0#3#1#1#1#5R1/25f6f5P7P5f2P6g00H[/271875%43#1#1#5'2'91217;=0F<W2W3W1X64W0X52W4o"). Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall a : word, 0x60d000 <= bv_unsigned a -> seg_rom asegs a = None.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01xi001xh17__arithh24__ffh34__p1h48__varmaph55__with64__x1h72Hah81ah91mh:1nh;1oh<1yi011bi021li032l0p;1p;2p;3p;4p;<p;6p;7p;8p;Bg00;oj11Tg00MQj16Tg00Moj1CTg00=7j15Tg00nnj19Tg01CMj28Tg003>R0j20Tg001bR1j1BTg00NRR2j1ATg00=\j1:Tg01FSj2DTg00?fj3<Tg00>`j22Tg01V`j3WTg0047j1VTg009ej1UTg00:Cj1TTg00:aj1MTg00Uej2@Tg00BNj4=Tg00>>j2LTg00?:j2KTg00@@j3JTg00@_j4ITg01WcR3j1>Tg003ZR4j24Tg005Wj27Tg01?Gj1HTg01@Nj4GTg00S6l<ETg01>aj3OTg01XAj6PTg008ij2QTg00;Lj2RTg00mRj6STg00C]j7`Tg00DAj8_Tg00VHj4^Tg01Xij4]Tg000ij6\Tg01N?j2XTg00C9j7YTg00`Xl<ZTg00a=lB[Tf0R5#1#1p=;%15#1#1#1p=3f1R6g00EjR7g00FIR8P8g00FiR9P5g00GIFYp=?g01YmR:g00DeR;P;P;P3P3f5R3f4R<f3R=f2R>P6P5M<Zp=FP;P;P;P;P;P;P4P5P6P>P4P=P<P3f6f7f8f9MB[p=Ng00KlR3#1#;R<#1#;R4#6R?#C%53#1#3#5#5#1#5#3#3#3#9R@18?5'0%6<#CR<#BRA#ARB%:A%A<RCP2PAPCP5P1P<PCP5%:<R11D<6n10110200020020101103P1n10110000021010200;<1X;B12C1g00bcRB%63R<7W6P6P<g00J5RA#VR2%BARA%U;%T;RD%M;REP;%93RF,@;RGg00ECRHPGC='?1LE9RGP5P>g00LQRIg00M1RJ'21K5>=<IJdg00H[=J;6CIRJb2b4b510FFP5b1%><RI,0Fe18?6RK/4IRL%;4#3#3#9R4'0RM10@KRN'714KFRO/04RP/7NPMPNPPPNP;P;P0P5X0;RPP01065#HX<;X0;PLPOPPPPPPP;P;g01Sd1465CG,2;X9;X:;PKPK12;KPIPFPPPP%>5,2;X0:P<PF12;FEFM:NP4P412;4M<Ep-0R</2N9ONNEPP2PA1Q;6PDPEP7P8P8P9P;1@;@PH1R;3C=,?ER3%:8PEP7P8P8P9PEP7P8P8P9P=ESP3F`G_PGPJb2b4b5X6;X3<10@510@6,7>[^6;^3<P518?>R?/4F/04P?P6O3b1C^C]E\1XB6=<C1eW7W8o"). Qed.
Lemma mrd_high : forall m a, 0x60d000 <= a < 2^64 -> mrd asegs m (wa a) = m (wa a).
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with62Hah71ah81bi001bh91mh:1oi011oh;1zi021xp;1p;2p;3p;4p;6p;7p;8g00;oj11Tg00MQj1=Tg00Moj1?Tg00NRR0j1YTg00=7j12Tg00nnj19Tg003>j24Tg01=Nj2GTg00acj28Tg0061j27Tg01A1j1:Tg01FSj2ATg01N?j2XTg00?fj3<Tg00>`j2@Tg0047j1UTg001bj1TTg008ij2NTg00:Cj1LTg00:aj1KTg00Uej23Tg00;Lj2HTg00BNj46Tg00mRj6FTg00=\j1ITg00>>j2ETg00?:j2JTg00@@j3DTg00@_j4CTg01CMj2MTg01D7j3BTg01DZj2OTg000ij6PTg01ZKj2QTg01POj3RTg00C9j7STg00b?j7WTg00DAj8VTf0R1#1#1p=0f1R2g00EjR3g00FIR4P4g00FiR5P1g00GIFSp=5f2R6P3P4P4P5P2P1FWp=;f3R7P3P4P4P5P6P2P1GVp=>g00KlR8#1R9#0R:#1#0R;#=R<#?%=:#?R:#YR=[g00DeR>%28#1#0#0#2#2#1#2#0#0#0#0#0#0#9R?/41R@%99R9%9;'GR;,81'7RAP6%:2RBO1RCP=P0P:P0P:P=P11A:1R0g00bcRD%:7'Xn10110200021010000=<=1P11@=0X8:P1O1%:6R:P>P6P@X;>p-0R0g00J5RE#URF%TERE1N>2RG%L>RH%K>RIP>13>?g00ECRJ1H>8R8C6,5IRKPIP3P4P4P5P7EF5;I%I4R4PKC>1EI5R5P1P6g00LQR3g00M1RL'@1J16=<3Ldg00H[RL=D>2CCR3b2b4b5X0>W317@214?2[^0>^30P1187;P7P6O3b11M<:PFPEPGPHPIP>P8g00f<13>9=B><C6,5IR<9;IKP4P>13>LPJP8C6,5I=;I<C>P5P3b2b4b5X0>14L2182;'7\A^0>P1P7P6O2b1,O6EP'Qn10110100021010001b:ARD6B=<=CeW6W7W9o"). Qed.
Lemma rw_C1_high : forall m a (b : byte), rw_cells asegs m a [C1 b] -> 0x60d000 <= a -> m (wa a) = Some b.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "h01Hh11ih22BRh31xh47__arithh54__ffh68__varmaph75__with84__x1h91mh:2B0h;2B1h<2B2h=2Hah>2WFh?2_Hh@1ahA1bhB4cstrhC1nhD1ohE1yhF1zp;1p;4p;2p;3p;6p;<p;7p;Bp;8g00;oj1=Tg00MQj1STg00Moj1HTg00NRj1tTg0047j1OTg00_Ej4^Tg013\j4JTg00ZXj1@Tg00QVR0j13Tg014Sj4ATg00=7j1BTg00nnj1CTg003>R1j20Tg01A1j14Tg01FSj2:Tg00?fj32Tg015Ej1LTg00h_j1?Tg016<j4RTg017gj29Tg003ZR2j21Tg01=Nj2[Tg01=kR3j2<Tg01>Cj3>Tg0061R4j2GTg006Lj1ZTg00acR5j2ITg00>`j2;Tg019nj1XTg001bj1WTg009ej1VTg00:Cj1UTg00:aj1TTg00Uej2DTg00BNj4ETg00>>j2sTg00?:j2rTg00@@j3qTg00@_j4pTg00VHj4oTg01[Hj1lTg000Mj6PTg01?Gj1kTg01@Nj4jTg00S6l<MTg018Gj4gTg008ij2fTg00;Lj2cTg00<Tj3dTg01D7j3eTg00=\j1bTg00b?j7aTg01[ij3`Tg012gj1KTg004Wj3QTg01POj3_Tg00C9j7mTg00`Xl<nTg00a=lB]Tg00DAj8\Tf0R6#=#=p=5g00cXR7f1R8#K;Q6p=6%K8=Q76#?p=8g00bcR9?_86p=7g00dMR:g00DeR;P3P0P5g01R`g00JaR5g00H[R3f3R<f2R=P8P6M<Mp=YP8g00EjR>g00FIR?P?g00FiR@P6g00GIFmp=FP:P;P;P;P0P0f5R0f4RAP<P=P8P6M<np=iP;P;P;P;P;P;P2P6P8P=P2P<PAP0f6R2f7RBf8RCf9RDMB]p=hP<P>P?P?P@P=P8P6G\p=Ng00KlRE#=RF#5RG#=#5RH#SRI#H%SG#HRG#tRJ[P9P=P8%O7R7,66C^P4P9P<P=1687RKCJP9P<P=%@K#3CA%BE#=#5#5#B#B#=#B#5#5#5#5#5#5#CRK/0<P0%4AO11:G<52J[P6P9P0PA16<7CJP416A7R<#LP9P2P0%?<CRP9PBP21607#@#3CA10KBPD%4CO11:GB52J[[P61627#LP9PDPC18B7CRP4103D18C7,9G#3,1D%CFRF%CH'[RH'016D7RD#?,9G,<6f<RCf;RB%38R2'1#4'7f:R</87=>G852J[^1:'GP9PBP<%@D#3CA10KBf=RD%4CO11:GB52J[[P6103B18B7,9G#3,1C/0H18C7,9GRC,<6f?RBf>R</12#4'716D7RL#?RM=>G852J[^1:'GP4%3C,1D/0H19GM,<6f@RM11B2#4'718<7RD=>G852J[^1:P9PBP<%@L#3CA10KBfARL%4MO11:GB52J[[P619GD#3,1B/0H16M7RM#?,9G,<6fCRBfBRD/12#4'718L7=>G852J[^1:P9PDPL%@M#3CA10KDP=P5%Z5RM,<5%CERL,I3R91;;3PMPL1;;LR2CY18D7RD,9GR7#X%37,03g00J5R<#ORC%W<R<%V;%U;R4%T;RNP;1D;3g00f<RO1D;LRPCE'F1sN@RQP6P=g00LQRRg00M1RS';1r6==2RSdAq;38CpRSb5b6b7P9P6b4bBCo1<57eO2fDR7%35,1B#4'7A>GD552JP;1173fFR3%46'71:G752JXF;P6P7%l7EPfERD%47'71:GB52JPJ%4DRB,731:GD92J6XDJP6P3PBO1%3MRB,1DRJ/0H11DL/0HR7P;P;P1P6X3;R5P11086#kXE;X3;PJP5PLO1RJ,1DP5P5P5P;P;g01Sd1186Cj,;;X9;XC;PDPD1;;DPBPJP5P5%36,;;X3:PMPLP2EiM:hPHPH1;;HA2;HHeM<MP0CgP7PCP<1f;8P4PNP;1c;ERE=d;Pg00ECRP1D;F=e;IRICE,FN%b?RFPNP;1D;KPPPECE,FNRPPFPNP>P?P?P@PPP;PEPOPICE,FNFaCNCNPQPSb5b6b7X8;116L/0H10K810K=1I=H'G[[^8;P6fGP8PAO3b4b<9`3DEPb2b2W=W?W2W;P8P6O2n2001000000121000000W0W:P8P6O2n2001000000121000000W0W>P8P6O2n2001000000121000000W0P8P6O2n2001000000121000000W0XAGX@;W9o"). Qed.
End CANSEC1.
