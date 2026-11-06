(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module Tac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Cells OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Exec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Step OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Arr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Image.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Tac () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthc79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac7sum_natC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3minI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List<length_skipnK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells;cells_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells:cells_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib2CJ3Lib7Mh_00394Step8rw_cellsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells8cells_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem5wr_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00393Mem8bytes_atC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells<cells_wf_appC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell05C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells7cell_wfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac>mk_CB_cells_wfC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ3Lib7Mh_00453TacAmk_CB_cells_bytesC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells>cells_size_appC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac@mk_CB_cells_sizeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ3Lib7Mh_00395Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C79OSSVerify5KrLib2CJ3Lib7Mh_00395CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc79OSSVerify5KrLib2CJ3Lib7Mh_00453Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
Ltac map_cbv_get ::= cbv beta iota delta [tget mkR].
Ltac map_cbv_set ::= cbv beta iota delta [tset mkR].

(* [comment removed for export] *)
Ltac solve_load_image :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      let Ez := zlit E in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          let obs := eval vm_compute in (image_bytes segs Ez n) in
          lazymatch obs with
          | Some ?bs =>
              let RO := fresh "ROimg" in
              assert (RO : ro_cells segs m Ez [CB n bs])
                by (apply (ro_cells_image segs m Ez bs HI); [vm_compute; reflexivity | lia | cbn; lia]);
              rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
                by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
              clear RO; load_post
          | None => fail "no readable image bytes at" Ez
          end
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image ].

(* [comment removed for export] *)
Ltac simpl_arr_sizes := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.
Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac footprint_after_store segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

Ltac fstep := step.

Ltac fsteps n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fsteps n'
      | _ => idtac
      end
  end.

(* [comment removed for export] *)
Ltac destruct_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs PO
  | _ => idtac
  end.

Ltac destruct_ands PO :=
  lazymatch type of PO with
  | _ /\ _ => let H := fresh "PC" in destruct PO as [H PO]; destruct_ands PO
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call segs m ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac carve_frame n ST :=
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi =>
      let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
      destruct (stk_carve segs m lo hi n ST ltac:(lia)) as [ST' [junk FR]];
      clear ST; rename ST' into ST;
      let z := eval vm_compute in (Z.of_nat n) in
      change (Z.of_nat n) with z in ST, FR;
      (* [comment removed for export] *)
      repeat match type of FR with
      | context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
           replace (Z.sub (Z.add b c) d) with (Z.add b v) in * by lia
      | context [Z.sub ?b ?d] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
           replace (Z.sub b d) with (Z.add b v) in * by lia
      end
  end.

(* [comment removed for export] *)
Fixpoint mk_CB_cells (sizes : list nat) (bs : list byte) : list cell :=
  match sizes with
  | [] => []
  | s :: sizes' => CB s (firstn s bs) :: mk_CB_cells sizes' (skipn s bs)
  end.

Fixpoint sum_nat (l : list nat) : nat := match l with [] => 0 | x :: l' => x + sum_nat l' end.

Lemma mk_CB_cells_wf : forall sizes bs, length bs = sum_nat sizes -> cells_wf (mk_CB_cells sizes bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h04__p1h14__x1h24__x2h34__x3h44__x4h52bsh61nh75sizesh81Hh92H0h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB2z2hC2IHhD1mhE1shF1xhG1yp&0p;1p;2p;3p;4p;6p;5p;Bp;<p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p710p10032p4p710p8g003Nj1OTg003nj1QTg004Sj1iTg0051j1`Tg005Tj27Tg0064j1:Tg0073j2DTg0086j1ITg0098j1STg009Xj3KTg00:8j3^Tg00:Wj3\Tg00;5k204Tg00;LR0j10Tg00;lR1j2JTg00<Ij1Wj3?Tg00<cj2wTg00=Fj3qTg00=cj2ETg00>=j2gTg00>TR2j2MTg00?1j4cTg00?Xj1PTg00@=j25Tg00@Yj2aTg00A;j2BTg00AWj26Tg00B2j2ATg00BLj1_Tg00Bjj2]Tg00CKj1@Tg00Cjj2>Tg00DSj3RTg00E<j2[Tg00EZk103Tg00F8j4ZTg00FVk102Tg00G4k101Tg00G_j6~Tg00HCj2HTg00Hfj1yTg00IKj1xTg00Imj2vTg00JPj3VTg00K3j2pTg00KUj2oTg00LAj3mTg00L`j4lTg00MRj4TTg00N=j3kTg00N_j6UTg00O=j2nTg00OTj2<Tg00P1j2GTg00PNj2rTg00Q0j3sTg00QSj3tTg00R4j4fTg00ROj5uTg00S1lBLTg00SWl<dTg00T<j3zTg00Tej2{Tg00UQj4YTg00V<j7|Tg00V`j7}Tg00WDj7bTg00Whk800Tg00XLR3f1R4f0R53?p=3g00XkR6??45p=1P3P3P3P6P6P6g00YIP0P0P0P1g00Yif5R1f4R7f3R8f2R9P4P5MBLp=jP3P6P5P0P4P9P8P7P1f6R:f7R;f8R<M<dp=NP3P3P3P6P6P6g00ZLP0P0P0P2g00ZlP1P7P8P9P4P5MBLp=eAz645p=2g00[O,{5p=8g00\;R2?K45p=9P6P4g00\gP5CYp==P4g00]NR=g00]mR>P>g00^MR?P5g00^mF|p=4P9P=P>P>P?P4P5F}p=FP6P4g00_MP5CYp=CP9P=P>P>P?P4P5Fbp=XP8P=P>P>P?P9P4P5L00p=;P3P3P3P6P6P6g00`4P0P0P0P:g00`TP1P7P8P9P4P5MBLp=h%O3R0P3g00a;R@#QRA#QRB#Q#i#`RC#ORD17C5RE%:4'31D94#I[]5RFX70%S3RG#:,3Eg00a`1DG4#IeW8X5DAK389#:,3EA^C74,7CRE/37A\C74RG,D8#IP317C4RH-047RI1351X6313I7%07RJ%0HRK'JRL/1J%W3RM%W6RN%04%05'113451w453qXG3XF3ROPIPLP7PJ1E6JRLPHPK1E6KRIEjP7PJPLM9N%:8RP,g7RQ,3H%0PRR,MJRS,1KRTPMPNPOPHPKPIPQPSP7PJPLPPPR1E6RRSEeM9NP5CcRQPT17C9RU#PRVg00b<RW%0U'5RU%:1RX#PRY%0X,5WRX%P;RZ%0;,5WR;%0<R[17C1#0R\'a1B[\1J[\R]/1['615\[11]\'6'Af9#0R]17C:#0R^'JP6p-0R_%_@,]6R`g00bZRa#@Rb#@Rc#@Rd,>6Re5R6Rf1>6cRc1>6bRb9R6`1>6aRa'2R`'2'2#8%@d,>6Rd12ea'2#812fa#8%S2Rg'9'9'9%O2R2P6P61[67P9&036CZP41[68CZRh&026Ri&016RjPjP=P>P>P?P:E~R=1H6@Rk1H6ARA'=,4jRl5Fj%y@,H6R@/CA,4j1=k@,4j5Fj5Xj%x>R>Pj1v6WRm1H6BRB'C,4jP>PjAV6AB,=@,4jP>PlC;C;C;1pj?R?P5P9g00c9Rng00cYRo'E1o59=?nodAm6W4ClRob<b=b>X16X26X36X46W01154,6715941159'6'A15W71M81,171187Rn[[[^16^26^36^46^0_P5f;#0Rp17C<#0R<'Bf:#:#0RqP<PpP4P9P7P:O8b;bBb:bAb@b?b9CTPEAkC74EUP9PGP31nH7RE%:7,35X6313EP1<KJ,GWRr/1RPMPNPOPEPr1<45,GWXD6X66PHPKPIP7PJPLFhPPPRPSM9NPQPTPVPUPYPXPZP;1<\[R\,rW1BW\1GW\R[/1\'615\WA?6[W'6'A1<^],GWP612f`R`,2d#812ca,2e#812ba,2e#8%8`/9g'9'9'9P2PhPiPjAs6@BRi,=k,4j9Fj=1Cim,4j1=km,4j5Fj5XjP>Pj1CmA,4jP>PjAV6BA,=@,4jP>PlC;C;C;P?Pob<b=b>X16X26X36X46X0_1<98Ro,15,6715oWA?65W'6'A15W91M18,17Pn[[[^16^26^36^46^0_P51<<p,BWPpP<PqP4P9P7P:O8b;bBb:bAb@b?b9CT17CGAtC74EUO2CfAK378/D4#IeW8X5DXCFX70XE3P5DuW7o"). Qed.

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "p'0h01Hh14__p1h24__x1h32bsh45sizesh52H0h67__arithh74__ffh88__varmaph95__with:4__x2h;4__x3h<4__x4h=4cstrh>1nh?1xh@2H2hA2IHhB1bi001bhC5cstr0hD5cstr1hE1li011lhF1mhG1shH1yhI2z2p&0p;1p;2p;3p;<p;4p;7p;6p;5p;8p;Bp-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p710p10032p4p710p8g003NR0j1NTg003nj1MTg004Sj1jTg0051j1_Tg005Tj22Tg0064j19Tg0073j2ATg00d9j1BTg00<Ij31j1VTg0098j1JTg00=cj2;Tg009Xj34Tg00CKR1j1@Tg00;LR2j10Tg00e>j1wTg00>TR3j2<Tg00<cj2kTg00=Fj3iTg00SWl<\Tg00?1j4[Tg00?Xj1LTg00@=j27Tg00E<j2KTg00FVj1aTg00G4j1`Tg00Imj2QTg00HCj2HTg00IKj1^Tg00JPj3PTg00K3k203Tg00KUk202Tg00LAk301Tg00L`k400Tg00:Wj3~Tg00:8j3}Tg00e\j3{Tg00f9j3zTg00O=j2yTg00OTj2:Tg00P1j2GTg00>=j2uTg00PNj2oTg00A;j2XTg00AWj2FTg00B2j2WTg00Cjj2=Tg00BLj1mTg00Bjj2lTg00DSj3UTg00Tej2CTg00EZj1nTg00F8j4TTg00Hfj1hTg00Q0j3pTg00WDj7qTg00MRj4rTg00QSj3sTg00N_j6ZTg00ROj5fTg00fZl<xTg00UQj4RTg00V<j7eTg00G_j6dTg00Whj8cTg00S1lB]Tg00T<j3|Tg00V`j7bTg00XLR4f1R5f0R631p=5g00bZR79146p=Eg00XkR8g00b<R9716p=DA1856p=8P4P4P8P8P1P2P2f3R1g00g?f2R:P5P6M<xp=gP8P5g00_MP6CRp=IP5g00]NR;g00]mR<P<g00^MR=P6g00^mFep=3P8P5g00\gP6CRp=?P5P;P<P<P=P6Edp=OP1P;P<P<P=P:P5P6Gcp=>P4P4P4P8P8P8g00`4P2P2P2f6R>g00`Tf5R?f4R@P1P:P5P6MB]p=vP4P8P6P2P5P:P1P@P?P>f7RAf8RBM<\p=YP4P4P4P8P8P8g00ZLP2P2P2P3g00ZlP?P@P1P:P5P6MB]p=tA|856p=6P:P;P<P<P=P5P6Fbp=S%N4R3P4g00a;RC#MRD#MRE#M#j#_RF#NRG12F6RH%95'51A:5#B=1G5[]3RIX43%J4RJ#9,5HP0PF%EH%JFR0=1G5]0P512F0#E1;G0W0A4F56,2F#E12F5RK#@RL#E%0KRM%wCRN'<#DROP4P8%V4RPP2%V8R2%05%06'815561k563iXH4X?4RQPL1<6NX?8RLPMO1PLPKPM1;8MRLCgP7P91;89M<\P6C[PO12F:RO#LRR%0O,79ROp-0RSg00\;RT#JRU%NTRV1K85%a8RW%`8RX1Q89RY1H8CRZ'I,3X%^<R[PX1Q8N9P8Z/?Y,3XP[1OX1C>C>203X=R\P6P:g00c9R]g00cYR^';2026:=1]^dB01895H00R^b7b8b9X28W117961<5N#DP1[[^28^1SP6A4F?@91G012F@#0P5P:O4b6b=b5W0X3GXBFP5P6O2n10110100020021100101P6O11AJ5#B=1G5eW0X3GA441:#9,5HPGA~F@5RHA}F?:={F6=1G:XEGAzF@51A1H#BP:PHP41yK@RJ%9@,56X>4%91R0,5J%0@RN,:M,G9R]%00R_'8PPP2PQPJP]1:56,G9XF8X>8PKPMPLP@PN1;8NR]FvP0P_1;8_RJM9Y1u@0R`,5K1<N_Ra,8MRbPPP2PQPKPMPLP`PaP@PNP]P0P_PJEtM9YP6C[PbPRPO%9?RO#L%0O,79%LA%0A,7912F?#0%0B':RA,o91X9A1G9ARO/8A'F17A9%DO'F'W12F>#0f9#0':,G9P8%@7RO#@RA#@RR#@,=8%mC,l8Rb1=8RRR5U81=8ORO9U8b1=87R7'6'6Rb'6g00[ORJ'C1=8A/67,6R/CJ16O7,6R/CJ1CbJ=4TU54T54T54TPVP8P81K8@P:%n8CTP51K81CTPWPXPXP;P<P<P=1OX>%hC,H8RC1H8ERE5p8R=,?Z,3X5SX1I=Y,3X1?ZY,3X5SXFqP[PX1H8DRD,IY,3XP[PXAP8ED,?C,3XP[1?ZD,3XC>C>C>P\P^b7b8b9X28X:8X;8X<8X1S1::1R^,86,F@17^9%D6'F'W179:1<?1,8@181@[[[^28^:8^;8^<8^1SP612FB#0RBf;#0RS':,X9PSPBf:#9#0P5P:P@P>O8b6bIb@bDbCb=b5Cr12FHAsF@5EZO2EZA44@1/A5#B=1G5eW0X3GXAIX43XG4P6DfW4o"). Qed.

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h02bsh15sizesh27IHsizesh31ah41np;1p;2p;3p;6p;5p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p710p10032p4p710p8g003Nj17Tg003nj15Tg004Sj1<Tg0051j18Tg0073j21Tg00gcj13Tg0064j10Tg00<Ij32Tg00=cj26Tg0098j1;Tg00>=j24Tg00:Wj39Tg00N_j6:Tg009Xj3>Tg00ROj5=Tg00XLR0#7R1P0g00a;#5#5#5#<#8R2#7R3f1R4f0R5'1#3%04520]0R6X11g00bZ,60%;0R7/15#3%07520eX03P0f2R7#0R8f4R9/45f3R:#0,49520X4014:8,60A92:5R2,17#3P4P2O1E:A>0:7R:/15#3%0:520eX03X26X11X30P5D=W1o"). Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh31nh41lh52Hbh62Hwh73Hwfh84__x1h94__x2h:4__x3h;1Ah<2H0h=2H1h>2H2h?2H3h@2HshA3Hs0hB1LhC7__arithhD4__ffhE8__varmaphF5__withG4cstrhH5cstr0hI5cstr1hJ4junkhK1mhL4posthM3prehN4segshO5sizeshP1xhQ1yp;1p;4p;2p;3p;6p;<p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p710g0032R0p4p710p8g003Nj1BTg003nj1=Tg004Sj1]Tg0051j1XTg00hgj1wTg00iIj4ATg00jJj4PTg00gcj13Tg00;LR1j11Tg00kLj46Tg0064j1:Tg0073j2;Tg0086j10Tg00d9j14Tg00lIj49Tg00AWR2j2ETg00mIj2jTg00nOj2DTg00oOj1^Tg005Tj2HTg00<Ij1Zj3QTg00<cj2cTg00=Fj3bTg00=cj2>Tg00?1j4YTg00?Xj1LTg00@=j2NTg00BLj1aTg00Bjj2`Tg00CKj1WTg00Cjj2JTg00DSj3VTg00T<j3CTg00Tej2UTg0098j1vTg009Xj3ITg00E<j2_Tg00F8j4uTg00FVj1tTg00G4j1sTg00HCj2STg00Hfj1qTg00IKj1pTg00K3j2oTg00KUj2nTg00LAj3mTg00L`j4lTg00MRj4kTg010Pj3iTg00R4j4FTg00e\j35Tg011Vj2KTP0j6[Tg012_j3hTg00N_j68Tg00>=j2@Tg013hj2OTg0150j2gTg00SWl<fTg00UQj4eTg00V<j7dTg00Whj8rTg0168R0f3R3f2R4f1R5'Df0R65I035p=7g00XLR7?Q56p=<A5056p=21D45=I06p=Gg00XkR8?Q56p=?P7P8P6P1P5P4P3f4R1f5R9f6R:f7R;f8R<M<fp=MP8P5g00\gP6Cep=TP5g00]NR=g00]mR>P>g00^MR?P6g00^mFdp=RP3P=P>P>P?P4P5P6Grp=\g0178#Bg00a;R=#=R@#=#=RA#=#=#=#]#X%]A#XRA#w[%B0R0%BARB%B7P;P:P9P1P3P4P5C7CAP2P<P;P:P9P1P3P4C7RCCPP<P;P:%3C#1C6%:4/<9f:RCf9RDP<1;39/21,2;CA[P6PCPDP<P;P:P9P1C7CPP2P<P;P:P9C7RE#0f;RFPCPD%4EC9f<REPFPCPDP<P;P:C7#3#1C6%::/<Df>R:f=RGPE1;;D/2<,2FCA[[P6PCPDP<P;C7#0P:PGPEPFPCPDP<C7#4C9f?R<P:PGPEPFPCPDC7#3#1C6%:D/<EP21256#0%04RD%05RF'ERH[RI%06,EF1245#0RF[RJ%03/ED\F1j56RFP5n2001000000120000000X20X10PI^20^10P6P<AG:GERDP1O3%0<%0D'EP2f@RD#0AG<:G#0fDRKfCRLfBRMfARN1;G</2:'2CAP6%0MAGMND#0P21DLM#^%0NfHRDfGR:fFR<fERO1;NL/2M'2CAP61DOK#^%0K1HA<RM%:KRK'<RN%1MRL%1KRP'?%Z7RQ%Z8RR%15%16RS'?1<561c563bXQ7XP7RTPMPL1>8LPKPP1>8PRLM9M1<K:%1:RM,?PRUPQPRPTPKPPPLP:PM1>8MM9MPCCYPU1HA:RU/<D%1URC%1DRM'?RLPQPRPTPUPC1>8CPDPM1>8MM9MP4CYPLfIRL#Lg00b<RM%1L'N%::RC#L%1C,NMfJRC,HARU#L%1U,NMg00\;RU%a=,`8RTg00bZRR#WRQ#W,J8RP5V81J8QRQ1J8RRR5C85C8g00[ORK'UAV8TQ=C8R9C8P/UK%vU5IU3I%BUP81_84P51_83Cu%t8%s8RU1S8=RK%q=,S8R='T,RU%p>R>PU1S8@R@/T=,RUP>1TK@,RUC\C\1oU?P6P4g00c9RUg00cYR?'>1n64=QU?dAm8M5ClbDbEbFX88X98X:81?641?43RMPM[[^88^98^:8P6fMRM#1%:C#1fLR?,HA#1P1P9O5bCbIbHbGb<bACkPNP?fKRNPC1;O:/2<RO,2LR9CPP?PNPC%39R1#1C6%09P?PNPC%49R9C9P2PIPJ1234#0\HPFP6n2001000000120000000X20X10RFPJ^20^10RJP6PC1;<DRH/2:RI%0C%0IP;PFPJP61;:LRJPD%0J%0DAi:L4P3CFO3b0CFO3b0PB%4LR3%4O55APMP?PNP6C9X4BR4PBAGD:<RJ,2LRF#4P4PG%4J95A3R31KLJE[P?PNPCP3C9PB%4HR3%4:55AfNRGPMP?%4NR4=5A6C9X4BPBPDPGPMP?%4D95A695A4C9X4BP6P3Ah<D5E8%4I1KH:E8b5P91KLOE8CFP7%3LR9%3O'@PMP?PNPSC6X37RSP7%3FPSPE%3J,@9R91OLJE[P?PNPC%19C6P7%3HR9%3:'@PGPMP?%3NRN/@6#1C6X37P7%:<RCPGPMP?%3D,@6,@N#1C6X37RNP7PLPNP6PCPEE8P91g<DE8%3I1OH:E8b6P11OLOE8CFbBW?W>P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000b7b0W@W6W5W7P5P6O2n2001000000121000000W0P5P6O2n2001000000121000000W0WOXL0WJX37WMX;8WKWNo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh32Hbh42Hwh53H23h63Hwfh71lh81nh91Ah:2H1h;2H2h<2H3h=1mh>3midh?4posth@3prehA4segsp;1p;4p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9p1002Up4p710g0032R0p4p710p8g003Nj1BTg003nj1:Tg004Sj1DTg0051j1CTg00hgj1MTg00iIj4;Tg00jJj4?Tg00gcj12Tg00d9j13Tg00nOj26Tg0086j11Tg00lIj45Tg00AWR1j2<Tg00mIj2LTg005Tj2KTg00<Ij3JTg0187j2HTg00R4j4=Tg00e\j37Tg011Vj2@TP0j6>Tg00N_j6ETg00>=j29Tg013hj2ATg00;Lj1GTg00kLj4FTg009Xj3ITg0168R0f1R2f0R337p=0f3R4f2R5P2%G3CFp=4AI023p=8g0178#Bg00a;#:#:#:R6#:#:#:#D#C%D6#CR6#M[g00Xk%B0R0f5R7f4R8P41023R9,05C;P1f6R:P7P81052R;,04R<C?P:P7P8%2<C4f7R<P:P7%24%34'6/85,08C;P3f8R=P<P:1084,07C?P11078,0:R8#1f9R>P=P<%38C5f:R8P>P=10:7,0<#2C4f;R7P8P>%2<%3<'6/8:,0=C;[P310<:,0=#1f<R:P7P810=<,0>#3C5f=R<P:P710>=,08#2C4P1%19%15R9%12R>'<R?[R@%13,<>%1;R;[R>%14/<9\;1L23R;P2n2001000000120000000X20X10R9P@^20^10RAP3P:1078R8P4O3%1:%18'<P1%1<10:7#1fAR7f@R8f?RBf>RC%2<%3<'6/8:'0C;P3%1B10BC#1P9PAP3P7P8P2O3%17R7%18'<P1fBR8#1P7fGR7fFRAfER9fDRCfCRB#2%3B'6/88'0C;P3%1CRCfJR8fIRBfHRD%2ARE%3ARF'6/89RG,07RHC?P8PBPD%2HRIC4%1HP8PBPD%3HRHC5P1P@P>1045#1\?P;P3n2001000000120000000X20X10P>^20^10P3PD%27R>%37R;'6/8AR?%1D%1?R?P=g00XLR=1K6;;J>%1A1H75P2C=P?eC=O3b0%B6R?%3G976;fKR5P8PBP3C5X7?R4P?10A9R9,07R@#3P4P<%39976;R<1@79E>P8PBPDP<C5P?107AR<#3fLR4P5P8%3BR1=763C5X7?P3A76;FR;1@7AE>P5P8PB%3DRF=76;C5P3P4P5P8%2DR;/6F/87RF#39761C5eb3b3PH1@7GEEC=P=%2G,9>P5P8PBP3C4X8=RHP=%2@PHP:%29,9>R:1A79E>P8PBPDP:C4P=%2<P4P5P8%2BR</93C4X8=P319>ER>1A7AE>P5P8PB19;>C4P3P4P5P8%2F,9<C4eb4b4PI1A7GEEC=X<CW;P2P3O2n2001000000121000000b5b0W5W:P2P3O2n2001000000121000000b6b0W4W3W6P2P3O2n2001000000121000000W0P2P3O2n2001000000121000000W0X?0X>0W@W9W=WAo"). Qed.

Lemma rw_cells_forget : forall segs m A cs,
  rw_cells segs m A cs -> exists junk, rw_cells segs m A [CB (cells_size cs) junk].
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Mh11Ah21Hh32csh44junkh51lh61mh74segsp;1p;4p;2p;3p;6p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9g019CR0p4p710g0032R1p4p710p8g003Nj17Tg003nj12Tg004Sj19Tg0051j18Tg00hgj1@Tg00iIj40Tg00gcj16Tg00nOj24Tg0098j1;Tg009Xj33Tg00d9j15Tg019aj6:TP0j2?TP1j6>Tg01:gj4=Tg00e\j3<Tg0168R1f1R0f0R23<p=1g0178#7g00a;#2#2#2R3#2#2#2#9#8%93#8R3#@[g00Xk%71R4f3R5f2R6P0P2C0%73R3f5R7f4R8P5%66R9/42%;1R:531C0X43%50P8P5P6P:P0P:E:P8P5P6110:,1:C0P7P8P5%56,49=31:,1:C0[P4116:f6R9P7P811:2C0f7P9P7%68%58'4=31:,1:C0[X54P2P61?16E>P7P8P511:6C0P9P7P8%65%55'4=31:,1:C0[P2P6O1b0b0C=W2W3W1W6W7o"). Qed.

(* [comment removed for export] *)
Ltac finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac release_frame FR ST hi :=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    (* [comment removed for export] *)
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    transport_chunks segs m E bs;
    footprint_after_store segs m E bs;
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.

End Tac.
Module Walk.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0045.Tac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Walk () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib4Bool4Bool>eq_true_iff_eqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z9mod_smallC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula09K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes?RelationClasses?iff_equivalenceI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z8add_comm".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma carry_sym : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((x + y) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? y)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h06__sat1h14__p1h24__p2h34__x1h44__x2h57__arithh64__ffh76__sat0h88__varmaph95__with:5lemmah;1Hh<2Hah=2Hxh>2Hyh?1oh@1xhA1yhB1zp;1p;2p;3p;7p;4p;6p;9p;8p-1R0g0000R1p4p710p9P0g000\R2p4p710p9P0p1001NR3p4p710p9P0P3p4p7210p9P0P3p4p73110p9P0g001lR0p4p710p9p1002fp4p710g003CR3p4p710p8g003_j18Tg004Dj1PTg004bj2TTg005?j20Tg005[j23Tg0066j22Tg006Sj2_Tg0078j2<Tg007TR4j2XTg007nj2CTg008Nj21Tg008kj3>Tg009ER5j29TP1j2OTg009^j2?TP2j3fTg00:>j7JTg00;9j2aTg00;aj3`Tg00<Ej2^Tg00<fj2ITg00=@j1\Tg00=`j1[Tg00>@j2ZTg00>^j1YTg00?<j4WTg00?Zj1VTg00@8j1UTg00@cj2@Tg00AFj2ETg00Aij1STg00BKj3GTg00Bnj2tTg00CPj2sTg00D<j3rTg00D[j4qTg00EMj3HTg00Eoj1FTg00FNj2ATg00G7j3NTg00G`j2mTg00HLj3lTg00Hlj1hTg00IJj3gTg00Imj3LTg00JPj6KTg00Jnj1eTg00KLj2dTg00Kij3cTg00LLj4BTg00M7j6bTg00M[j4iTP3j6jTP0l9kTg00N<j7QTg00N`j6nTg00ODj7oTg00Ohj7]Tg00PLj8pTg00Q0R0f0R3'<p=5g00QNR2g00QnR17>3p=6p-0R6P5g00RNf5R7f4R8f3R9f2R:f1R;P3M9kp=Mg00S?R<P;g00S]P3CBp==P;g00TDR=g00TcR>P>g00UCR?P3g00UcR@FQp=;P;P=P>P>P?P3Enp=DP:P=P>P>P?P;P3Fop=:P:P=P>P>P?P<P;g00VCP3CBP@FQp=7P:P=P>P>P?P;P3F]p=RP9P=P>P>P?P:P;P3Gpp=4%5;R@g00VjRA#8RB#PRC%8B#8#8#8#8RD#PRE'TRF,0;RG'3RH129:RI/_F10IF1<FI'XP41289R4/0F1<F41278R4/CFRI/1711I85>2P3104FP<f6RI/27RJf7RK,13113I5>2XB<RL11JIRM11J7RN%6M10JI'912KIRM/1K#610MKROP311MI#6RPPP1O6PEMW:1?JI%6N10J7'9P6P5g00WO9f65RNPOPP10MIP3FJW:1?J71aCERP100CRO%5E100F[RQ[RR%5CRSg00XARTA`CE;UW<RE%5F\T^<SRSP;g00X]1^0C'IPOeO1ROPQg00YCRT#\RU%[TRVP<1Z<:P;%Y<RWCWRX%V<RY%U<RZ1@<0R[1E<BRB'=,;Z1DZ8R\5:ZR]%S>R^PZ1E<AR_,=[,;Z1DZ7R`5:ZRaP^AG<_BRb=7Z_A7ZbB5RZC4C41tZ?RcP3P:1I211s3:#6dAr<0;CqR1b6b8b9X3<X4<X16X2613@:13@812:9R@/0:10@9'9[[^3<^4<^16^26P3f:R2/0FRdf9Re/0FRfPeP2PKf8RgO6b5b0b7b0O2O23H1CJFRhPPPRPEPSPOPQg00YoRi#FRj#F,A<1A<j1A<i5N<5N<g00ZN'm=lTURTPVPXPYPZ1@<C%hD5g<RD97ZbRCP^PZP]P^PZPaP^1=[b,;Z=:ZCC4C4C4PcP1b6b8b9X3<X4<X16X26123;R;/0F%5:RC/3913C71298RC#510CF'3[[[^3<^4<^16^26P3PdPfPeP2P8PKPgO7b5b0b7b09LJFEKW;P3O11<F4P<%eARA/dFR4,2JRf/CFRdPLP<PfPL11fIRL11f7Ra%6L10fI'912M4RM/1K#610MKRLP311MI#6R]P]1O6]EMW:1?fI%6a10f7'9P6P5PNPLP]10MIP3FJW:1?f7PPPRPEPSPOPQPUPVPXPYPZA7ZBD9:Z\R\P^PZA7Z_D9:Z`R`P^1@<A=c<D9G<bRM=7Z_A7ZMB5RZC4C4PcP1b6b8b9X3<X4<X16X2613:G138G12@4R@/0:10@9'9[[^3<^4<^16^26P3%52R@%5eRGPeP2PKPgO6b5b0b7b0O2O23HPdPPPRPEPSPOPQPTPVPXPYPZ1=Db,;ZP^PZP\P^PZP`P^1=[M,;ZA7ZMD5:ZC4C4C4PcP1b6b8b9X3<X4<X16X261<F;10:FR:,39137:12C4R4#5104F'3[[[^3<^4<^16^26P3P@PGPeP2P8PKPgO7b5b0b7b09LfFEKPhPJPAPFPPPRPEPSPOPQPUPVPWPYPZP=P>P>P?P<PDg00[:P[CB,;ZEbPcP1b6b8b9A><F0g00[a[P3b5b0b7b0CiEjW;P3O1n200100000021100011000b?X>HW=XA<X@<o"). Qed.
Lemma carry_sym' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
  ((y + x) mod 18446744073709551616 <? x)%Z = ((x + y) mod 18446744073709551616 <? x)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xh11yh21zp;2p;1p;3p;6p-1R0p100\>p4p710p9P0p100\ap4p710p9P0p1001NR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p100]Mp4p710p9p1002fp4p710p1003Cp4p710p8g0078j2?Tg003_j10Tg004Dj12Tg004bj2>Tg005?j2:Tg005[j28Tg0066j23Tg007nj24Tg008Nj25Tg008kj39Tg00<fj2=Tg00^Ej2<Tg00JPj6;Tf0R0#0#0#0#0p=6%00#0p=7%00#0#0#0#0#0#0#0p=1g00S?R1g00Q0f1R2'?g00Vj#0R3#2%03#6R3#2'>,:2'8R2P1f3R4f2R5'3R6g00QNR7%73#1#1#1#1#1#1#1#2R3,40f4R0'51304/43/5039X211463/54,=713541<54E;V2UX11W0o"). Qed.

(* [comment removed for export] *)
Ltac zeq :=
  first
  [ reflexivity
  | lazymatch goal with
    (* [comment removed for export] *)
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq | rewrite (Z.lor_comm a b); f_equal; zeq ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq | rewrite (Z.land_comm a b); f_equal; zeq ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq | rewrite (Z.lxor_comm a b); f_equal; zeq ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq | rewrite (Z.add_comm a b); f_equal; zeq ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq | rewrite (Z.mul_comm a b); f_equal; zeq ]
    (* [comment removed for export] *)
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq); f_equal; zeq
    (* [comment removed for export] *)
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq | rewrite (Z.eqb_sym a b); f_equal; zeq
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith ]
    | |- negb _ = negb _ => f_equal; zeq
    | |- @eq bool _ _ => zeq_boolarith
    end
  | lia ]
(* [comment removed for export] *)
with unfold1 a := try (is_var a; cbv delta [a])
(* [comment removed for export] *)
with zeq_boolarith :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac zeq_fast :=
  first
  [ reflexivity
  | lazymatch goal with
    | |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
    | |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
    | |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
    | |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
    | |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
    | |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
    | |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
    | |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
    | |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
    | |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
    | |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
    | |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
        first [ f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
        first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
              | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- Z.leb ?a ?b = Z.leb ?c ?d =>
        first [ f_equal; zeq_fast | unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
    | |- negb _ = negb _ => f_equal; zeq_fast
    | |- @eq bool _ _ => zeq_boolarith_fast
    end
  | slim; lia ]
with zeq_boolarith_fast :=
  apply eq_true_iff_eq;
  rewrite ?Bool.negb_true_iff, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.leb_le, ?Z.ltb_ge, ?Z.eqb_neq, ?Z.leb_gt;
  slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac getreg n :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with
      | Some ?w => w
      | _ => fail "getreg: register" n "not concrete"
      end
  end.

(* [comment removed for export] *)
Ltac name_as_tac X e :=
  set (X := e);
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (subst X; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_as" ident(X) constr(e) := name_as_tac X e.

(* [comment removed for export] *)
Ltac name_reg_tac n X :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e => name_as_tac X e
  | _ => fail "name_reg: register" n "holds" w
  end.
Tactic Notation "name_reg" constr(n) ident(X) := name_reg_tac n X.

(* [comment removed for export] *)
Ltac model_reg_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      first [ constr_eq e mexpr
            | replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
                by (first [ f_equal; zeq_fast
                          | rewrite Z_to_bv_land64; f_equal; zeq_fast
                          | f_equal; zeq
                          | rewrite Z_to_bv_land64; f_equal; zeq
                          | apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq
                          | apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
                          | apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
      name_as_tac X mexpr
  | _ => fail "model_reg: register" n "holds" w
  end.
Tactic Notation "model_reg" constr(n) ident(X) constr(mexpr) := model_reg_tac n X mexpr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wrap64_lit : forall x, (x mod 2^64 = x mod 18446744073709551616)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Walk ()) [] "h01xp;1p;2p-1R0p100\>p4p710p9P0p100\ap4p710p9P0p1001NR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p100]Mp4p710p9p1002fp4p710p1003Cp4p710p8g004Dj14Tg007nj23Tg00<fj22Tg003_j10Tf0R0#0#0#0#0#0#0#0#0p=1g00S?R1g00Vj#1#1#1#1#1#1#1#1#4,30,21W0o"). Qed.

(* [comment removed for export] *)
Ltac name_virtual_tac X e :=
  set (X := e);
  let EX := fresh "E" X in assert (EX : X = e) by reflexivity;
  let RX := fresh "R" X in
  first [ assert (RX : (0 <= X < 18446744073709551616)%Z) by (rewrite EX; change (inr64 e); zrange)
        | idtac "note: no range fact for" X ].
Tactic Notation "name_virtual" ident(X) constr(e) := name_virtual_tac X e.

End Walk.
