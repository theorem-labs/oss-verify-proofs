(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Tac () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac7sum_natC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac;mk_CB_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3minI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List<length_skipnK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~K47Corelib7Numbers7BinNums1Z02C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells<cells_wf_appC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells7cell_wfC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac>mk_CB_cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells?cells_bytes_appC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3TacAmk_CB_cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells>cells_size_appC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac@mk_CB_cells_sizeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Tac>rw_cells_mergeC13~~~C46Stdlib5Lists4List9app_nil_rK47Corelib4Init5Logic2ex01".
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
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h04__p1h14__x1h24__x2h34__x3h44__x4h52bsh61nh75sizesh81Hh92H0h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB2z2hC2IHhD1mhE1shF1xhG1yp&0p;1p;2p;3p;4p;6p;5p;Bp;<p;7p;8p10000p4p710p1000Mp4p710p8g000ij1OTg001Ij1QTg001nj1iTg002Lj1`Tg002oj27Tg003Oj1:Tg004\j2DTg005mj1ITg007=j1STg007]j3KTg008=j3^Tg008\j3\Tg009:k204Tg009QR0j10Tg00:1R1j2JTg00:Nj1Wj3?Tg00:hj2wTg00;Kj3qTg00;hj2ETg00<Bj2gTg00<YR2j2MTg00=6j4cTg00=]j1PTg00>Bj25Tg00>^j2aTg00?@j2BTg00?\j26Tg00@7j2ATg00@Qj1_Tg00@oj2]Tg00APj1@Tg00Aoj2>Tg00BXj3RTg00CAj2[Tg00C_k103Tg00D=j4ZTg00D[k102Tg00E9k101Tg00Edj6~Tg00FHj2HTg00Fkj1yTg00GPj1xTg00H2j2vTg00HUj3VTg00I8j2pTg00IZj2oTg00JFj3mTg00Jej4lTg00KWj4TTg00LBj3kTg00Ldj6UTg00MBj2nTg00MYj2<Tg00N6j2GTg00NSj2rTg00O5j3sTg00OXj3tTg00P9j4fTg00PTj5uTg00Q6lBLTg00Q\l<dTg00RAj3zTg00Rjj2{Tg00SVj4YTg00TAj7|Tg00Tej7}Tg00UIj7bTg00Umk800Tg00VQR3f1R4f0R53?p=3g00W0R6??45p=1P3P3P3P6P6P6g00WNP0P0P0P1g00Wnf5R1f4R7f3R8f2R9P4P5MBLp=jP3P6P5P0P4P9P8P7P1f6R:f7R;f8R<M<dp=NP3P3P3P6P6P6g00XQP0P0P0P2g00Y1P1P7P8P9P4P5MBLp=eAz645p=2g00YT,{5p=8g00Z@R2?K45p=9P6P4g00ZlP5CYp==P4g00[SR=g00\2R>P>g00\RR?P5g00]2F|p=4P9P=P>P>P?P4P5F}p=FP6P4g00]RP5CYp=CP9P=P>P>P?P4P5Fbp=XP8P=P>P>P?P9P4P5L00p=;P3P3P3P6P6P6g00^9P0P0P0P:g00^YP1P7P8P9P4P5MBLp=h%O3R0P3g00_@R@#QRA#QRB#Q#i#`RC#ORD17C5RE%:4'31D94#I[]5RFX70%S3RG#:,3Eg00_e1DG4#IeW8X5DAK389#:,3EA^C74,7CRE/37A\C74RG,D8#IP317C4RH-047RI1351X6313I7%07RJ%0HRK'JRL/1J%W3RM%W6RN%04%05'113451w453qXG3XF3ROPIPLP7PJ1E6JRLPHPK1E6KRIEjP7PJPLM9N%:8RP,g7RQ,3H%0PRR,MJRS,1KRTPMPNPOPHPKPIPQPSP7PJPLPPPR1E6RRSEeM9NP5CcRQPT17C9RU#PRVg00`ARW%0U'5RU%:1RX#PRY%0X,5WRX%P;RZ%0;,5WR;%0<R[17C1#0R\'a1B[\1J[\R]/1['615\[11]\'6'Af9#0R]17C:#0R^'JP6p-0R_%_@,]6R`g00`_Ra#@Rb#@Rc#@Rd,>6Re5R6Rf1>6cRc1>6bRb9R6`1>6aRa'2R`'2'2#8%@d,>6Rd12ea'2#812fa#8%S2Rg'9'9'9%O2R2P6P61[67P9&036CZP41[68CZRh&026Ri&016RjPjP=P>P>P?P:E~R=1H6@Rk1H6ARA'=,4jRl5Fj%y@,H6R@/CA,4j1=k@,4j5Fj5Xj%x>R>Pj1v6WRm1H6BRB'C,4jP>PjAV6AB,=@,4jP>PlC;C;C;1pj?R?P5P9g00a>Rng00a^Ro'E1o59=?nodAm6W4ClRob<b=b>X16X26X36X46W01154,6715941159'6'A15W71M81,171187Rn[[[^16^26^36^46^0_P5f;#0Rp17C<#0R<'Bf:#:#0RqP<PpP4P9P7P:O8b;bBb:bAb@b?b9CTPEAkC74EUP9PGP31nH7RE%:7,35X6313EP1<KJ,GWRr/1RPMPNPOPEPr1<45,GWXD6X66PHPKPIP7PJPLFhPPPRPSM9NPQPTPVPUPYPXPZP;1<\[R\,rW1BW\1GW\R[/1\'615\WA?6[W'6'A1<^],GWP612f`R`,2d#812ca,2e#812ba,2e#8%8`/9g'9'9'9P2PhPiPjAs6@BRi,=k,4j9Fj=1Cim,4j1=km,4j5Fj5XjP>Pj1CmA,4jP>PjAV6BA,=@,4jP>PlC;C;C;P?Pob<b=b>X16X26X36X46X0_1<98Ro,15,6715oWA?65W'6'A15W91M18,17Pn[[[^16^26^36^46^0_P51<<p,BWPpP<PqP4P9P7P:O8b;bBb:bAb@b?b9CT17CGAtC74EUO2CfAK378/D4#IeW8X5DXCFX70XE3P5DuW7o"). Qed.

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "p'0h01Hh14__p1h24__x1h32bsh45sizesh52H0h67__arithh74__ffh88__varmaph95__with:4__x2h;4__x3h<4__x4h=4cstrh>1nh?1xh@2H2hA2IHhB1bi001bhC5cstr0hD5cstr1hE1li011lhF1mhG1shH1yhI2z2p&0p;1p;2p;3p;<p;4p;7p;6p;5p;8p;Bg000iR0j1NTg001Ij1MTg001nj1jTg002Lj1_Tg002oj22Tg003Oj19Tg004\j2ATg00b>j1BTg00:Nj31j1VTg007=j1JTg00;hj2;Tg007]j34Tg00APR1j1@Tg009QR2j10Tg00cQj1wTg00<YR3j2<Tg00:hj2kTg00;Kj3iTg00Q\l<\Tg00=6j4[Tg00=]j1LTg00>Bj27Tg00CAj2KTg00D[j1aTg00E9j1`Tg00H2j2QTg00FHj2HTg00GPj1^Tg00HUj3PTg00I8k203Tg00IZk202Tg00JFk301Tg00Jek400Tg008\j3~Tg008=j3}Tg00coj3{Tg00dLj3zTg00MBj2yTg00MYj2:Tg00N6j2GTg00<Bj2uTg00NSj2oTg00?@j2XTg00?\j2FTg00@7j2WTg00Aoj2=Tg00@Qj1mTg00@oj2lTg00BXj3UTg00Rjj2CTg00C_j1nTg00D=j4TTg00Fkj1hTg00O5j3pTg00UIj7qTg00KWj4rTg00OXj3sTg00Ldj6ZTg00PTj5fTg00dml<xTg00SVj4RTg00TAj7eTg00Edj6dTg00Umj8cTg00Q6lB]Tg00RAj3|Tg00Tej7bTg00VQR4f1R5f0R631p=5g00`_R79146p=Eg00W0R8g00`AR9716p=DA1856p=8P4P4P8P8P1P2P2f3R1g00eRf2R:P5P6M<xp=gP8P5g00]RP6CRp=IP5g00[SR;g00\2R<P<g00\RR=P6g00]2Fep=3P8P5g00ZlP6CRp=?P5P;P<P<P=P6Edp=OP1P;P<P<P=P:P5P6Gcp=>P4P4P4P8P8P8g00^9P2P2P2f6R>g00^Yf5R?f4R@P1P:P5P6MB]p=vP4P8P6P2P5P:P1P@P?P>f7RAf8RBM<\p=YP4P4P4P8P8P8g00XQP2P2P2P3g00Y1P?P@P1P:P5P6MB]p=tA|856p=6P:P;P<P<P=P5P6Fbp=S%N4R3P4g00_@RC#MRD#MRE#M#j#_RF#NRG12F6RH%95'51A:5#B=1G5[]3RIX43%J4RJ#9,5HP0PF%EH%JFR0=1G5]0P512F0#E1;G0W0A4F56,2F#E12F5RK#@RL#E%0KRM%wCRN'<#DROP4P8%V4RPP2%V8R2%05%06'815561k563iXH4X?4RQPL1<6NX?8RLPMO1PLPKPM1;8MRLCgP7P91;89M<\P6C[PO12F:RO#LRR%0O,79ROp-0RSg00Z@RT#JRU%NTRV1K85%a8RW%`8RX1Q89RY1H8CRZ'I,3X%^<R[PX1Q8N9P8Z/?Y,3XP[1OX1C>C>203X=R\P6P:g00a>R]g00a^R^';2026:=1]^dB01895H00R^b7b8b9X28W117961<5N#DP1[[^28^1SP6A4F?@91G012F@#0P5P:O4b6b=b5W0X3GXBFP5P6O2n10110100020021100101P6O11AJ5#B=1G5eW0X3GA441:#9,5HPGA~F@5RHA}F?:={F6=1G:XEGAzF@51A1H#BP:PHP41yK@RJ%9@,56X>4%91R0,5J%0@RN,:M,G9R]%00R_'8PPP2PQPJP]1:56,G9XF8X>8PKPMPLP@PN1;8NR]FvP0P_1;8_RJM9Y1u@0R`,5K1<N_Ra,8MRbPPP2PQPKPMPLP`PaP@PNP]P0P_PJEtM9YP6C[PbPRPO%9?RO#L%0O,79%LA%0A,7912F?#0%0B':RA,o91X9A1G9ARO/8A'F17A9%DO'F'W12F>#0f9#0':,G9P8%@7RO#@RA#@RR#@,=8%mC,l8Rb1=8RRR5U81=8ORO9U8b1=87R7'6'6Rb'6g00YTRJ'C1=8A/67,6R/CJ16O7,6R/CJ1CbJ=4TU54T54T54TPVP8P81K8@P:%n8CTP51K81CTPWPXPXP;P<P<P=1OX>%hC,H8RC1H8ERE5p8R=,?Z,3X5SX1I=Y,3X1?ZY,3X5SXFqP[PX1H8DRD,IY,3XP[PXAP8ED,?C,3XP[1?ZD,3XC>C>C>P\P^b7b8b9X28X:8X;8X<8X1S1::1R^,86,F@17^9%D6'F'W179:1<?1,8@181@[[[^28^:8^;8^<8^1SP612FB#0RBf;#0RS':,X9PSPBf:#9#0P5P:P@P>O8b6bIb@bDbCb=b5Cr12FHAsF@5EZO2EZA44@1/A5#B=1G5eW0X3GXAIX43XG4P6DfW4o"). Qed.

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h02bsh15sizesh27IHsizesh31ah41np;1p;2p;3p;6p;5g000ij17Tg001Ij15Tg001nj1<Tg002Lj18Tg004\j21Tg00f6j13Tg003Oj10Tg00:Nj32Tg00;hj26Tg007=j1;Tg00<Bj24Tg008\j39Tg00Ldj6:Tg007]j3>Tg00PTj5=Tg00VQR0#7R1P0g00_@#5#5#5#<#8R2#7R3f1R4f0R5'1#3%04520]0R6X11g00`_,60%;0R7/15#3%07520eX03P0f2R7#0R8f4R9/45f3R:#0,49520X4014:8,60A92:5R2,17#3P4P2O1E:A>0:7R:/15#3%0:520eX03X26X11X30P5D=W1o"). Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh31nh41lh52Hbh62Hwh73Hwfh84__x1h94__x2h:4__x3h;1Ah<2H0h=2H1h>2H2h?2H3h@2HshA3Hs0hB1LhC7__arithhD4__ffhE8__varmaphF5__withG4cstrhH5cstr0hI5cstr1hJ4junkhK1mhL4posthM3prehN4segshO5sizeshP1xhQ1yp;1p;4p;2p;3p;6p;<p;7p;8g000ij1BTg001Ij1=Tg001nj1]Tg002Lj1XTg00gHj1wTg00gjj4ATg00i9j4PTg00f6j13Tg009QR0j11Tg00jIj46Tg003Oj1:Tg004\j2;Tg005mj10Tg00b>j14Tg00kTj49Tg00?\R1j2ETg00lbj2jTg00n6j2DTg00oDj1^Tg002oj2HTg00:Nj1Zj3QTg00:hj2cTg00;Kj3bTg00;hj2>Tg00=6j4YTg00=]j1LTg00>Bj2NTg00@Qj1aTg00@oj2`Tg00APj1WTg00Aoj2JTg00BXj3VTg00RAj3CTg00Rjj2UTg007=j1vTg007]j3ITg00CAj2_Tg00D=j4uTg00D[j1tTg00E9j1sTg00FHj2STg00Fkj1qTg00GPj1pTg00I8j2oTg00IZj2nTg00JFj3mTg00Jej4lTg00KWj4kTg010Sj3iTg00P9j4FTg00coj35Tg011gj2KTg000Mj6[Tg013>j3hTg00Ldj68Tg00<Bj2@Tg014Uj2OTg015kj2gTg00Q\l<fTg00SVj4eTg00TAj7dTg00Umj8rTg017AR2f3R3f2R4f1R5'Df0R65I235p=7g00VQR7?Q56p=<A5256p=21D45=I26p=Gg00W0R8?Q56p=?P7P8P6P0P5P4P3f4R0f5R9f6R:f7R;f8R<M<fp=MP8P5g00ZlP6Cep=TP5g00[SR=g00\2R>P>g00\RR?P6g00]2Fdp=RP3P=P>P>P?P4P5P6Grp=\g018O#Bg00_@R=#=R@#=#=RA#=#=#=#]#X%]A#XRA#w[%B2R2%BARB%B7P;P:P9P0P3P4P5C7CAP1P<P;P:P9P0P3P4C7RCCPP<P;P:%3C#1C6%:4/<9f:RCf9RDP<1;39/20,2;CA[P6PCPDP<P;P:P9P0C7CPP1P<P;P:P9C7RE#0f;RFPCPD%4EC9f<REPFPCPDP<P;P:C7#3#1C6%::/<Df>R:f=RGPE1;;D/2<,2FCA[[P6PCPDP<P;C7#0P:PGPEPFPCPDP<C7#4C9f?R<P:PGPEPFPCPDC7#3#1C6%:D/<EP11256#0%04RD%05RF'ERH[RI%06,EF1245#0RF[RJ%03/ED\F1j56RFP5n2001000000120000000X22X12PI^22^12P6P<AG:GERDP0O3%0<%0D'EP1f@RD#0AG<:G#0fDRKfCRLfBRMfARN1;G</2:'2CAP6%0MAGMND#0P11DLM#^%0NfHRDfGR:fFR<fERO1;NL/2M'2CAP61DOK#^%0K1HA<RM%:KRK'<RN%1MRL%1KRP'?%Z7RQ%Z8RR%15%16RS'?1<561c563bXQ7XP7RTPMPL1>8LPKPP1>8PRLM9M1<K:%1:RM,?PRUPQPRPTPKPPPLP:PM1>8MM9MPCCYPU1HA:RU/<D%1URC%1DRM'?RLPQPRPTPUPC1>8CPDPM1>8MM9MP4CYPLfIRL#Lg00`ARM%1L'N%::RC#L%1C,NMfJRC,HARU#L%1U,NMg00Z@RU%a=,`8RTg00`_RR#WRQ#W,J8RP5V81J8QRQ1J8RRR5C85C8g00YTRK'UAV8TQ=C8R9C8P/UK%vU5IU3I%BUP81_84P51_83Cu%t8%s8RU1S8=RK%q=,S8R='T,RU%p>R>PU1S8@R@/T=,RUP>1TK@,RUC\C\1oU?P6P4g00a>RUg00a^R?'>1n64=QU?dAm8M5ClbDbEbFX88X98X:81?641?43RMPM[[^88^98^:8P6fMRM#1%:C#1fLR?,HA#1P0P9O5bCbIbHbGb<bACkPNP?fKRNPC1;O:/2<RO,2LR9CPP?PNPC%39R0#1C6%09P?PNPC%49R9C9P1PIPJ1234#0\HPFP6n2001000000120000000X22X12RFPJ^22^12RJP6PC1;<DRH/2:RI%0C%0IP;PFPJP61;:LRJPD%0J%0DAi:L4P3CFO3b0CFO3b0PB%4LR3%4O55APMP?PNP6C9X4BR4PBAGD:<RJ,2LRF#4P4PG%4J95A3R31KLJE[P?PNPCP3C9PB%4HR3%4:55AfNRGPMP?%4NR4=5A6C9X4BPBPDPGPMP?%4D95A695A4C9X4BP6P3Ah<D5E8%4I1KH:E8b5P91KLOE8CFP7%3LR9%3O'@PMP?PNPSC6X37RSP7%3FPSPE%3J,@9R91OLJE[P?PNPC%19C6P7%3HR9%3:'@PGPMP?%3NRN/@6#1C6X37P7%:<RCPGPMP?%3D,@6,@N#1C6X37RNP7PLPNP6PCPEE8P91g<DE8%3I1OH:E8b6P01OLOE8CFbBW?W>P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000b7b0W@W6W5W7P5P6O2n2001000000121000000W0P5P6O2n2001000000121000000W0WOXL2WJX37WMX;8WKWNo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh32Hbh42Hwh53H23h63Hwfh71lh81nh91Ah:2H1h;2H2h<2H3h=1mh>3midh?4posth@3prehA4segsp;1p;4p;2p;3p;6g000ij1BTg001Ij1:Tg001nj1DTg002Lj1CTg00gHj1MTg00gjj4;Tg00i9j4?Tg00f6j12Tg00b>j13Tg00n6j26Tg005mj11Tg00kTj45Tg00?\R0j2<Tg00lbj2LTg002oj2KTg00:Nj3JTg019Nj2HTg00P9j4=Tg00coj37Tg011gj2@Tg000Mj6>Tg00Ldj6ETg00<Bj29Tg014Uj2ATg009Qj1GTg00jIj4FTg007]j3ITg017AR1f1R2f0R337p=0f3R4f2R5P2%G3CFp=4AI123p=8g018O#Bg00_@#:#:#:R6#:#:#:#D#C%D6#CR6#M[g00W0%B1R1f5R7f4R8P41023R9,05C;P0f6R:P7P81052R;,04R<C?P:P7P8%2<C4f7R<P:P7%24%34'6/85,08C;P3f8R=P<P:1084,07C?P01078,0:R8#1f9R>P=P<%38C5f:R8P>P=10:7,0<#2C4f;R7P8P>%2<%3<'6/8:,0=C;[P310<:,0=#1f<R:P7P810=<,0>#3C5f=R<P:P710>=,08#2C4P0%19%15R9%12R>'<R?[R@%13,<>%1;R;[R>%14/<9\;1L23R;P2n2001000000120000000X21X11R9P@^21^11RAP3P:1078R8P4O3%1:%18'<P0%1<10:7#1fAR7f@R8f?RBf>RC%2<%3<'6/8:'0C;P3%1B10BC#1P9PAP3P7P8P2O3%17R7%18'<P0fBR8#1P7fGR7fFRAfER9fDRCfCRB#2%3B'6/88'0C;P3%1CRCfJR8fIRBfHRD%2ARE%3ARF'6/89RG,07RHC?P8PBPD%2HRIC4%1HP8PBPD%3HRHC5P0P@P>1045#1\?P;P3n2001000000120000000X21X11P>^21^11P3PD%27R>%37R;'6/8AR?%1D%1?R?P=g00VQR=1K6;;J>%1A1H75P2C=P?eC=O3b0%B6R?%3G976;fKR5P8PBP3C5X7?R4P?10A9R9,07R@#3P4P<%39976;R<1@79E>P8PBPDP<C5P?107AR<#3fLR4P5P8%3BR0=763C5X7?P3A76;FR;1@7AE>P5P8PB%3DRF=76;C5P3P4P5P8%2DR;/6F/87RF#39760C5eb3b3PH1@7GEEC=P=%2G,9>P5P8PBP3C4X8=RHP=%2@PHP:%29,9>R:1A79E>P8PBPDP:C4P=%2<P4P5P8%2BR</93C4X8=P319>ER>1A7AE>P5P8PB19;>C4P3P4P5P8%2F,9<C4eb4b4PI1A7GEEC=X<CW;P2P3O2n2001000000121000000b5b0W5W:P2P3O2n2001000000121000000b6b0W4W3W6P2P3O2n2001000000121000000W0P2P3O2n2001000000121000000W0X?1X>1W@W9W=WAo"). Qed.

Lemma rw_cells_forget : forall segs m A cs,
  rw_cells segs m A cs -> exists junk, rw_cells segs m A [CB (cells_size cs) junk].
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Mh11Ah21Hh32csh44junkh51lh61mh74segsp;1p;4p;2p;3p;6g000ij17Tg001Ij12Tg001nj19Tg002Lj18Tg00gHj1@Tg00gjj40Tg00f6j16Tg00n6j24Tg007=j1;Tg007]j33Tg00b>j15Tg01:hj6:Tg01<<j2?Tg000Mj6>Tg01<Zj4=Tg00coj3<Tg017AR0f1R1f0R23<p=1g018O#7g00_@#2#2#2R3#2#2#2#9#8%93#8R3#@[g00W0%70R4f3R5f2R6P1P2C0%73R3f5R7f4R8P5%66R9/42%;0R:530C0X43%51P8P5P6P:P1P:E:P8P5P6111:,1:C0P7P8P5%56,49=30:,1:C0[P4116:f6R9P7P811:2C0f7P9P7%68%58'4=30:,1:C0[X54P2P61?06E>P7P8P511:6C0P9P7P8%65%55'4=30:,1:C0[P2P6O1b0b0C=W2W3W1W6W7o"). Qed.

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
