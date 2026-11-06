(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export ExElim.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Tac () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3minI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib5Lists4List<length_skipnK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List<firstn_skipnC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Tac>mk_CB_cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3TacAmk_CB_cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Tac@mk_CB_cells_sizeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib3Tac>rw_cells_mergeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rK47Corelib4Init5Logic2ex01".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
(* [comment removed for export] *)
Ltac map_cbv_get ::= lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tget mkR] in G in change_no_check G' end.
Ltac map_cbv_set ::= lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tset mkR] in G in change_no_check G' end.

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

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    let kz := eval vm_compute in (Z.of_nat kn) in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB; lit_of_nat_in HB;
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);   (* [comment removed for export] *)
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + kz)) c') in HI;
              [ | exact I
                | change (wa (A + kz)) with (wa (A + Z.of_nat kn));
                  apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          change (wa (A + Z.of_nat kn)) with (wa (A + kz)) in H';
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + kz)%Z (cbytes c');
          footprint_after_store segs m (A + kz)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + kz)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Ltac norm_lit_store_bytes :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           is_Zlit z; change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
       end).

Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
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
(* [comment removed for export] *)
Ltac destruct_exs_loop PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs_loop PO
  | _ => idtac
  end.
Ltac destruct_exs PO :=
  diet_run ltac:(idtac; destruct_exs_loop PO) ltac:(idtac; ex_elim_hyp PO; destruct_exs_loop PO).

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
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h04__p1h14__x1h24__x2h34__x3h44__x4h52bsh61nh75sizesh81Hh92H0h:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB2z2hC2IHhD1mhE1shF1xhG1yp&0p;1p;2p;3p;4p;6p;5p;Bp;<p;7p;8p10000p4p710p1000Mp4p710p8g000ij1OTg001Ij1QTg001nj1iTg002Lj1`Tg002oj27Tg003Oj1:Tg004Cj2DTg005;j1ITg0062j1STg006Rj3KTg0072j3^Tg007Qj3\Tg007ok204Tg008FR0j10Tg008fR1j2JTg009Cj1Wj3?Tg009]j2wTg00:@j3qTg00:]j2ETg00;7j2gTg00;NR2j2MTg00;kj4cTg00<Rj1PTg00=7j25Tg00=Sj2aTg00>5j2BTg00>Qj26Tg00>lj2ATg00?Fj1_Tg00?dj2]Tg00@Ej1@Tg00@dj2>Tg00AMj3RTg00B6j2[Tg00BTk103Tg00C2j4ZTg00CPk102Tg00Cnk101Tg00DYj6~Tg00E=j2HTg00E`j1yTg00FEj1xTg00Fgj2vTg00GJj3VTg00Gmj2pTg00HOj2oTg00I;j3mTg00IZj4lTg00JLj4TTg00K7j3kTg00KYj6UTg00L7j2nTg00LNj2<Tg00Lkj2GTg00MHj2rTg00Mjj3sTg00NMj3tTg00Nnj4fTg00OIj5uTg00OklBLTg00PQl<dTg00Q6j3zTg00Q_j2{Tg00RKj4YTg00S6j7|Tg00SZj7}Tg00T>j7bTg00Tbk800Tg00UFR3f1R4f0R53?p=3g00UeR6??45p=1P3P3P3P6P6P6g00VCP0P0P0P1g00Vcf5R1f4R7f3R8f2R9P4P5MBLp=jP3P6P5P0P4P9P8P7P1f6R:f7f8R;M<dp=NP3P3P3P6P6P6g00WFP0P0P0P2g00WfP1P7P8P9P4P5MBLp=eAz645p=2g00XI,{5p=8g00Y5R2?K45p=9P6P4g00YaP5CYp==P4g00ZHR<g00ZgR=P=g00[GR>P5g00[gF|p=4P9P<P=P=P>P4P5F}p=FP6P4g00\GP5CYp=CP9P<P=P=P>P4P5Fbp=XP8P<P=P=P>P9P4P5L00p=;P3P3P3P6P6P6g00\nP0P0P0P:g00]NP1P7P8P9P4P5MBLp=h%O3R0P3g00^5R?#QR@#QRA#Q#i#`RB#ORC17B5RD%:4'31D94#I[]5REX70%S3RF#:,3Dg00^Z1DF4#IeW8X5CAK389#:,3DA^B74,7BRD/37A\B74RF,D8#IP317B4RG-047RH1351X6313H7%07RI%0GRJ'JRK/1I%W3RL%W6RM%04%05'113451w453qXG3XF3RNPHPKP7PI1E6IRKPGPJ1E6JRHEjP7PIPKM9N%:8RO,g7RP,3G%0ORQ,MIRR,1JRSPLPMPNPGPJPHPPPRP7PIPKPOPQ1E6QRREeM9NP5CcRPPS17B9RT#PRUg00_6RV%0T'5RT%P:RW%0:,5VRX%::RY#PRZ%0Y,5VRY%0;R[17B1#0R\'a1B[\1J[\R]/1['615\[11]\'6'Af9#0R]17B:#0R^'JP6p-0R_%_?,]6R`g00_TRa#@Rb#@Rc#@Rd,>6Re5R6Rf1>6cRc1>6bRb9R6`1>6aRa'2R`'2'2#8%@d,>6Rd12ea'2#812fa#8%S2Rg'9'9'9%O2R2P6P61[67P9&036CZP41[68CZRh&026Ri&016RjPjP<P=P=P>P:E~R<1H6?Rk1H6@R@'=,4jRl5Fj%y?,H6R?/C@,4j1=k?,4j5Fj5Xj%x=R=Pj1v6VRm1H6ARA'C,4jP=PjAV6@A,=?,4jP=PlC;C;C;1pj>R>P5P9g00`3Rng00`SRo'E1o59=?nodAm6V4ClRob<b=b>X16X26X36X46W01154,6715941159'6'A15V71M81,171187Rn[[[^16^26^36^46^0_P5f;#0Rp17B;#0R;'Bf:#:#0RqP;PpP4P9P8P:O8b;bBb:bAb@b?b9CTPDAkB74EUP9PFP31nG7RD%:7,35X6313DO1<JI,GVRr/1QPLPMPNPDPr1<45,GVXD6X66PGPJPHP7PIPKFhPOPQPRM9NPPPSPUPTPWPXPZPY1<\[R\,rV1BV\1GV\R[/1\'615\VA?6[V'6'A1<^],GVP612f`R`,2d#812ca,2e#812ba,2e#8%8`/9g'9'9'9P2PhPiPjAs6?ARi,=k,4j9Fj<1Cim,4j1=km,4j5Fj5XjP=Pj1Cm@,4jP=PjAV6A@,=?,4jP=PlC;C;C;P>Pob<b=b>X16X26X36X46X0_1<98Ro,15,6715oVA?65V'6'A15V91M18,17Pn[[[^16^26^36^46^0_P51<;p,BVPpP;PqP4P9P8P:O8b;bBb:bAb@b?b9CT17BFAtB74EUO2CfAK378/D4#IeW8X5CXCEX70XE3P5DuW7o"). Qed.

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "p'0h01Hh14__p1h24__x1h32bsh45sizesh52H0h67__arithh74__ffh88__varmaph95__with:4__x2h;4__x3h<4__x4h=4cstrh>1nh?1xh@2H2hA2IHhB1bi001bhC5cstr0hD5cstr1hE1li011lhF1mhG1shH1yhI2z2p&0p;1p;2p;3p;<p;4p;7p;6p;5p;8p;Bg000iR0j1NTg001Ij1MTg001nj1jTg002Lj1_Tg002oj22Tg003Oj19Tg004Cj2ATg00a3j1BTg009Cj31j1VTg0062j1JTg00:]j2;Tg006Rj34Tg00@ER1j1@Tg008FR2j10Tg00amj1wTg00;NR3j2<Tg009]j2kTg00:@j3iTg00PQl<\Tg00;kj4[Tg00<Rj1LTg00=7j27Tg00B6j2KTg00CPj1aTg00Cnj1`Tg00Fgj2QTg00E=j2HTg00FEj1^Tg00GJj3PTg00Gmk203Tg00HOk202Tg00I;k301Tg00IZk400Tg007Qj3~Tg0072j3}Tg00bKj3{Tg00bhj3zTg00L7j2yTg00LNj2:Tg00Lkj2GTg00;7j2uTg00MHj2oTg00>5j2XTg00>Qj2FTg00>lj2WTg00@dj2=Tg00?Fj1mTg00?dj2lTg00AMj3UTg00Q_j2CTg00BTj1nTg00C2j4TTg00E`j1hTg00Mjj3pTg00T>j7qTg00JLj4rTg00NMj3sTg00KYj6ZTg00OIj5fTg00cIl<xTg00RKj4RTg00S6j7eTg00DYj6dTg00Tbj8cTg00OklB]Tg00Q6j3|Tg00SZj7bTg00UFR4f1R5f0R631p=5g00_TR79146p=Eg00UeR8g00_6R9716p=DA1856p=8P4P4P8P8P1P2P2f3R1g00cnf2R:P5P6M<xp=gP8P5g00\GP6CRp=IP5g00ZHR;g00ZgR<P<g00[GR=P6g00[gFep=3P8P5g00YaP6CRp=?P5P;P<P<P=P6Edp=OP1P;P<P<P=P:P5P6Gcp=>P4P4P4P8P8P8g00\nP2P2P2f6R>g00]Nf5R?f4R@P1P:P5P6MB]p=vP4P8P6P2P5P:P1P@P?P>f7f8RAM<\p=YP4P4P4P8P8P8g00WFP2P2P2P3g00WfP?P@P1P:P5P6MB]p=tA|856p=6P:P;P<P<P=P5P6Fbp=S%N4R3P4g00^5RB#MRC#MRD#M#j#_RE#NRF12E6RG%95'51A:5#B=1F5[]3RHX43%J4RI#9,5GP0PE%EG%JER0=1F5]0P512E0#E1;F0W0A4E56,2E#E12E5RJ#@RK#E%0JRL%wBRM'<#DRNP4P8%V4ROP2%V8R2%05%06'815561k563iXH4X?4RPPK1<6MX?8RKPLO1PKPJPL1;8LRKCgP7P91;89M<\P6C[PN12E:RN#LRQ%0N,79RNp-0RRg00Y5RS#JRT%NSRU1K85%a8RV%`8RW1Q89RX1H8BRY'I,3W%^<RZPW1Q8M9P8Y/?X,3WPZ1OW1C>C>203W=R[P6P:g00`3R\g00`SR]';2026:=1\]dB01895H00R]b7b8b9X28W117961<5M#DP1[[^28^1RP6A4E?@91F012E@#0P5P:O4b6b=b5W0X3FXBEP5P6O2n10110100020021100101P6O11AI5#B=1F5eW0X3FA441:#9,5GPFA~E@5RGA}E?:={E6=1F:XEFAzE@51A1G#BP:PGP41yJ@RI%9@,56X>4%91R0,5I%0@RM,:L,G9R\%00R^'8POP2PPPIP\1:56,G9XF8X>8PJPLPKP@PM1;8MR\FvP0P^1;8^RIM9Y1u@0R_,5J1<M^R`,8LRaPOP2PPPJPLPKP_P`P@PMP\P0P^PIEtM9YP6C[PaPQPN%L>%0>,79%9>RN#L%0N,7912E?#0%0A':RN,o91X9N1G9NRQ/8N'F17N9%DQ'F'W12E>#0f9#0':,G9P8%@7RQ#@RN#@Ra#@,=8%mB,l8RI1=8aRa5U81=8QRQ9U8I1=87R7'6'6RI'6g00XIR^'C1=8N/67,6a/C^16Q7,6a/C^1CI^=4ST54S54S54SPUP8P81K8@P:%n8CTP51K81CTPVPWPWP;P<P<P=1OW>%hB,H8RB1H8DRD5p8R=,?Y,3W5SW1I=X,3W1?YX,3W5SWFqPZPW1H8CRC,IX,3WPZPWAP8DC,?B,3WPZ1?YC,3WC>C>C>P[P]b7b8b9X28X:8X;8X<8X1R1::1R],86,F@17]9%D6'F'W179:1<?1,8@181@[[[^28^:8^;8^<8^1RP612EA#0RAf;#0RR':,X9PRPAf:#9#0P5P:P1P>O8b6bIb@bDbCb=b5Cr12EGAsE@5EZO2EZA44@1/A5#B=1F5eW0X3FXAHX43XG4P6DfW4o"). Qed.

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h02bsh15sizesh27IHsizesh31ah41np;1p;2p;3p;6p;5g000ij17Tg001Ij15Tg001nj1<Tg002Lj18Tg004Cj21Tg00dRj13Tg003Oj10Tg009Cj32Tg00:]j26Tg0062j1;Tg00;7j24Tg007Qj39Tg00KYj6:Tg006Rj3>Tg00OIj5=Tg00UFR0#7R1P0g00^5#5#5#5#<#8R2#7R3f1R4f0R5'1#3%04520]0R6X11g00_T,60%;0R7/15#3%07520eX03P0f2R7#0R8f4R9/45f3R:#0,49520X4014:8,60A92:5R2,17#3P4P2O1E:A>0:7R:/15#3%0:520eX03X26X11X30P5D=W1o"). Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh31nh41lh52Hbh62Hwh73Hwfh84__x1h94__x2h:4__x3h;1Ah<2H0h=2H1h>2H2h?2H3h@2HshA3Hs0hB1LhC7__arithhD4__ffhE8__varmaphF5__withG4cstrhH5cstr0hI5cstr1hJ4junkhK1mhL4posthM3prehN4segshO5sizeshP1xhQ1yp;1p;4p;2p;3p;6p;<p;7p;8g000ij1BTg001Ij1=Tg001nj1]Tg002Lj1XTg00eKj1wTg00emj4ATg00fcj4PTg00dRj13Tg008FR0j11Tg00gZj46Tg003Oj1:Tg004Cj2;Tg005;j10Tg00a3j14Tg00hLj49Tg00>QR1j2ETg00iAj2jTg00j<j2DTg00k1j1^Tg002oj2HTg009Cj1Zj3QTg009]j2cTg00:@j3bTg00:]j2>Tg00;kj4YTg00<Rj1LTg00=7j2NTg00?Fj1aTg00?dj2`Tg00@Ej1WTg00@dj2JTg00AMj3VTg00Q6j3CTg00Q_j2UTg0062j1vTg006Rj3ITg00B6j2_Tg00C2j4uTg00CPj1tTg00Cnj1sTg00E=j2STg00E`j1qTg00FEj1pTg00Gmj2oTg00HOj2nTg00I;j3mTg00IZj4lTg00JLj4kTg00kgj3iTg00Nnj4FTg00bKj35Tg00lbj2KTg000Mj6[Tg00m`j3hTg00KYj68Tg00;7j2@Tg00n^j2OTg00o[j2gTg00PQl<fTg00RKj4eTg00S6j7dTg00Tbj8rTg010XR2f3R3f2R4f1R5'Df0R65I235p=7g00UFR7?Q56p=<A5256p=21D45=I26p=Gg00UeR8?Q56p=?P7P8P6P0P5P4P3f4R0f5R9f6R:f7R;f8R<M<fp=MP8P5g00YaP6Cep=TP5g00ZHR=g00ZgR>P>g00[GR?P6g00[gFdp=RP3P=P>P>P?P4P5P6Grp=\g011M#Bg00^5R=#=R@#=#=RA#=#=#=#]#X%]A#XRA#w[%B2R2%BARB%B7P;P:P9P0P3P4P5C7CAP1P<P;P:P9P0P3P4C7RCCPP<P;P:%3C#1C6%:4/<9f:RCf9RDP<1;39/20,2;CA[P6PCPDP<P;P:P9P0C7CPP1P<P;P:P9C7RE#0f;RFPCPD%4EC9f<REPFPCPDP<P;P:C7#3#1C6%::/<Df>R:f=RGPE1;;D/2<,2FCA[[P6PCPDP<P;C7#0P:PGPEPFPCPDP<C7#4C9f?R<P:PGPEPFPCPDC7#3#1C6%:D/<EP11256#0%04RD%05RF'ERH[RI%06,EF1245#0RF[RJ%03/ED\F1j56RFP5n2001000000120000000X22X12PI^22^12P6P<AG:GERDP0O3%0<%0D'EP1f@RD#0AG<:G#0fDRKfCRLfBRMfARN1;G</2:'2CAP6%0MAGMND#0P11DLM#^%0NfHRDfGR:fFR<fERO1;NL/2M'2CAP61DOK#^%0K1HA<RM%:KRK'<RN%1MRL%1KRP'?%Z7RQ%Z8RR%15%16RS'?1<561c563bXQ7XP7RTPMPL1>8LPKPP1>8PRLM9M1<K:%1:RM,?PRUPQPRPTPKPPPLP:PM1>8MM9MPCCYPU1HA:RU/<D%1URC%1DRM'?RLPQPRPTPUPC1>8CPDPM1>8MM9MP4CYPLfIRL#Lg00_6RM%1L'N1HALRC#L%1C,NM%:DRC#L%1C,NMg00Y5RC%a=,`8RUg00_TRT#WRR#W,J8RQ5V81J8RRR1J8TRT5C85C8g00XIRP'UAV8UR=C8T9C8Q/UP%vC5IC3I%BCP81_84P51_83Cu%t8%s8RC1S8=RP%q=,S8R='T,RC%p>R>PC1S8@R@/T=,RCP>1TP@,RCC\C\1oC?P6P4g00`3RCg00`SR?'>1n64=QC?dAm8M5ClbDbEbFX88X98X:81?641?43RMPM[[^88^98^:8P6fMRM#1fJR?#:#1fLRC,HA#1P0P9O5bCbIbHbGb<bACkPNPCfKRNP?1;O:/2<RO,2LR9CPPCPNP?%39R0#1C6%09PCPNP?%49R9C9P1PIPJ1234#0\HPFP6n2001000000120000000X22X12RFPJ^22^12RJP6P?1;<DRH/2:RI%0?%0IP;PFPJP61;:LRJPD%0J%0DAi:L4P3CFO3b0CFO3b0PB%4LR3%4O55APMPCPNP6C9X4BR4PBAGD:<RJ,2LRF#4P4PG%4J95A3R31KLJE[PCPNP?P3C9PB%4HR3%4:55AfNRGPMPC%4NR4=5A6C9X4BPBPDPGPMPC%4D95A695A4C9X4BP6P3Ah<D5E8%4I1KH:E8b5P91KLOE8CFP7%3LR9%3O'@PMPCPNPSC6X37RSP7%3FPSPE%3J,@9R91OLJE[PCPNP?%19C6P7%3HR9%3:'@PGPMPC%3NRN/@6#1C6X37P7%:<R?PGPMPC%3D,@6,@N#1C6X37RNP7PLPNP6P?PEE8P91g<DE8%3I1OH:E8b6P01OLOE8CFbBW?W>P5P6O2n2001000000121000000W0W=P5P6O2n2001000000121000000b7b0W@W6W5W7P5P6O2n2001000000121000000W0P5P6O2n2001000000121000000W0WOXL2WJX37WMX;8WKWNo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post).
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Hh11ah21bh32Hbh42Hwh53H23h63Hwfh71lh81nh91Ah:2H1h;2H2h<2H3h=1mh>3midh?4posth@3prehA4segsp;1p;4p;2p;3p;6g000ij1BTg001Ij1:Tg001nj1DTg002Lj1CTg00eKj1MTg00emj4;Tg00fcj4?Tg00dRj12Tg00a3j13Tg00j<j26Tg005;j11Tg00hLj45Tg00>QR0j2<Tg00iAj2LTg002oj2KTg009Cj3JTg012Lj2HTg00Nnj4=Tg00bKj37Tg00lbj2@Tg000Mj6>Tg00KYj6ETg00;7j29Tg00n^j2ATg008Fj1GTg00gZj4FTg006Rj3ITg010XR1f1R2f0R337p=0f3R4f2R5P2%G3CFp=4AI123p=8g011M#Bg00^5#:#:#:R6#:#:#:#D#C%D6#CR6#M[g00Ue%B1R1f5R7f4R8P41023R9,05C;P0f6R:P7P81052R;,04R<C?P:P7P8%2<C4f7R<P:P7%24%34'6/85,08C;P3f8R=P<P:1084,07C?P01078,0:R8#1f9R>P=P<%38C5f:R8P>P=10:7,0<#2C4f;R7P8P>%2<%3<'6/8:,0=C;[P310<:,0=#1f<R:P7P810=<,0>#3C5f=R<P:P710>=,08#2C4P0%19%15R9%12R>'<R?[R@%13,<>%1;R;[R>%14/<9\;1L23R;P2n2001000000120000000X21X11R9P@^21^11RAP3P:1078R8P4O3%1:%18'<P0%1<10:7#1fAR7f@R8f?RBf>RC%2<%3<'6/8:'0C;P3%1B10BC#1P9PAP3P7P8P2O3%17R7%18'<P0fBR8#1P7fGR7fFRAfER9fDRCfCRB#2%3B'6/88'0C;P3%1CRCfJR8fIRBfHRD%2ARE%3ARF'6/89RG,07RHC?P8PBPD%2HRIC4%1HP8PBPD%3HRHC5P0P@P>1045#1\?P;P3n2001000000120000000X21X11P>^21^11P3PD%27R>%37R;'6/8AR?%1D%1?R?P=g00UFR=1K6;;J>%1A1H75P2C=P?eC=O3b0%B6R?%3G976;fKR5P8PBP3C5X7?R4P?10A9R9,07R@#3P4P<%39976;R<1@79E>P8PBPDP<C5P?107AR<#3fLR4P5P8%3BR0=763C5X7?P3A76;FR;1@7AE>P5P8PB%3DRF=76;C5P3P4P5P8%2DR;/6F/87RF#39760C5eb3b3PH1@7GEEC=P=%2G,9>P5P8PBP3C4X8=RHP=%2@PHP:%29,9>R:1A79E>P8PBPDP:C4P=%2<P4P5P8%2BR</93C4X8=P319>ER>1A7AE>P5P8PB19;>C4P3P4P5P8%2F,9<C4eb4b4PI1A7GEEC=X<CW;P2P3O2n2001000000121000000b5b0W5W:P2P3O2n2001000000121000000b6b0W4W3W6P2P3O2n2001000000121000000W0P2P3O2n2001000000121000000W0X?1X>1W@W9W=WAo"). Qed.

Lemma rw_cells_forget : forall segs m A cs,
  rw_cells segs m A cs -> exists junk, rw_cells segs m A [CB (cells_size cs) junk].
Proof.
ltac2:(KReplay.run1 (kr_t_Tac ()) [] "h01Mh11Ah21Hh32csh44junkh51lh61mh74segsp;1p;4p;2p;3p;6g000ij17Tg001Ij12Tg001nj19Tg002Lj18Tg00eKj1@Tg00emj40Tg00dRj16Tg00j<j24Tg0062j1;Tg006Rj33Tg00a3j15Tg013Mj6:Tg014Hj2?Tg000Mj6>Tg014fj4=Tg00bKj3<Tg010XR0f1R1f0R23<p=1g011M#7g00^5#2#2#2R3#2#2#2#9#8%93#8R3#@[g00Ue%70R4f3R5f2R6P1P2C0%73R3f5R7f4R8P5%66R9/42%;0R:530C0X43%51P8P5P6P:P1P:E:P8P5P6111:,1:C0P7P8P5%56,49=30:,1:C0[P4116:f6R9P7P811:2C0f7P9P7%68%58'4=30:,1:C0[X54P2P61?06E>P7P8P511:6C0P9P7P8%65%55'4=30:,1:C0[P2P6O1b0b0C=W2W3W1W6W7o"). Qed.

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
