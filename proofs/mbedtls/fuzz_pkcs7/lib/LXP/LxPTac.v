(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxDex.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_arith T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | le _ _ => idtac | lt _ _ => idtac
  | @eq Z _ _ => idtac | @eq (bv _) _ _ => idtac | @eq bool _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac
  | @eq (list _) _ _ => idtac        (* [comment removed for export] *)
  | ?A /\ ?B => lxp_arith A; lxp_arith B
  | ?A \/ ?B => lxp_arith A; lxp_arith B
  | ~ ?A => lxp_arith A
  | ?A -> ?B => lxp_arith A; lxp_arith B
  | True => idtac | False => idtac
  end.

(* [comment removed for export] *)
Ltac lxp_arith_ctx :=
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with
    | Prop => tryif lxp_arith T then fail else clear H
    | _ => fail
    end end.

(* [comment removed for export] *)
Ltac lxp_bool_hyps :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

(* [comment removed for export] *)
Ltac lxp_goal_selects :=
  repeat match goal with |- context [Z.b2z ?c] =>
    lazymatch c with true => fail | false => fail | _ => destruct c end end;
  try change (Z.b2z true) with 1; try change (Z.b2z false) with 0;
  repeat match goal with |- context [Z.add ?a ?b] =>
    is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v end;
  rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.land_m1_l, ?Z.land_m1_r, ?Z.lor_0_l, ?Z.lor_0_r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_noevar_goal := lazymatch goal with |- ?G => tryif has_evar G then fail else idtac end.
Ltac lxp_lia := lxp_noevar_goal; lxp_arith_ctx; lxp_bool_hyps; prune_disj; lxp_goal_selects;
  rewrite ?lx_bvu64;
  first [ lia | unfold zlow, zswrap; lia | (progress (unfold zlow, zswrap in * ); lia) ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_c4 :=
  repeat match goal with H : rw_cells _ _ _ ?cs |- _ =>
    match cs with context [C4 ?w] =>
      lazymatch w with Z_to_bv _ _ => fail | _ => rewrite <- (Z_to_bv_bv_unsigned w) in H end end end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxPTac () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.csize"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cbytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_opq"; "RocqVerifyHarness.AgentSubmission.LX.LxTac.lx_no_layout"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zswrap"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.ltb"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"].


(* [comment removed for export] *)
Lemma lxp_rw_cells_retype : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' H <-. exact H. Qed.
(* [comment removed for export] *)
Ltac lxp_weqz := first [ reflexivity | apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned
                       | apply (f_equal (Z_to_bv _)); solve [ lxp_lia ] ].
Ltac lxp_cells_eq :=
  first [ reflexivity
        | apply (f_equal2 cons);
          [ first [ reflexivity | apply (f_equal C8); lxp_weqz | apply (f_equal C4); lxp_weqz | apply (f_equal C2); lxp_weqz ]
          | lxp_cells_eq ] ].

(* [comment removed for export] *)
Lemma lxp_rw_cells_join : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pcs1,(0.$5.)PB,$4.Pcs2,(0.$5.)P,(6.$4.R2.(7.R4.(8.(9.R3.))))P,(:.R7.R6.R5.R4.)P,(:.R8.R7.R4.R3.)(:.R9.R8.R7.(;.$5.R6.R4.))")
(* [comment removed for export] *).
Proof. intros segs m A cs1 B cs2 -> H1 H2. apply (proj2 (rw_cells_app segs m A cs1 cs2)). split; assumption. Qed.

(* [comment removed for export] *)
Lemma lxp_rw_cells_Cw_CB : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pc,$5.Ppost,(0.$5.)P,(:.R6.R5.R4.(;.$5.R3.(<.$5.R2.R1.)))(:.R7.R6.R5.(;.$5.R4.(<.$5.(=.(>.R3.)(?.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre c post H. pose proof (rw_cells_merge segs m A pre [c] post H) as K.
  cbn [app cells_size cells_bytes] in K. rewrite app_nil_r, PeanoNat.Nat.add_0_r in K. exact K.
Qed.

(* [comment removed for export] *)
Ltac lxp_addr_split A :=
  lazymatch A with
  | ?u + ?c => let t := constr:(true) in
               lazymatch c with Z0 => constr:((u, c)) | Zpos _ => constr:((u, c)) | Zneg _ => constr:((u, c)) | _ => constr:((A, 0)) end
  | _ => constr:((A, 0))
  end.

(* [comment removed for export] *)
Ltac lxp_gather mx A need :=
  match goal with
  | H1 : rw_cells ?sg mx A ?cs1 |- _ =>
      let z := eval cbv in (Z.of_nat (cells_size cs1)) in
      lazymatch eval cbv in (z <? need) with
      | false => idtac
      | true =>
          let p := lxp_addr_split A in
          lazymatch p with (?u, ?c1) =>
            let c2 := eval cbv in (c1 + z) in
            match goal with
            | H2 : rw_cells _ mx (u + c2) ?cs2 |- _ =>
                let J := fresh "JN" in
                first [ pose proof (lxp_rw_cells_join sg mx A cs1 (u + c2) cs2 (Z.add_assoc u c1 z) H1 H2) as J
                      | pose proof (lxp_rw_cells_join sg mx A cs1 (u + c2) cs2 eq_refl H1 H2) as J ];
                cbn [List.app] in J; clear H1 H2; lxp_gather mx A need
            | _ => idtac
            end
          end
      end
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac lxp_cells_z H :=
  repeat match type of H with
  | context [C8 ?w] => lazymatch w with Z_to_bv _ _ => fail | _ => rewrite <- (Z_to_bv_bv_unsigned w) in H end
  | context [C4 ?w] => lazymatch w with Z_to_bv _ _ => fail | _ => rewrite <- (Z_to_bv_bv_unsigned w) in H end
  | context [C2 ?w] => lazymatch w with Z_to_bv _ _ => fail | _ => rewrite <- (Z_to_bv_bv_unsigned w) in H end
  end.

(* [comment removed for export] *)
Lemma lxp_le4_le_bytes_to_word : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  pose proof (PropExec.bytes_le_to_Z_bound bs) as HB. rewrite Hl in HB. pose proof (bytes_le_to_Z_nonneg bs) as H0.
  rewrite Z.mod_small by (cbn in HB; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma lxp_rw_cells_CB4_C4 : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pbs,(0.(2.&8.))Ppost,(0.$5.)P,(:.R6.R5.R4.(;.$5.R3.(<.$5.(=.#4.R2.)R1.)))(:.R7.R6.R5.(;.$5.R4.(<.$5.(10.(11.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite lxp_le4_le_bytes_to_word by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Ltac lxp_cb4_to_c4 H pre :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A _ => apply (lxp_rw_cells_CB4_C4 sg mx A pre) in H; cbn [app] in H
  end.

Lemma lxp_rw_cells_C8j_CB8 : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pj,(0.(2.&8.))Ppost,(0.$5.)P,(6.$12.(13.(2.&8.)R2.)#8.)P,(:.R7.R6.R5.(;.$5.R4.(<.$5.(14.(11.R3.))R2.)))(:.R8.R7.R6.(;.$5.R5.(<.$5.(=.#8.R4.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre j post HL H. pose proof (lxp_rw_cells_Cw_CB segs m A pre _ post H) as K.
  cbn [csize cbytes] in K. rewrite (le8_le_bytes_to_word j HL) in K. exact K.
Qed.
Lemma lxp_rw_cells_C4j_CB4 : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pj,(0.(2.&8.))Ppost,(0.$5.)P,(6.$12.(13.(2.&8.)R2.)#4.)P,(:.R7.R6.R5.(;.$5.R4.(<.$5.(10.(11.R3.))R2.)))(:.R8.R7.R6.(;.$5.R5.(<.$5.(=.#4.R4.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre j post HL H. pose proof (lxp_rw_cells_Cw_CB segs m A pre _ post H) as K.
  cbn [csize cbytes] in K. rewrite (lxp_le4_le_bytes_to_word j HL) in K. exact K.
Qed.

(* [comment removed for export] *)
Lemma lxp_CB_length : forall segs m A pre n bs post, rw_cells segs m A (pre ++ CB n bs :: post) -> length bs = n.
Proof. intros segs m A pre n bs post [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [H2 _]]. exact H2. Qed.
Ltac lxp_note_len H pre n j :=
  try (is_var j; lazymatch goal with
                 | _ : length j = _ |- _ => idtac
                 | _ => lazymatch type of H with rw_cells ?sg ?mx ?A _ =>
                          let K := fresh "LXJ" in pose proof (lxp_CB_length sg mx A pre n j _ H) as K end
                 end).

(* [comment removed for export] *)
Ltac lxp_cells_go H pre cs :=
  lazymatch cs with
  | nil => idtac
  | CB 8 ?j :: ?rest => lxp_note_len H pre 8%nat j; cb8_to_c8 H pre; let pre' := eval cbv [List.app] in (pre ++ [C8 (le_bytes_to_word j)]) in lxp_cells_go H pre' rest
  | CB 4 ?j :: ?rest => lxp_note_len H pre 4%nat j; lxp_cb4_to_c4 H pre; let pre' := eval cbv [List.app] in (pre ++ [C4 (le_bytes_to_word j)]) in lxp_cells_go H pre' rest
  | ?c :: ?rest => let pre' := eval cbv [List.app] in (pre ++ [c]) in lxp_cells_go H pre' rest
  end.
Ltac lxp_cells H :=
  lazymatch type of H with rw_cells _ _ _ ?cs => lxp_cells_go H (@nil cell) cs end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lxp_rw_cells_app_at : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Ppost,(0.$5.)PB,$4.P,(6.$4.R1.(7.R4.(8.(9.R3.))))P,(:.R7.R6.R5.(;.$5.R4.R3.))(15.(:.R8.R7.R6.R5.)(:.R8.R7.R3.R4.))")
(* [comment removed for export] *).
Proof. intros segs m A pre post B -> H. apply (proj1 (rw_cells_app segs m A pre post)). exact H. Qed.

(* [comment removed for export] *)
Ltac lxp_chunk_split H n H1 H2 :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn] in (@firstn cell n cs) in
      let post := eval cbv beta iota delta [skipn] in (@skipn cell n cs) in
      let z := eval cbv in (Z.of_nat (cells_size pre)) in
      change (rw_cells sg mx A cs) with (rw_cells sg mx A (pre ++ post)) in H;
      lazymatch A with
      | Z.add ?u ?c =>
          first [ is_Zlit c; let v := eval cbv in (c + z) in
                  apply (lxp_rw_cells_app_at sg mx A pre post (u + v) (Z.add_assoc u c z)) in H
                | apply (lxp_rw_cells_app_at sg mx A pre post (A + z) eq_refl) in H ]
      | _ => apply (lxp_rw_cells_app_at sg mx A pre post (A + z) eq_refl) in H
      end;
      destruct H as [H1 H2]
  end.

(* [comment removed for export] *)
Ltac lxp_index_of cs z :=
  lazymatch z with
  | 0 => constr:(O)
  | _ => lazymatch cs with ?c :: ?cs' =>
           let s := eval cbv in (z - Z.of_nat (csize c)) in let n := lxp_index_of cs' s in constr:(S n) end
  end.
Ltac lxp_shift zs z := eval cbv beta iota delta [List.map Z.sub Z.add Z.opp Z.pos_sub Z.succ_double Z.pred_double Z.double Pos.pred_double] in (List.map (fun x => x - z) zs).

(* [comment removed for export] *)
Ltac lxp_cut H zs :=
  lazymatch zs with
  | nil => idtac
  | ?z :: ?zs' =>
      lazymatch type of H with rw_cells _ _ _ ?cs =>
        let n := lxp_index_of cs z in
        lazymatch n with
        | O => lxp_cut H zs'
        | _ => let A := fresh "FC" in lxp_chunk_split H n A H; let zs'' := lxp_shift zs' z in lxp_cut H zs''
        end
      end
  end.

(* [comment removed for export] *)
Ltac lxp_locate cs d :=
  lazymatch cs with ?c :: ?cs' =>
    let w := eval cbv in (Z.of_nat (csize c)) in
    lazymatch eval cbv in (d <? w) with
    | true => constr:((O, d))
    | false => let d' := eval cbv in (d - w) in
               lazymatch lxp_locate cs' d' with (?n, ?e) => constr:((S n, e)) end
    end
  end.

(* [comment removed for export] *)
Ltac lxp_zlit_shape c := lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Lemma lxp_cell_to_CB : forall segs m A c, rw_cells segs m A [c] -> rw_cells segs m A [CB (csize c) (cbytes c)].
Proof.
  intros segs m A c H. pose proof (rw_cells_merge segs m A [] [c] [] H) as K. cbn [app cells_size cells_bytes] in K.
  rewrite app_nil_r, PeanoNat.Nat.add_0_r in K. exact K.
Qed.
Ltac lxp_cell_cut1 H e :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A [?c] =>
      apply (lxp_cell_to_CB sg mx A c) in H; cbn [csize cbytes] in H;
      lazymatch type of H with rw_cells _ _ _ [CB ?n ?bs] =>
        let e' := eval cbv in (Z.to_nat e) in
        let r := eval cbv in (Nat.sub n e') in
        let K := fresh "FC" in
        pose proof (rw_cells_split_CB sg mx A [] n bs [] [e'; r] H eq_refl) as K; clear H;
        cbn [app mk_CB_cells firstn skipn le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in K;
        (* [comment removed for export] *)
        repeat match type of K with context [bv_unsigned (Z_to_bv 64 ?z)] =>
          lxp_zlit_shape z; let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in
          change (bv_unsigned (Z_to_bv 64 z)) with v in K end;
        repeat match type of K with context [Z.shiftr ?a ?b] =>
          lxp_zlit_shape a; lxp_zlit_shape b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in K end;
        rename K into H;
        let K1 := fresh "FC" in lxp_chunk_split H 1%nat K1 H
      end
  end.

(* [comment removed for export] *)
Ltac lxp_cut_hyp H c cs t :=
  let sz := eval cbv in (Z.of_nat (cells_size cs)) in
  let d := eval cbv in (t - c) in
  lazymatch eval cbv in (andb (0 <? d) (d <? sz)) with
  | true =>
      lazymatch lxp_locate cs d with
      | (?n, 0) => let A := fresh "FC" in lxp_chunk_split H n A H
      | (?n, ?e) =>
          (* [comment removed for export] *)
          (lazymatch n with O => idtac | _ => let A := fresh "FC" in lxp_chunk_split H n A H end);
          (lazymatch type of H with
           | rw_cells _ _ _ [_] => idtac
           | _ => let B := fresh "FC" in lxp_chunk_split H 1%nat H B end);
          lxp_cell_cut1 H e
      end
  end.
Ltac lxp_cut_at u t :=
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
    match goal with
    | H : rw_cells _ mx (u + ?c) ?cs |- _ => is_Zlit c; lxp_cut_hyp H c cs t
    | H : rw_cells _ mx u ?cs |- _ => lxp_cut_hyp H 0 cs t
    | _ => idtac
    end
  end.
Ltac lxp_cuts_at u cb zs :=
  lazymatch zs with
  | nil => idtac
  | ?z :: ?zs' => let t := eval cbv in (cb + z) in lxp_cut_at u t; lxp_cuts_at u cb zs'
  end.

(* [comment removed for export] *)
Ltac lxp_frame_cut base zs :=
  lazymatch base with
  | ?u + ?cb => lxp_cuts_at u cb zs
  | ?u => lxp_cuts_at u 0 zs
  end.
Ltac lxp_cuts base zs := lxp_frame_cut base zs.

(* [comment removed for export] *)
Ltac lxp_cut_mem m u t :=
  match goal with
  | H : rw_cells _ m (u + ?c) ?cs |- _ => is_Zlit c; lxp_cut_hyp H c cs t
  | H : rw_cells _ m u ?cs |- _ => lxp_cut_hyp H 0 cs t
  | _ => idtac
  end.
Ltac lxp_cuts_mem m u ts :=
  lazymatch ts with
  | nil => idtac
  | ?t :: ?ts' => lxp_cut_mem m u t; lxp_cuts_mem m u ts'
  end.
(* [comment removed for export] *)
Ltac lxp_psums cs acc :=
  lazymatch cs with
  | nil => constr:(@nil Z)
  | ?c :: ?r => let a := eval cbv in (acc + Z.of_nat (csize c)) in let t := lxp_psums r a in constr:(@cons Z a t)
  end.

(* [comment removed for export] *)
Lemma lxp_le2_le_bytes_to_word : forall bs, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  pose proof (PropExec.bytes_le_to_Z_bound bs) as HB. rewrite Hl in HB. pose proof (bytes_le_to_Z_nonneg bs) as H0.
  rewrite Z.mod_small by (cbn in HB; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.
Lemma lxp_rw_cells_CB2_C2 : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pbs,(0.(2.&8.))Ppost,(0.$5.)P,(:.R6.R5.R4.(;.$5.R3.(<.$5.(=.#2.R2.)R1.)))(:.R7.R6.R5.(;.$5.R4.(<.$5.(16.(11.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite lxp_le2_le_bytes_to_word by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.
Lemma lxp_rw_cells_CB1_C1 : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pb,(2.&8.)Ppost,(0.$5.)P,(:.R6.R5.R4.(;.$5.R3.(<.$5.(=.#1.(<.(2.&8.)R2.(17.(2.&8.))))R1.)))(:.R7.R6.R5.(;.$5.R4.(<.$5.(18.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre b post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes app] in *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Ltac lxp_adapt_go H pre cs cs' :=
  lazymatch cs' with
  | nil => idtac
  | ?c' :: ?rest' =>
      lazymatch cs with ?c :: ?rest =>
        let sg := lazymatch type of H with rw_cells ?sg _ _ _ => sg end in
        let mx := lazymatch type of H with rw_cells _ ?mx _ _ => mx end in
        let A := lazymatch type of H with rw_cells _ _ ?A _ => A end in
        let next c2 := (let pre' := eval cbv [List.app] in (pre ++ [c2]) in lxp_adapt_go H pre' rest rest') in
        lazymatch c' with
        | C8 _ => lazymatch c with
                  | CB 8 ?bs => apply (rw_cells_CB8_C8 sg mx A pre) in H; cbn [app] in H; next constr:(C8 (le_bytes_to_word bs))
                  | _ => next c end
        | C4 _ => lazymatch c with
                  | CB 4 ?bs => apply (lxp_rw_cells_CB4_C4 sg mx A pre) in H; cbn [app] in H; next constr:(C4 (le_bytes_to_word bs))
                  | _ => next c end
        | C2 _ => lazymatch c with
                  | CB 2 ?bs => apply (lxp_rw_cells_CB2_C2 sg mx A pre) in H; cbn [app] in H; next constr:(C2 (le_bytes_to_word bs))
                  | _ => next c end
        | C1 _ => lazymatch c with
                  | CB 1 [?b] => apply (lxp_rw_cells_CB1_C1 sg mx A pre) in H; cbn [app] in H; next constr:(C1 b)
                  | _ => next c end
        | CB ?n' _ =>
            let n := eval cbv in (csize c) in
            lazymatch eval cbv in (Nat.eqb n n') with
            | true => lazymatch c with
                      | CB _ _ => next c
                      | C8 (le_bytes_to_word ?j) =>
                          first [ lazymatch goal with LXJ : length j = 8%nat |- _ =>
                                    apply (lxp_rw_cells_C8j_CB8 sg mx A pre j _ LXJ) in H; cbn [app] in H; next constr:(CB 8 j) end
                                | let bs := eval cbn [cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in (cbytes c) in
                                  apply (lxp_rw_cells_Cw_CB sg mx A pre) in H;
                                  cbn [app csize cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in H;
                                  next constr:(CB n bs) ]
                      | C4 (le_bytes_to_word ?j) =>
                          first [ lazymatch goal with LXJ : length j = 4%nat |- _ =>
                                    apply (lxp_rw_cells_C4j_CB4 sg mx A pre j _ LXJ) in H; cbn [app] in H; next constr:(CB 4 j) end
                                | let bs := eval cbn [cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in (cbytes c) in
                                  apply (lxp_rw_cells_Cw_CB sg mx A pre) in H;
                                  cbn [app csize cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in H;
                                  next constr:(CB n bs) ]
                      | _ => let bs := eval cbn [cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in (cbytes c) in
                             apply (lxp_rw_cells_Cw_CB sg mx A pre) in H;
                             cbn [app csize cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in H;
                             next constr:(CB n bs)
                      end
            | false =>
                (* [comment removed for export] *)
                let k := lxp_index_of cs (Z.of_nat n') in
                let mid := eval cbv beta iota delta [firstn] in (@firstn cell k cs) in
                let post := eval cbv beta iota delta [skipn] in (@skipn cell k cs) in
                change (rw_cells sg mx A (pre ++ mid ++ post)) in H;
                apply (rw_cells_merge sg mx A pre mid post) in H;
                cbn [app cells_size csize Nat.add cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes] in H;
                lazymatch type of H with rw_cells _ _ _ ?cs2 =>
                  let c2 := eval cbv beta iota delta [nth] in (@nth cell (length pre) cs2 (CB 0 nil)) in
                  let pre' := eval cbv [List.app] in (pre ++ [c2]) in
                  lxp_adapt_go H pre' post rest'
                end
            end
        | _ => next c
        end
      end
  end.
(* [comment removed for export] *)
Ltac lxp_adapt H cs' :=
  lazymatch type of H with rw_cells _ _ _ ?cs => lxp_adapt_go H (@nil cell) cs cs' end.

(* [comment removed for export] *)
Ltac lxp_pre_of cs c :=
  lazymatch cs with
  | c :: _ => constr:(@nil cell)
  | ?x :: ?r => let p := lxp_pre_of r c in constr:(x :: p)
  end.
(* [comment removed for export] *)
Ltac lxp_spine_todo cs :=
  lazymatch cs with
  | nil => fail
  | _ :: ?r => lxp_spine_todo r
  | ?l1 ++ _ => lazymatch l1 with _ :: _ => constr:(0) | nil => constr:(0) | _ ++ _ => constr:(0) | _ => head_of l1 end
  | _ => head_of cs
  end.
Ltac lxp_chunk :=
  (* [comment removed for export] *)
  repeat (lazymatch goal with |- rw_cells _ _ _ ?cs0 =>
    let t := lxp_spine_todo cs0 in
    lazymatch t with
    | 0 => cbn [List.app]
    | ?h => cbv delta [h]; cbn [List.app]
    end end);
  lazymatch goal with |- rw_cells _ ?m ?A ?cs' =>
    let need := eval cbv in (Z.of_nat (cells_size cs')) in
    let p := lxp_addr_split A in
    lazymatch p with (?u, ?c0) =>
      let bs := lxp_psums cs' c0 in
      lxp_cut_mem m u c0; lxp_cuts_mem m u bs;
      lxp_gather m A need;
      match goal with H : rw_cells _ m A ?cs |- _ =>
        first [ exact H
              | lxp_adapt H cs';
                lazymatch type of H with rw_cells _ _ _ ?cs2 =>
                  first [ exact H | apply (lxp_rw_cells_retype _ m A cs2 cs' H); lxp_cells_eq ] end ] end
    end
  end.

(* [comment removed for export] *)
Ltac lxp_side :=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aevtM _ _ _ _ => idtac
  | |- rw_cells _ _ _ _ => lxp_chunk
  | |- bytes_at _ ?m ?A _ => match goal with H : bytes_at _ m A _ |- _ => exact H end
  | |- ro_cells _ ?m ?A _ => match goal with H : ro_cells _ m A _ |- _ => exact H end
  | |- stk _ ?m _ _ => match goal with H : stk _ m _ _ |- _ => exact H end
  | |- statics_ok _ _ ?m => match goal with H : statics_ok _ _ m |- _ => exact H end
  | |- mem_inv _ ?m => match goal with H : mem_inv _ m |- _ => exact H end
  | |- ?T => tryif lxp_arith T then try lxp_lia else (try assumption)
  end.

(* [comment removed for export] *)
Ltac lxp_reg_refl :=
  try (lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
       end).

(* [comment removed for export] *)
Tactic Notation "callx" tactic3(apptac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ apptac; lxp_side | post_call segs m ]
  end.
Tactic Notation "callx_sp" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ apptac; lxp_side
      | lazymatch goal with |- forall x, ?P x -> _ => let h := head_of P in try unfold h end;
        rewrite ?(unsigned_lit e) by plia; post_call segs m ]
  end.

(* [comment removed for export] *)
Ltac lxp_explode H :=
  lazymatch type of H with
  | rw_cells _ _ _ [_] => idtac
  | rw_cells _ _ _ (_ :: _) => let A := fresh "FC" in lxp_chunk_split H 1%nat A H; lxp_explode H
  | rw_cells _ _ _ [] => clear H
  end.

(* [comment removed for export] *)
Ltac lxp_chunk_join H1 H2 H := chunk_join H1 H2 H.

(* [comment removed for export] *)
Ltac lxp_name_junk FR :=
  repeat match type of FR with context [CB _ (firstn ?n ?t)] =>
    let j := fresh "j" in set (j := @firstn byte n t) in FR; clearbody j end.
Ltac lxp_split_frame L :=
  lazymatch goal with FR : rw_cells ?sg ?mx ?a [CB ?F ?jk] |- _ =>
    let FRS := fresh "FRS" in
    pose proof (rw_cells_split_CB sg mx a [] F jk [] L FR eq_refl) as FRS; cbn [mk_CB_cells app] in FRS;
    clear FR; rename FRS into FR; lxp_name_junk FR; try clear jk; lxp_cells FR
  end.

(* [comment removed for export] *)
Ltac lxp_sep H F :=
  lazymatch type of H with
  | ?A + ?n <= ?lo \/ bv_unsigned ?sp <= ?A' =>
      let H' := fresh "FS" in
      assert (H' : A + n <= bv_unsigned sp + - F \/ bv_unsigned sp + - F + F <= A') by (lxp_arith_ctx; prune_disj; lia)
  end.
(* [comment removed for export] *)
Ltac lxp_seps F := idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_norm_cells :=
  repeat match goal with H : rw_cells _ _ _ ?cs |- _ =>
    let t := lxp_spine_todo cs in
    lazymatch t with
    | 0 => cbn [List.app] in H
    | ?h => cbv delta [h] in H; cbn [List.app] in H
    end end;
  repeat match goal with H : rw_cells ?sg ?mx ?A ?cs |- _ =>
    match cs with context [C1 ?b] =>
      lazymatch b with
      | Z_to_bv 8 _ => fail
      | _ => is_var b; let pre := lxp_pre_of cs constr:(C1 b) in
             apply (lxp_rw_cells_Cw_CB sg mx A pre (C1 b)) in H; cbn [app csize cbytes] in H
      end end end;
  (* [comment removed for export] *)
  repeat match goal with H : rw_cells _ _ _ ?cs |- _ =>
    match cs with
    | context [CB 8 ?j] => is_var j; lxp_cells H
    | context [CB 4 ?j] => is_var j; lxp_cells H
    end end.

(* [comment removed for export] *)
Lemma lxp_aevtM_of_evt : forall segs mo Q ms,
  MOK mo -> evt segs (fun x => aevtM segs mo Q x) ms -> aevtM segs mo Q ms.
Proof. intros segs mo Q ms MK H. eapply aevtM_cut_evt; [exact MK | exact H | intros ms' H'; exact H']. Qed.

Ltac lxp_toevt :=
  lazymatch goal with
  | |- aevtM ?segs ?mo ?Q ?ms =>
      first [ lazymatch goal with MK : MOK mo |- _ => apply (lxp_aevtM_of_evt segs mo Q ms MK) end
            | lazymatch goal with HH : HEAP segs ?L ?HI _ _ _ mo |- _ =>
                apply (lxp_aevtM_of_evt segs mo Q ms (heap_mok segs L HI _ _ _ _ HH)) end
            | fail 0 "lxp_toevt: no hypothesis (MOK" mo ") / (HEAP .." mo ")" ]
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_is_protected H := fail.
Ltac lxp_gc_clear H := tryif lxp_is_protected H then fail else clear H.
Ltac lxp_dedup := repeat match goal with H : ?T, H' : ?T |- _ => lazymatch type of T with Prop => first [ lxp_gc_clear H | lxp_gc_clear H' ] end end.
Ltac lxp_gc :=
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
    repeat match goal with H : ?T |- _ =>
      lazymatch T with
      | rw_cells _ ?mm _ _ => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | ro_cells _ ?mm _ _ => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | bytes_at _ ?mm _ _ => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | stk _ ?mm _ _ => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | mem_inv _ ?mm => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | munch _ _ ?mm => tryif constr_eq mm mx then fail else lxp_gc_clear H
      | wmono _ _ ?mm => tryif constr_eq mm mx then fail else lxp_gc_clear H
      end end
  end.


Ltac lxp_names :=
  try lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
    (* [comment removed for export] *)
    repeat match goal with
      Ho : bytes_at _ ?mo ?A ?bs, Hn : bytes_at _ mx ?A ?bs |- _ =>
        tryif constr_eq mo mx then fail else (lxp_gc_clear Ho; rename Hn into Ho) end;
    repeat match goal with
      Ho : rw_cells _ ?mo ?A _, Hn : rw_cells _ mx ?A _ |- _ =>
        tryif constr_eq mo mx then fail else (lxp_gc_clear Ho; rename Hn into Ho) end;
    repeat match goal with
      Ho : ro_cells _ ?mo ?A _, Hn : ro_cells _ mx ?A _ |- _ =>
        tryif constr_eq mo mx then fail else (lxp_gc_clear Ho; rename Hn into Ho) end;
    repeat match goal with
      Ho : stk _ ?mo _ _, Hn : stk _ mx _ _ |- _ =>
        tryif constr_eq mo mx then fail else (lxp_gc_clear Ho; rename Hn into Ho) end;
    (* [comment removed for export] *)
    first [ match goal with E : @eq mem ?a _ |- _ => is_var a end | lxp_gc ];
    try match goal with H : munch _ _ mx |- _ => rename H into MU end;
    try match goal with H : wmono _ _ mx |- _ => rename H into WM end;
    try match goal with H : mem_inv _ mx |- _ => rename H into MI end
  end.

(* [comment removed for export] *)
Ltac lxp_back_to_aevtM :=
  try lazymatch goal with |- evt _ (fun _ => aevtM _ _ _ _) _ => apply evt_done; cbv beta end.

(* [comment removed for export] *)
Ltac lxp_box_frame :=
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    try match goal with MU0 : munch ?W ?m0 mc, WM0 : wmono ?sg ?m0 mc |- _ =>
      tryif constr_eq m0 mc then fail else
        (let B := fresh "MWbox" in pose proof (conj MU0 WM0) as B; clear MU0 WM0) end
  end.
Ltac lxp_unbox_frame :=
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
    try match goal with B : munch ?W ?m0 ?mc /\ wmono ?sg ?m0 ?mc |- _ =>
      match goal with MUr : munch ?W' mc mx, WMr : wmono _ mc mx |- _ =>
        let MU := fresh "MU" in let WM := fresh "WM" in
        first [ pose proof (munch_trans W m0 mc mx (proj1 B) (munch_weaken W' W mc mx ltac:(unfold sub_fp; cbn [outside]; clear; intros; lia) MUr)) as MU
              | idtac "lxp: run footprint not inside the declared footprint; keeping the relative munch only" ];
        pose proof (wmono_trans _ m0 mc mx (proj2 B) WMr) as WM;
        (* [comment removed for export] *)
        let R := fresh "MWrel" in pose proof (conj MUr WMr) as R; clear MUr WMr B
      end end
  end.
(* [comment removed for export] *)
Ltac lxp_same_mem := try match goal with E : @eq mem ?lxm ?m0 |- _ => is_var lxm; subst lxm end.
(* [comment removed for export] *)
Ltac lxp_no_add0 :=
  repeat match goal with H : context [Z.add _ 0] |- _ => rewrite Z.add_0_r in H end;
  repeat match goal with |- context [Z.add _ 0] =>
    lazymatch goal with |- ?G => tryif has_evar G then fail else rewrite Z.add_0_r end end.
(* [comment removed for export] *)
Lemma lxp_lit_disj_hull : forall r a b : Z, r = a \/ r = b -> Z.min a b <= r <= Z.max a b.
Proof. intros r a b [-> | ->]; lia. Qed.
Ltac lxp_lit_disj :=
  repeat match goal with H : ?r = ?a \/ ?r = ?b |- _ =>
    is_var r; lxp_zlit_shape a; lxp_zlit_shape b;
    lazymatch goal with
    | _ : a <= r <= b |- _ => fail
    | _ : b <= r <= a |- _ => fail
    | _ => let lo := eval vm_compute in (Z.min a b) in let hi := eval vm_compute in (Z.max a b) in
           let K := fresh "LD" in assert (K : lo <= r <= hi) by (generalize (lxp_lit_disj_hull r a b H); clear; cbn; lia)
    end end.
(* [comment removed for export] *)
Lemma lxp_opq_statics : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Psegs,(0.$1.)PL,$19.Pm,P,(2.&40.)(3.(2.&8.))P,(1:.R3.R2.R1.)(1;.R4.$1<.L,$4.$1=.(1:.R4.R3.)(<.(1>.$4.$4.)(1?.$4.$4.=(20.R3.))(<.(1>.$4.$4.)(1?.$4.$4.(21.R3.)+10000000000000000.)(17.(1>.$4.$4.))))(17.$22.)R2.)")
(* [comment removed for export] *).
Proof.
  intros segs L m SO.
  apply (lx_opq_intro segs lx_no_layout (fun _ => True) (statics_ok segs L) (fun a => a < hl_data_lo L \/ hl_data_hi L <= a));
    [exact SO| | | intros lo hi c [] ].
  - intros W m1 m2 H1 MU WM HW. apply (statics_ok_munch segs L W m1 m2 H1 MU).
    intros a Ha _. clear - HW Ha. induction HW as [|[u v] W' Hiv HW' IH]; cbn [outside]; [exact I|].
    split; [| exact IH]. intros Hin. cbn [fst snd] in Hiv. specialize (Hiv a Hin). lia.
  - intros lo hi a [E|[E|[]]] Ha; injection E as <- <-; lia.
Qed.
(* [comment removed for export] *)
Ltac lxp_statics_box_at m :=
  match goal with
  | _ : lx_opq _ _ _ (statics_ok _ _) _ _ m |- _ => idtac
  | SO : statics_ok ?segs ?L m |- _ => pose proof (lxp_opq_statics segs L m SO)
  | _ => idtac
  end.
Ltac lxp_statics_box :=
  lazymatch goal with
  | SU : forall AL', List.Forall (summary_okO _ AL' _ ?OPS _) _ |- _ (MS _ _ _ _ _ ?m _) =>
      lazymatch OPS with context [statics_ok _ _] => lxp_statics_box_at m | _ => idtac end
  | SU : List.Forall (summary_okO _ _ _ ?OPS _) _ |- _ (MS _ _ _ _ _ ?m _) =>
      lazymatch OPS with context [statics_ok _ _] => lxp_statics_box_at m | _ => idtac end
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lxp_statics_unbox :=
  repeat match goal with
  | K : lx_opq _ _ _ (statics_ok ?segs ?L) _ _ ?m |- _ =>
      first [ lazymatch goal with _ : statics_ok segs L m |- _ => clear K end
            | let H := fresh "SOK" in pose proof (lx_opq_holds _ _ _ _ _ _ _ K) as H; cbv beta in H; clear K ]
  end.

(* [comment removed for export] *)
Ltac lxp_run_pre := idtac.
Ltac lxp_run_post := idtac.
(* [comment removed for export] *)
Ltac lxp_frag_list mx :=
  let rec go acc :=
    match goal with
    | H : rw_cells _ mx ?A _ |- _ => lazymatch acc with context [A] => fail | _ => go constr:(@cons Z A acc) end
    | _ => acc
    end in
  go constr:(@nil Z).
Ltac lxp_frag_note :=
  try match goal with F := _ : list Z |- _ => clear F end;
  try lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
    let l := lxp_frag_list mc in pose (lxp_fragl := l) end.
Ltac lxp_refrag_go mx l :=
  lazymatch l with
  | nil => idtac
  | ?a :: ?r =>
      (let p := lxp_addr_split a in lazymatch p with (?u, ?c) => try lxp_cut_mem mx u c end);
      lxp_refrag_go mx r
  end.
Ltac lxp_refrag :=
  try lazymatch goal with F := ?l : list Z |- _ (MS _ _ _ _ _ ?mx _) => lxp_refrag_go mx l end.
(* [comment removed for export] *)
Ltac lxp_run_refrag := idtac.
(* [comment removed for export] *)
Ltac lxp_unjunk :=
  try lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
    repeat match goal with
    | H : rw_cells ?sg mx ?A ?cs, LXJ : length ?j = 8%nat |- _ =>
        lazymatch cs with context [C8 (le_bytes_to_word j)] =>
          let pre := lxp_pre_of cs constr:(C8 (le_bytes_to_word j)) in
          apply (lxp_rw_cells_C8j_CB8 sg mx A pre j _ LXJ) in H; cbn [app] in H end
    | H : rw_cells ?sg mx ?A ?cs, LXJ : length ?j = 4%nat |- _ =>
        lazymatch cs with context [C4 (le_bytes_to_word j)] =>
          let pre := lxp_pre_of cs constr:(C4 (le_bytes_to_word j)) in
          apply (lxp_rw_cells_C4j_CB4 sg mx A pre j _ LXJ) in H; cbn [app] in H end
    end end.
Ltac lxp_run pl := lxp_run_pre; lxp_statics_box; lxp_norm_cells; lxp_no_add0; lxp_lit_disj; lxp_toevt; lxp_box_frame; lxp_frag_note; lx_run_tac pl; lx_tree;
                   lxp_back_to_aevtM; lxp_unbox_frame; lxp_statics_unbox; lxp_run_refrag; lxp_names; lxp_same_mem; lxp_dedup; lxp_unjunk; lxp_run_post.

(* [comment removed for export] *)
Ltac lxp_name_mem mname :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => is_var mx; rename mx into mname end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_clear_mem mo := repeat match goal with H : context [mo] |- _ => clear H end; try clear mo.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxp_statics_from L mx SO MU :=
                let H := fresh "SOK" in
                pose proof (statics_ok_munch _ L _ _ _ SO MU) as H;
                lazymatch type of H with ?P -> _ =>
                  let lo := lazymatch goal with _ : stk _ mx ?lo _ |- _ => lo end in
                  assert P as Htmp by (intros aa Ha _; cbn;
                                       repeat match goal with K : _ |- _ => lazymatch type of K with
                                         | context [hl_data_lo] => fail | context [hl_data_hi] => fail | context [alloc_ceiling] => fail
                                         | context [hl_stack] => fail
                                         | context [lo] => fail | Z => fail | _ => clear K end end;
                                       first [ exact I | lia | repeat split; lia | repeat split; lxp_arith_ctx; lia ]);
                  specialize (H Htmp); clear Htmp end.
Ltac lxp_statics_mem L mx :=
    first [ lazymatch goal with _ : statics_ok _ L mx |- _ => idtac end
          | match goal with MU : munch ?W ?m0 mx, SO : statics_ok _ L ?m0 |- _ => lxp_statics_from L mx SO MU end
          | match goal with B : munch ?W ?m0 mx /\ wmono _ ?m0 mx, SO : statics_ok _ L ?m0 |- _ =>
              lxp_statics_from L mx SO (proj1 B) end ].
Ltac lxp_statics_for L :=
  lazymatch goal with
  | |- statics_ok _ _ ?mx => lxp_statics_mem L mx
  | |- _ (MS _ _ _ _ _ ?mx _) => lxp_statics_mem L mx
  end.
(* [comment removed for export] *)
Ltac lxp_statics :=
  match goal with
  | _ : statics_ok _ ?L _ |- _ => lxp_statics_for L
  | _ => idtac
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lxp_zswrap32_errsum : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Pr,$4.Pc,$4.Pk,$4.P,(6.$4.R1.(23.+10000000000000000.R2.))P,(15.(24.=R3.)(24.R3.+40000000.))P,(15.(25.-40000000.R5.)(25.R5.=))(6.$4.(26.+20.(27.+20.(7.R6.R4.)))(23.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros r c k -> Hc Hr. unfold zswrap, zlow.
  change (2 ^ 32) with 4294967296. change (2 ^ (32 - 1)) with 2147483648.
  replace (r + (18446744073709551616 - c)) with ((r - c) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full.
  rewrite <- (Z.mod_unique (r - c) 4294967296 (-1) (r - c + 4294967296)) by lia.
  rewrite <- (Z.mod_unique (r - c + 4294967296 + 2147483648) 4294967296 1 (r - c + 2147483648)) by lia.
  lia.
Qed.

Ltac lxp_errsum :=
  match goal with |- context [zswrap 32 (zlow 32 (?r + ?k))] =>
    is_Zlit k; let c := eval vm_compute in (18446744073709551616 - k) in
    rewrite (lxp_zswrap32_errsum r c k eq_refl) by (lxp_arith_ctx; prune_disj; lia)
  end.

Ltac lxp_errsum_lia := try lxp_errsum; lxp_lia.

(* [comment removed for export] *)
Ltac lxp_hyp :=
  match goal with
  | H : ?C |- ?C => exact H
  | H : _ -> ?C |- ?C => apply H; lxp_lia
  | H : _ -> _ -> ?C |- ?C => apply H; lxp_lia
  end.

(* [comment removed for export] *)
Ltac lxp_exhyp_with H :=
  lxp_dex H; lxp_dand H; intros; lx_exs; lx_ands;
  first [ eassumption | reflexivity | lxp_lia | lxp_hyp
        | lazymatch goal with |- _ \/ _ => first [ left; lx_ands; first [ eassumption | lxp_lia ]
                                               | right; lx_ands; first [ eassumption | lxp_lia ] ] end ].
Ltac lxp_exhyp :=
  lazymatch goal with |- exists _, _ =>
    match goal with
    | H : exists _, _ |- _ => lxp_exhyp_with H
    | H : _ -> exists _, _ |- _ =>
        let K := fresh "EXH" in
        pose proof (H ltac:(first [ reflexivity | assumption | lxp_lia ])) as K; lxp_exhyp_with K
    end
  end.

(* [comment removed for export] *)
Ltac lxp_release :=
  lazymatch goal with |- stk ?sg ?m ?lo ?hi =>
    match goal with ST : stk _ m lo ?hi' |- _ =>
      let need := eval cbv in (0) in
      let p := lxp_addr_split hi' in
      lazymatch p with (?u, ?c0) =>
        (* [comment removed for export] *)
        let ph := lxp_addr_split hi in
        lazymatch ph with (?u2, ?c2) =>
          let len := eval cbv in (c2 - c0) in
          (* [comment removed for export] *)
          try lxp_cut_mem m u c2;
          lxp_gather m hi' len;
          match goal with FR : rw_cells _ m hi' ?cs |- _ =>
            let K := fresh "STR" in
            pose proof (stk_release sg m lo hi' cs ST FR ltac:(lxp_arith_ctx; prune_disj; lia)) as K;
            cbn [cells_size csize Nat.add] in K;
            lazymatch type of K with stk _ _ _ ?h2 => replace h2 with hi in K by (clear; lia) end;
            exact K
          end
        end
      end
    end
  end.

Lemma lxp_zlow64_nonpos_zero : forall r, -18446744073709551616 < r < 18446744073709551616 -> 0 <= - zlow 64 r -> r = 0.
Proof. intros r Hr Hz. unfold zlow in Hz. pose proof (Z.mod_pos_bound r 18446744073709551616 ltac:(lia)) as B.
  assert (M : r mod 18446744073709551616 = 0) by lia.
  apply Z.mod_divide in M; [|lia]. destruct M as [k ->]. assert (k = 0) by lia. lia. Qed.
(* [comment removed for export] *)
Ltac lxp_ends1 t := lazymatch t with Z.add _ ?b => lxp_ends1 b | 1 => idtac end.
Ltac lxp_is_postcase T := match T with context [?x <= 0] => lxp_ends1 x end.
Ltac lxp_refute_closed a n := assert (n : ~ a) by (clear; intro; lia).
Ltac lxp_disj_prune :=
  repeat match goal with
  | H : ?a \/ ?b |- _ =>
      let n := fresh "n" in let H' := fresh "Hd" in
      first [ lxp_refute_closed a n;
              assert (H' : b) by (destruct H as [H|H]; [exact (False_ind _ (n H)) | exact H]);
              clear n H; rename H' into H
            | lxp_refute_closed b n;
              assert (H' : a) by (destruct H as [H|H]; [exact H | exact (False_ind _ (n H))]);
              clear n H; rename H' into H
            | lazymatch b with ?b1 \/ ?b2 =>
                lxp_refute_closed b1 n;
                assert (H' : a \/ b2) by (destruct H as [H|[H|H]]; [left; exact H | exact (False_ind _ (n H)) | right; exact H]);
                clear n H; rename H' into H
              end ]
  end.
Ltac lxp_settle_results :=
  repeat match goal with
  | Hz : 0 <= - zlow 64 ?v |- _ =>
      is_var v; let E := fresh "R0" in
      assert (E : v = 0) by (apply lxp_zlow64_nonpos_zero; [clear Hz; lxp_arith_ctx; clear_disj; lia | exact Hz]);
      subst v; clear Hz
  end.
Ltac lxp_uw_norm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by (clear_disj; lia)
  | H : context [bv_unsigned (Z_to_bv 64 ?x)] |- _ => rewrite (unsigned_lit x) in H by (clear_disj; lia)
  end.
Ltac lxp_clear_seps_but_post :=
  repeat match goal with
  | H : ?T |- _ => lazymatch T with _ \/ _ => tryif lxp_is_postcase T then fail else clear H end
  end.
Ltac lxp_logic_light :=
  repeat first [ eassumption | reflexivity | lia
               | lazymatch goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end ].
Ltac lxp_case_imp :=
  lazymatch goal with |- _ -> _ =>
    match goal with K : ?T |- _ => lxp_is_postcase T end;
    let G := fresh "HG" in intros G;
    lxp_arith_ctx; lxp_bool_hyps;
    (try lazymatch type of G with ?a = ?b => first [ is_var a; subst a | is_var b; subst b | idtac ] end);
    lxp_settle_results; lxp_clear_seps_but_post; lxp_disj_prune; lxp_uw_norm;
    first [ exfalso; clear - G; lia | lxp_logic_light ]
  end.

(* [comment removed for export] *)
Ltac lxp_goal :=
  lxp_no_add0;
  lazymatch goal with
  | |- @eq machine_state _ _ => reflexivity
  | |- Z_to_bv _ ?x = Z_to_bv _ ?r =>
      first [ lazymatch x with
              | context [Z.b2z ?bb] =>
                  lazymatch bb with true => idtac | false => idtac end;
                  let v := eval vm_compute in (let u := x mod 2^64 in if u <? 2^63 then u else u - 2^64) in
                  unify r v; apply bv_eq; vm_compute; reflexivity
              end
            | (* [comment removed for export] *)
              is_Zlit x;
              let v := eval vm_compute in (let u := x mod 2^64 in if u <? 2^63 then u else u - 2^64) in
              unify r v; apply bv_eq; vm_compute; reflexivity
            | reflexivity | lx_weq ]
  | |- @eq (bv _) ?a _ => first [ reflexivity | match goal with H : a = _ |- _ => exact H end | lxp_weqz | lx_weq ]
  | |- rw_cells _ ?m ?A ?cs' =>
      (* [comment removed for export] *)
      first [ match goal with H : rw_cells _ m A _ |- _ => exact H end | lxp_chunk ]
  | |- ro_cells _ ?m ?A _ => first [ match goal with H : ro_cells _ m A _ |- _ => exact H end
                                   | match goal with H : ro_cells _ m _ _ |- _ => exact H end ]
  | |- bytes_at _ ?m ?A _ => first [ match goal with H : bytes_at _ m A _ |- _ => exact H end
                                   | match goal with H : bytes_at _ m _ _ |- _ => exact H end ]
  | |- u8arr _ ?m ?A _ => first [ match goal with H : u8arr _ m A _ |- _ => exact H end
                                | match goal with H : u8arr _ m _ _ |- _ => exact H end ]
  | |- stk _ ?m _ _ => first [ match goal with H : stk _ m _ _ |- _ => exact H end | lxp_release ]
  | |- statics_ok _ _ ?m => first [ match goal with H : statics_ok _ _ m |- _ => exact H end
                                   | lxp_statics; match goal with H : statics_ok _ _ m |- _ => exact H end ]
  | |- munch _ _ ?m => match goal with H : munch _ _ m |- _ => first [ exact H | eapply munch_weaken; [| exact H]; unfold sub_fp; cbn [outside]; clear; intros; lia ] end
  (* [comment removed for export] *)
  | |- _ -> ?B => first [ solve [ lxp_case_imp ] | lxp_errsum_lia | intro; lxp_goal ]
  | |- _ /\ _ => first [ lxp_errsum_lia | lxp_hyp | split; lxp_goal ]
  | |- exists _, _ => first [ lxp_hyp | lxp_exhyp
                            | (* [comment removed for export] *)
                              eexists; lxp_goal ]
  | |- _ \/ _ => first [ left; reflexivity | right; reflexivity | lxp_errsum_lia | lxp_hyp
                        | left; first [ lxp_hyp | lxp_errsum_lia ]
                        | right; first [ lxp_hyp | lxp_errsum_lia ] ]
  | |- In _ _ => cbn; repeat (first [ left; reflexivity | right ])
  | |- _ => first [ lxp_errsum_lia | lxp_hyp ]
  end.

(* [comment removed for export] *)
Ltac lxp_goal_shape :=
  lazymatch goal with
  | |- @eq machine_state _ _ => reflexivity
  | |- Z_to_bv _ _ = Z_to_bv _ _ => lxp_goal
  | |- @eq (bv _) _ _ => lxp_goal
  | |- rw_cells _ _ _ _ => lxp_goal
  | |- ro_cells _ _ _ _ => lxp_goal
  | |- bytes_at _ _ _ _ => lxp_goal
  | |- u8arr _ _ _ _ => lxp_goal
  | |- stk _ _ _ _ => lxp_goal
  | |- statics_ok _ _ _ => lxp_goal
  | |- munch _ _ _ => lxp_goal
  | |- wmono _ _ ?m => match goal with H : wmono _ _ m |- _ => exact H end
  | |- mem_inv _ ?m => match goal with H : mem_inv _ m |- _ => exact H end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_fin := lazymatch goal with |- _ => try apply aevtM_done; lx_post; try lxp_goal end.

(* [comment removed for export] *)
Lemma lxp_ltb1_true_zero : forall r, -18446744073709551616 < r < 18446744073709551616 -> (zlow 64 r <? 1) = true -> r = 0.
Proof.
  intros r Hr K. apply Z.ltb_lt in K. unfold zlow in K. change (2 ^ 64) with 18446744073709551616 in K.
  destruct (Z.eq_dec r 0) as [E|NE]; [exact E|]. exfalso.
  destruct (Z.lt_ge_cases r 0).
  - rewrite <- (Z.mod_unique r 18446744073709551616 (-1) (r + 18446744073709551616)) in K by lia. lia.
  - rewrite Z.mod_small in K by lia. lia.
Qed.
Lemma lxp_ltb1_false_nonzero : forall r, (zlow 64 r <? 1) = false -> r <> 0.
Proof. intros r K ->. discriminate K. Qed.
Lemma lxp_ltb0_false_zero : forall r, -18446744073709551616 < r < 18446744073709551616 -> (0 <? zlow 64 r) = false -> r = 0.
Proof.
  intros r Hr K. apply lxp_ltb1_true_zero; [exact Hr|]. apply Z.ltb_ge in K. apply Z.ltb_lt.
  pose proof (Z.mod_pos_bound r 18446744073709551616 ltac:(lia)) as B. unfold zlow in *. change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.
Lemma lxp_ltb0_true_nonzero : forall r, (0 <? zlow 64 r) = true -> r <> 0.
Proof. intros r K ->. discriminate K. Qed.

(* [comment removed for export] *)
Lemma lxp_lxor_bound : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Pa,$4.Pb,$4.P,(15.(25.=R2.)(24.R2.+10000000000000000.))P,(15.(25.=R2.)(24.R2.+10000000000000000.))(15.(25.=(28.R4.R3.))(24.(28.R4.R3.)+10000000000000000.))")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb. pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)) as H0.
  split; [exact H0|]. change 18446744073709551616 with (2 ^ 64) in *.
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NE]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HL.
  assert (Z.log2 a < 64) by (destruct (Z.eq_dec a 0) as [-> |]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < 64) by (destruct (Z.eq_dec b 0) as [-> |]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  lia.
Qed.
Lemma lxp_xorb_true_eq : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Pa,$4.Pb,$4.P,(15.(25.=R2.)(24.R2.+10000000000000000.))P,(15.(25.=R2.)(24.R2.+10000000000000000.))P,(6.$29.(2:.(27.+40.(28.R4.R3.))+1.)$2;.)(6.$4.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros a b Ha Hb K. apply Z.ltb_lt in K. unfold zlow in K. change (2 ^ 64) with 18446744073709551616 in K.
  rewrite Z.mod_small in K by (apply lxp_lxor_bound; assumption). apply lxor_small_eq; lia.
Qed.
Lemma lxp_xorb_false_ne : forall a b, (zlow 64 (Z.lxor a b) <? 1) = false -> a <> b.
Proof. intros a b K ->. rewrite Z.lxor_nilpotent in K. discriminate K. Qed.
(* [comment removed for export] *)
Lemma lxp_eqb0_true_zero : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Pr,$4.P,(15.(24.-10000000000000000.R1.)(24.R1.+10000000000000000.))P,(6.$29.(2<.(27.+40.R2.)(27.+40.=))$2;.)(6.$4.R3.=)")
(* [comment removed for export] *).
Proof.
  intros r Hr K. apply Z.eqb_eq in K. apply lxp_ltb1_true_zero; [exact Hr|]. apply Z.ltb_lt. rewrite K. unfold zlow.
  rewrite Z.mod_0_l by lia. lia.
Qed.
Lemma lxp_eqb0_false_nonzero : forall r, (zlow 64 r =? zlow 64 0) = false -> r <> 0.
Proof. intros r K ->. rewrite Z.eqb_refl in K. discriminate K. Qed.

Ltac lxp_sel_fact K :=
  lazymatch type of K with
  | (zlow 64 (Z.lxor ?a ?b) <? 1) = true => let E := fresh "XEQ" in
      assert (E : a = b) by (apply lxp_xorb_true_eq; [clear K; lxp_lia | clear K; lxp_lia | exact K])
  | (zlow 64 (Z.lxor ?a ?b) <? 1) = false => let E := fresh "XNE" in pose proof (lxp_xorb_false_ne a b K) as E
  | (zlow 64 ?r =? zlow 64 0) = true => is_var r; let E := fresh "R0" in
      assert (E : r = 0) by (apply lxp_eqb0_true_zero; [lxp_arith_ctx; prune_disj; lia | exact K])
  | (zlow 64 ?r =? zlow 64 0) = false => is_var r; let E := fresh "RNZ" in pose proof (lxp_eqb0_false_nonzero r K) as E
  | (zlow 64 ?r <? 1) = true => is_var r; let E := fresh "R0" in
      assert (E : r = 0) by (apply lxp_ltb1_true_zero; [lxp_arith_ctx; prune_disj; lia | exact K])
  | (zlow 64 ?r <? 1) = false => is_var r; let E := fresh "RNZ" in pose proof (lxp_ltb1_false_nonzero r K) as E
  | (0 <? zlow 64 ?r) = false => is_var r; let E := fresh "R0" in
      assert (E : r = 0) by (apply lxp_ltb0_false_zero; [lxp_arith_ctx; prune_disj; lia | exact K])
  | (0 <? zlow 64 ?r) = true => is_var r; let E := fresh "RNZ" in pose proof (lxp_ltb0_true_nonzero r K) as E
  end.

(* [comment removed for export] *)
Ltac lxp_simp_sel :=
  change (Z.b2z true) with 1; change (Z.b2z false) with 0;
  repeat match goal with |- context [Z.add ?a ?b] =>
    is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v end;
  repeat match goal with |- context [Z.mul ?a ?b] =>
    is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v end;
  rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.land_m1_l, ?Z.land_m1_r, ?Z.lor_0_l, ?Z.lor_0_r.

Ltac lxp_selects :=
  repeat match goal with |- _ (MS ?R _ _ _ _ _ _) =>
    match R with context [Z.b2z ?c] =>
      lazymatch c with true => fail | false => fail | _ =>
        let K := fresh "KS" in destruct c eqn:K; lxp_simp_sel; try lxp_sel_fact K end end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_sel_count R n :=
  match R with
  | context C [Z.b2z ?c] =>
      lazymatch c with true => fail | false => fail | _ =>
        lazymatch n with O => fail 1 | S ?n' => let R' := context C [Z.b2z true] in lxp_sel_count R' n' end end
  | _ => idtac
  end.
Ltac lxp_few_selects n := lazymatch goal with |- _ (MS ?R _ _ _ _ _ _) => lxp_sel_count R n end.

(* [comment removed for export] *)
Ltac lxp_arith_evar :=
  lazymatch goal with |- ?T => lxp_arith T; has_evar T; eassumption end.
(* [comment removed for export] *)
Ltac lxp_evar_refl :=
  lazymatch goal with
  | |- ?a = ?k => first [ is_evar k; tryif has_evar a then fail else reflexivity
                        | is_evar a; tryif has_evar k then fail else reflexivity ]
  end.
(* [comment removed for export] *)
Ltac lxp_opaque_hyp :=
  lazymatch goal with |- ?G =>
    let h := head_of G in
    lazymatch h with
    | rw_cells => fail | ro_cells => fail | bytes_at => fail | stk => fail | munch => fail | wmono => fail
    | mem_inv => fail | u8arr => fail | Z.le => fail | Z.lt => fail | @eq => fail | or => fail | and => fail | not => fail
    | _ => match goal with H : ?T |- _ => let h' := head_of T in constr_eq h h'; exact H end
    end
  end.
Ltac lxp_in_list := lazymatch goal with |- In _ _ => cbn; repeat (first [ left; reflexivity | right ]) end.
(* [comment removed for export] *)
Ltac lxp_misc :=
  lazymatch goal with
  | |- In _ _ => lxp_in_list
  | |- _ \/ _ => first [ left; reflexivity | right; reflexivity | lxp_lia | left; lxp_lia | right; lxp_lia ]
  end.
(* [comment removed for export] *)
Ltac lxp_apply_extra := fail.
(* [comment removed for export] *)
Ltac lxp_apply_post := try assumption; try lxp_evar_refl; try lxp_opaque_hyp; try lxp_goal_shape; try lxp_arith_evar; try lxp_misc; try lxp_lia;
  try lazymatch goal with |- word => exact (Z_to_bv 64 0) | |- bv _ => exact (Z_to_bv _ 0) | |- Z => exact 0 end;
  (* [comment removed for export] *)
  try (lazymatch goal with |- ?a = ?b => tryif has_evar a then fail else (tryif has_evar b then fail else solve [ cbn; reflexivity ]) end);
  try lxp_apply_extra.
(* [comment removed for export] *)
Ltac lxp_apply_core L := eapply L; lxp_apply_post; lxp_apply_post.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_lia_fast :=
  lxp_noevar_goal; lxp_arith_ctx; lxp_bool_hyps;
  repeat match goal with H : context [Z.b2z _] |- _ => clear H | H : context [Z.land _ _] |- _ => clear H end;
  rewrite ?lx_bvu64; timeout 5 lia.   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
Ltac lxp_open_impl :=
  repeat match goal with H : @eq Z ?x ?c -> _ |- _ =>
    let E := fresh "E" in
    assert (E : x = c) by (clear H; first [ lxp_lia_fast
                                        | (* [comment removed for export] *)
                                          lazymatch goal with Hz : 0 <= - zlow 64 x |- _ =>
                                            apply lxp_zlow64_nonpos_zero; [ clear Hz; lxp_lia_fast | exact Hz ] end ]);
    specialize (H E); clear E;
    first [ progress (decompose [ex and] H); clear H | idtac ] end;
  (* [comment removed for export] *)
  repeat match goal with E : ?w = Z_to_bv 64 _ |- ?G =>
    is_var w; tryif lxp_is_protected E then fail else (tryif lxp_is_protected w then fail else
    (* [comment removed for export] *)
    lazymatch G with context [w] => fail | _ => subst w end) end.

(* [comment removed for export] *)
Ltac lxp_lits_signed :=
  repeat match goal with |- context [Z_to_bv 64 ?k] =>
    lxp_zlit_shape k;
    lazymatch eval vm_compute in (Z.leb 9223372036854775808 k) with
    | true => let k' := eval vm_compute in (k - 18446744073709551616) in
              replace (Z_to_bv 64 k) with (Z_to_bv 64 k') by (apply bv_eq; vm_compute; reflexivity)
    end end.
Ltac lxp_apply L :=
  try lxp_open_impl;
  first [ solve [ lxp_apply_core L ]
        | lxp_few_selects 4%nat; progress lxp_selects; try lxp_open_impl; solve [ lxp_apply_core L ]
        | progress lxp_lits_signed; lxp_few_selects 4%nat; try lxp_selects; try lxp_open_impl; solve [ lxp_apply_core L ]
        | lxp_few_selects 4%nat; progress lxp_selects; try lxp_open_impl; lxp_apply_core L
        | lxp_apply_core L ].


(* [comment removed for export] *)
Ltac lxp_default :=
  lazymatch goal with
  | |- Z => exact 0 | |- nat => exact 0%nat | |- N => exact 0%N | |- positive => exact 1%positive | |- bool => exact false
  | |- bv ?n => exact (Z_to_bv n 0) | |- list ?A => exact (@nil A) | |- option ?A => exact (@None A)
  | |- (?A * ?B)%type => split; lxp_default
  end.

(* [comment removed for export] *)
Ltac lxp_dead := exfalso; lxp_selects; lxp_lia.

(* [comment removed for export] *)
Ltac lxp_at pc :=
  lazymatch goal with |- _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => constr_eq p pc end.

(* [comment removed for export] *)
Ltac lxp_pre_ret := idtac.

(* [comment removed for export] *)
Ltac lxp_ret_post := idtac.
(* [comment removed for export] *)
Ltac lxp_ret := lazymatch goal with |- _ => lxp_pre_ret; lxp_selects; lxp_statics; lxp_fin; lxp_ret_post; lxp_ret_post end.

(* [comment removed for export] *)
#[export] Ltac finish ::=
  first [ apply evt_done | apply aevtM_done ];
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf; lx_exs; lx_ands; [> reflexivity | ..];
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac lxp_ret_err := lxp_ret.

(* [comment removed for export] *)
Lemma zlow64_nonpos_zero : forall r, -18446744073709551616 < r < 18446744073709551616 -> 0 <= - zlow 64 r -> r = 0.
Proof.
  intros r Hr Hz. unfold zlow in Hz. change (2 ^ 64) with 18446744073709551616 in Hz.
  destruct (Z.eq_dec r 0) as [E|NE]; [exact E|].
  destruct (Z.lt_ge_cases r 0).
  - rewrite <- (Z.mod_unique r 18446744073709551616 (-1) (r + 18446744073709551616)) in Hz by lia. lia.
  - rewrite Z.mod_small in Hz by lia. lia.
Qed.
Ltac lxp_r0 r :=
  let E := fresh "R0" in
  first [ lazymatch goal with Hz : 0 <= - zlow 64 r |- _ =>
            assert (E : r = 0) by (apply zlow64_nonpos_zero; [lxp_arith_ctx; prune_disj; lia | exact Hz]) end
        | (* [comment removed for export] *)
          assert (E : r = 0) by (lxp_arith_ctx; prune_disj; lia) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_post_pure :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in destruct PO as [E PO]; subst ms'; try destruct_ands PO;
  try (lazymatch goal with
       | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).
Tactic Notation "lxp_callp" tactic3(apptac) :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ _ _) => eapply evt_cut; [ apptac | lxp_post_pure ]
  | |- aevtM _ _ _ (MS _ _ _ _ _ _ _) => eapply aevtM_cut_evt; [ eassumption | apptac | lxp_post_pure ]
  end.
Ltac lxp_bcmp_probe SPB ROx :=
  lxp_callp (eapply SPB; rewrite ?unsigned_lit by (clear_disj; lia);
             [ exact ROx | lxp_side | reflexivity | clear_disj; lia ]; lxp_side).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lxp_land_127_range : forall x, 0 <= Z.land (Z.land x 255) 127 <= 127.
Proof.
  intros x. split. apply Z.land_nonneg; right; lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. rewrite Z.ones_equiv.
  pose proof (Z.mod_pos_bound (Z.land x 255) (2^7) ltac:(lia)) as H. change (2^7) with 128 in *. cbn. lia.
Qed.
Lemma lxp_longform_n : ltac2:(CDefT.buildp (gd_tbl_LxPTac ()) "Pnn,$4.P,(15.(25.=R1.)(25.R1.+7?.))P,(25.+???????????????<.(2=.(7.R2.-5.)+10000000000000000.))(15.(25.+1.R3.)(25.R3.+4.))")
(* [comment removed for export] *).
Proof.
  intros nn NR Kn.
  destruct (Z_lt_le_dec nn 5) as [Hl|Hl]; [| rewrite Z.mod_small in Kn by lia; lia].
  destruct (Z_le_gt_dec nn 0) as [Hz|Hz]; [| ].
  - exfalso. assert (E0 : nn = 0) by lia. subst nn. vm_compute in Kn. exact (Kn eq_refl).
  - replace ((nn + -5) mod 18446744073709551616) with (nn + -5 + 18446744073709551616) in Kn; [lia|].
    rewrite <- (Z.mod_small (nn + -5 + 18446744073709551616) 18446744073709551616) by lia.
    rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma lxp_sext_nm1 : forall n, 1 <= n <= 2147483648 ->
  Z.shiftr (zlow 64 (4294967296 * n + -4294967296)) 32 = n - 1.
Proof.
  intros n Hn. unfold zlow. change (2 ^ 64) with 18446744073709551616. rewrite Z.mod_small by lia.
  replace (4294967296 * n + -4294967296) with ((n - 1) * 2 ^ 32) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac lxp_longform nn :=
  match goal with H : context [zlow 64 (Z.land (Z.land ?v 255) 127 + -5)] |- _ =>
    let NR := fresh "NR" in let HN := fresh "HN" in
    pose proof (lxp_land_127_range v) as NR; set (nn := Z.land (Z.land v 255) 127) in *;
    unfold zlow in H; change (2 ^ 64) with 18446744073709551616 in H;
    pose proof (lxp_longform_n nn NR ltac:(clear -H NR; lia)) as HN; clearbody nn;
    rewrite ?(lxp_sext_nm1 nn) by (clear -HN; lia)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxp_intro_rest PO :=
  lazymatch goal with
  | |- forall _ : ?A, _ =>
      lazymatch goal with
      | |- _ -> _ -> _ => let H := fresh "PC" in intro H; lxp_intro_rest PO
      | |- _ -> _ => intros PO
      end
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac lxp_addr_norm e :=
  lazymatch e with
  | ?a + ?c =>
      lazymatch c with
      | Z0 => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 + c) in constr:((u, v)) end
      | Zpos _ => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 + c) in constr:((u, v)) end
      | Zneg _ => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 + c) in constr:((u, v)) end
      | _ => constr:((e, 0))
      end
  | ?a - ?c =>
      lazymatch c with
      | Z0 => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 - c) in constr:((u, v)) end
      | Zpos _ => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 - c) in constr:((u, v)) end
      | Zneg _ => lazymatch lxp_addr_norm a with (?u, ?c0) => let v := eval cbv in (c0 - c) in constr:((u, v)) end
      | _ => constr:((e, 0))
      end
  | _ => constr:((e, 0))
  end.

(* [comment removed for export] *)
Ltac lxp_precut_ivs m W :=
  lazymatch W with
  | nil => idtac
  | (?lo, ?hi) :: ?W' =>
      lazymatch lxp_addr_norm lo with (?u, ?clo) =>
        lazymatch lxp_addr_norm hi with (?u', ?chi) =>
          tryif constr_eq u u' then (try lxp_cut_mem m u clo; try lxp_cut_mem m u chi) else idtac
        end
      end;
      lxp_precut_ivs m W'
  | _ => idtac
  end.

#[export] Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  lxp_dex PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  lxp_dand PO; intros E MUc WMc; try intros MIc; lxp_intro_rest PO;
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      lxp_precut_ivs m W;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ])
  end).
