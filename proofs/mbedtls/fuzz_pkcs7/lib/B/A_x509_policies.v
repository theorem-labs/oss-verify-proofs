(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_seq_stmtsE_w A_x509_get_san_A A_asn1_trav A_x509_policies_A A_x509_policies_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_x509_policies () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.SEQ_SIZE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.SSEQ"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Walk.Call.Body.nodeF"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_trav.seqrep"; "Walk.Call.Body.curP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.removelast"; "Stdlib.Lists.List.last"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Walk.Call.Body.pinvx"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.seq_parser_postE"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.PHIpol"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.FFRpol"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_B.CNTpol"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Walk.Call.Body.LoopOblig"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Lists.ListDef.repeat"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_A.A_X509_POLICIES"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.seq_parser_stmtE"; "RocqVerifyHarness.AgentSubmission.B.A_x509_policies_A.STKpol"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.B.A_crt_parse_stmts.LFMAX_CRT"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmts.seq_parser_stmtA"].

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29782099606.1000001S".
Lemma pz_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac pz_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac pz_lia := pz_clear; lia.
Local Ltac pz_hyp E :=
  unfold c_ltu, c_lts, c_eq, bv_eqb, bv_ltu, bv_lts, bv_leu in E; cbn [negb] in E;
  repeat match type of E with
         | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in E by pz_lia
         | context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) in E by pz_lia
         end;
  first [ apply Z.ltb_lt in E | apply Z.ltb_ge in E | apply Z.eqb_eq in E | apply Z.eqb_neq in E
        | apply Z.leb_le in E | apply Z.leb_gt in E | idtac ].
Local Ltac pz_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; pz_lia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; pz_lia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; pz_lia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; pz_lia) ]
  | |- context [Z.eqb ?a ?b] =>
      first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; pz_lia)
            | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; pz_lia) ]
  end.
Local Ltac pz_base :=
  first [ reflexivity
        | apply Z.ltb_lt; pz_lia | apply Z.ltb_ge; pz_lia | apply Z.leb_le; pz_lia | apply Z.leb_gt; pz_lia
        | apply Z.eqb_eq; pz_lia | apply Z.eqb_neq; pz_lia ].
Local Ltac pz_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); pz_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); pz_rec
  | _ => pz_base
  end.
Local Ltac pz_lits :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by pz_lia
  | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) by pz_lia
  end.
Local Ltac pz_split :=
  repeat match goal with
  | |- context [if ?b then _ else _] => let E := fresh "EB" in destruct b eqn:E; cbv iota; pz_hyp E
  end.
Local Ltac pz_solve :=
  rewrite ?pz_land7;
  first [ reflexivity
        | unfold_cond; fold_lit_ux; rewrite ?pz_land7; pz_lits; pz_dec; pz_rec
        | unfold v_sltu, v_slt, v_xor, c_ltu, c_lts, c_eq; unfold_cond; pz_split; cbn [negb]; fold_lit_ux; rewrite ?pz_land7; pz_lits; pz_dec;
          first [ reflexivity | pz_rec | exfalso; pz_lia ] ].
Local Ltac pz_if :=
  match goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xabec8 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; pz_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xabec8) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; pz_solve]
  end.
Local Ltac pz_pre := repeat pz_if.
Local Ltac pz_br :=
  match goal with
  | |- _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv_concl_iota | symmetry; pz_solve]
            | replace c with false; [cbv_concl_iota | symmetry; pz_solve] ]
  end.
Local Ltac cb8_at H i :=
  lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.
Local Ltac zstep ::= pz_pre; step; zsimp; pz_pre.
Local Ltac zto L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0G.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis OIDH : oid_rt_hyps R HIA.

  Local Notation STKpol := (A_x509_policies_A.STKpol R).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CUR P END BUF lo slo : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKpol.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold A_x509_policies_A.STKpol in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].


  Variable mo0 : Model.
  Variable d : Z.
  Hypothesis NDL : List.NoDup (map fst LB).

  Local Notation PHIpol := A_x509_policies_B.PHIpol.
  Local Notation FFRpol := A_x509_policies_B.FFRpol.
  Local Notation CNTpol := A_x509_policies_B.CNTpol.
  Local Notation POST := (seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r => r = 0 \/ r = -8320) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF (END - P) lo slo d m mo0).
  Local Notation nLB nodes := (SSEQ (rev nodes) ++ LB).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis BUDF : hfr asegs R HIA h + FFRpol (END - P) d <= FR_MAX.
  Hypothesis BUDV : havol asegs R HIA h <= AVOL_MAX.

  Section Body.
  Variables (FB sp1 : Z).
  Hypothesis SP1 : bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 64.
  Hypothesis CFB : crange CS FB 64.
  Hypothesis APP : FB + 64 <= PP \/ PP + 8 <= FB.
  Hypothesis APC : FB + 64 <= CUR \/ CUR + 32 <= FB.
  Local Notation LF' := ((FB, 64) :: LF).
  Local Notation WMU cur := [(PP, PP + 8); (cur%Z, (cur + 32)%Z); (FB, FB + 64); (lo, bv_unsigned sp)].
  Local Notation K24 := (Z_to_bv 64 18446744073709542038).
  Local Notation K32 := (Z_to_bv 64 18446744073709542144).
  Local Notation K40 := (Z_to_bv 64 18446744073709542042).
  Local Notation K48 := (Z_to_bv 64 156864).
  Local Notation K56 := (Z_to_bv 64 18446744073709543296).

  #[using="Type"] Lemma nLB_in : forall nodes x, In x nodes -> In (x, 32) (nLB nodes).
  Proof. intros nodes x Hx. apply in_or_app. left. unfold SSEQ. apply (in_map (fun a => (a, SEQ_SIZE))). apply -> in_rev. exact Hx. Qed.
  #[using="Type"] Lemma nLB_snoc : forall nodes N, nLB (nodes ++ [N]) = (N, 32) :: nLB nodes.
  Proof. intros nodes N. unfold SSEQ. rewrite rev_app_distr. reflexivity. Qed.

  Definition nodeF (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(0.(1.=O1.)(0.(2.$3.(4.O1.+10.)=)(0.(5.(6.O1.+20.)Vlo,)(0.(7.(5.(6.VPP,+8.)O1.)(5.(6.O1.+20.)VPP,))(0.(7.(5.(6.VCUR,+20.)O1.)(5.(6.O1.+20.)VCUR,))(0.(7.(5.(6.VFB,+40.)O1.)(5.(6.O1.+20.)VFB,))(0.PB,$3.Pk,$3.P,(8.(9.$3.$3.)(:.$3.$3.R2.R1.)VLB,)(7.(5.(6.O1.$;.)R3.)(5.(6.R3.R2.)O1.))(<.VR,VLB,VLF,O1.+20.))))))))")
(* [comment removed for export] *).
  Definition curP (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(0.(1.=O1.)(0.(2.$3.(4.O1.+8.)=)(0.(5.(6.O1.+20.)Vlo,)(0.(7.(5.(6.VPP,+8.)O1.)(5.(6.O1.+20.)VPP,))(0.(7.(5.(6.O1.+20.)VBUF,)(5.(6.VBUF,(=.(>.(?.&8.)Vbs,)))O1.))(0.(7.(5.(6.VFB,+40.)O1.)(5.(6.O1.+20.)VFB,))(0.(10.(11.VR,)(12.$13.(12.$13.(14.(15.$3.O2.))VLB,)(16.(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)))Vlo,(18.$19.VR,VHIA,Vh,)O1.+20.)(7.(2.$3.O1.VCUR,)(8.$3.O1.O2.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L38383890888.1 L44052539574.1 L64638104799.4 L66151427842.1600000500:00J00eS3curS3curS3BUF2bs3cur3NLBS3cur2r03N161q1r1H2H02q02H4". (* [comment removed for export] *)
  #[using="BIN ALC CUR0 CWC CURLO DCB D1 APC"] Lemma curP_of : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pm',P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.P,Px,$3.P,(8.$3.R1.R3.)(1<.R2.)P,(1=.$19.R4.(12.$13.(14.(15.$3.R3.))VLB,)VBUF,VEND,VCUR,R3.R2.)(1>.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m' nodes cur HF HS. destruct nodes as [|a r].
    - cbn in HS. subst cur. unfold curP. spine; first [assumption | left; reflexivity | idtac].
      eapply client_wrange_mono; [exact CWC|]. intros b Hb. apply fdata_cons_sub. exact Hb.
    - ddestruct HS as (E & HI & H16 & H0 & _).
      assert (Hne : a :: r <> []) by discriminate.
      pose proof (last_in (a :: r) Hne) as HIN. rewrite <- E in HIN.
      ddestruct (HF cur HIN) as (N0 & N16 & NLO & NPP & NCUR & NFB & NLB & _).
      unfold curP. spine; try assumption.
      + clear - N16. Z.div_mod_to_equations. lia.
      + specialize (NLB _ _ BIN). unfold SEQ_SIZE in NLB. clear - NLB. lia.
      + eapply client_wrange_block; [apply in_or_app; left; exact HI| clear; lia| clear; lia].
      + right. exact HIN.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pinvx (Lx : list blk) (mm : mem) (hc : HST asegs R HIA) (nodes : list Z) (cur : Z) (nt npad : word) (cl cp : Z)
                  (w0 w1 w2 lenw k64 : word) (ja jb : list byte) : Prop := 
    ((@HM asegs R HIA hc (Lx ++ ((@SSEQ (rev nodes)) ++ LB)) ((FB, 64) :: LF) mm) /\
    (forall x : Z,
    (@hcs asegs R HIA h x) ->
    (@hcs asegs R HIA hc x)) /\
    ((@htop asegs R HIA hc) = (@htop asegs R HIA h)) /\
    ((@hstkhi asegs R HIA hc) = (@hstkhi asegs R HIA h)) /\
    ((@hflag asegs R HIA hc) = (@hflag asegs R HIA h)) /\
    ((@havol asegs R HIA hc) <= (@havol asegs R HIA h)) /\
    (List.NoDup nodes) /\
    (forall x : Z,
    (In x nodes) ->
    (@nodeF x)) /\
    (@seqrep asegs mm ((@SSEQ (rev nodes)) ++ LB) BUF END CUR nodes cur) /\
    (@rw_cells asegs mm cur (@seq_cells nt npad cl cp 0)) /\
    (((cp = 0) /\ (cl = 0)) \/ ((BUF <= cp) /\ ((0 <= cl) /\ ((cp + cl) <= END)))) /\
    ((k64 = (Z_to_bv 64 0)) \/ (k64 = K56)) /\
    (@rw_cells asegs mm FB [(@C8 w0); (@C8 w1); (@C8 w2)]) /\
    (@rw_cells asegs mm (FB + 32) [(@C8 lenw)]) /\
    (@rw_cells asegs mm ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R))) [(@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 0)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243))]) /\
    (@rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(@C8 s11); (@C8 s10); (@C8 s9); (@C8 s8); (@C8 s7); (@C8 s6); (@C8 s5); (@C8 s4); (@C8 s3); (@C8 s2); (@C8 s1); (@C8 s0); (@C8 ra)]) /\
    (@rw_cells asegs mm sp1 [(@CB 8%nat ja); (@C8 K32); (@C8 K40); (@C8 K48); (@C8 (Z_to_bv 64 FB)); (@C8 k64); (@C8 (Z_to_bv 64 END)); (@C8 (Z_to_bv 64 (@al_sb (@arl_AL R)))); (@CB 16%nat jb); (@C8 (Z_to_bv 64 FB))]) /\
    (@stk asegs mm (sp1 + 88) ((bv_unsigned sp) + (-104))) /\
    (@stk asegs mm lo sp1) /\
    (@mem_inv asegs mm) /\
    (@bytes_at asegs mm BUF bs) /\
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA hc) mm PP 8) /\
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA hc) mm BUF (@Z.of_nat (length bs))) /\
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA hc) mm CUR 32) /\
    (@presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) [(PP, (PP + 8)); (CUR, (CUR + 32))] m mm) /\
    (@sshad asegs (@arl_AL R) mm slo sp1) /\
    (@sshad asegs (@arl_AL R) mm sp1 (bv_unsigned sp)))
(* [comment removed for export] *).

  Local Notation pinv := (pinvx []).

  #[using="Type"] Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PLx,(1;.$13.)Phc,(37.$19.VR,VHIA,)Pmq,P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Py,$3.P,(1?.$19.VR,VHIA,R4.(12.$13.R5.(12.$13.(14.(15.$3.R2.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R3.)P,(24.$3.R3.)P,(38.(2.(1;.$3.)R4.(2:.$3.)))P,(8.$3.R4.(39.$3.R5.))(7.(5.(6.R5.+20.)(3:.$3.R6.=))(5.(6.(3:.$3.R6.=)+20.)R5.))")
(* [comment removed for export] *).
  Proof.
    intros Lx hc mq nodes y HH HND Hne Hy.
    pose proof (in_rl _ _ Hy) as HyN.
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP].
    assert (NE : y <> last nodes 0).
    { intros E. rewrite <- (rl_last_app nodes 0) in HND by exact Hne.
      apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
    eapply (blocks_apart_in2 _ y 32 (last nodes 0) 32); [exact HAP| apply in_or_app; left; apply in_or_app; right; apply nLB_in; exact HyN| apply in_or_app; left; apply in_or_app; right; apply nLB_in; apply last_in; exact Hne| exact NE].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2389586940.10 L36149741099.1000000R019S2sp2PP2lo2FB3cur1A2OA3NLO3NPP3NFBS2sp2PP3CUR2lo5CURLO2D12FB3APC3cur4NCUR". (* [comment removed for export] *)
  #[using="CURLO D1 APC"] Lemma seqrep_mu : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PLx,(1;.$13.)Phc,(37.$19.VR,VHIA,)Pmm,P,(?.&40.)(1:.(?.&8.))Pmm',P,(?.&40.)(1:.(?.&8.))Pnodes,(1;.$3.)Pcur,$3.P,(1=.$19.R4.(12.$13.(14.(15.$3.R2.))VLB,)VBUF,VEND,VCUR,R2.R1.)P,Px,$3.P,(8.$3.R1.R4.)(1<.R2.)P,(1?.$19.VR,VHIA,R7.(12.$13.R8.(12.$13.(14.(15.$3.R4.))VLB,))(17.(9.$3.$3.)(:.$3.$3.VFB,+40.)VLF,)R6.)P,(24.$3.R5.)P,(3;.(17.(9.$3.$3.)(:.$3.$3.VPP,(6.VPP,+8.))(17.(9.$3.$3.)(:.$3.$3.R5.(6.R5.+20.))(17.(9.$3.$3.)(:.$3.$3.VFB,(6.VFB,+40.))(17.(9.$3.$3.)(:.$3.$3.Vlo,(2?.&40.Vsp,))(2:.(9.$3.$3.))))))R8.R7.)P,(3<.$19.R9.R8.)(1=.$19.R9.(12.$13.(14.(15.$3.R8.))VLB,)VBUF,VEND,VCUR,R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros Lx hc mm mm' nodes cur HS HF HH HND MU WM. eapply seqrep_mem; [exact HS| intros b Hb; exact Hb|].
    intros A cs HA HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. cbn [disjoint_from].
    assert (CURE : nodes <> [] -> cur = last nodes 0 /\ In cur nodes).
    { intros Hne. destruct nodes as [|a0 r0]; [exfalso; exact (Hne eq_refl)|]. destruct HS as (E & _). split; [exact E| rewrite E; apply last_in; exact Hne]. }
    destruct HA as [[-> Hne]|HA].
    - destruct (CURE Hne) as [_ CINn]. ddestruct (HF cur CINn) as (_ & _ & _ & _ & NCUR & _).
      clear - D1 APC CURLO NCUR. lia.
    - assert (Hne : nodes <> []) by (intros E; rewrite E in HA; exact HA).
      destruct (CURE Hne) as [CE _]. pose proof (others_apart Lx hc mm nodes A HH HND Hne HA) as OA. rewrite <- CE in OA.
      destruct (HF A (in_rl _ _ HA)) as (_ & _ & NLO & NPP & _ & NFB & _). clear - OA NLO NPP NFB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac open_pinv INV hc :=
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2);
    pose proof (curP_of _ _ _ HNF HSR) as (CU0 & CUA8 & CLO & CPPa & CBUFa & CFBa & CWcur & CIN);
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_x509_policies_A.STKpol in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (cs_ok_sb _ _ CSOKc) as SB64;
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo0) as KINV;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc; rewrite HTc, HSc in HTOPc;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NB1 NEED0; lia);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_mono; [exact HCSc| eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NB1 NEED0 TOP HTOPc; lia]]);
    assert (SCS1c : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS0c : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 64) by (eapply crange_mono; [exact HCSc| exact CFB]);
    pose proof FRSH as (F0 & F1 & F2 & F3);
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia);
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia);
    assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN);
    assert (BUFLO : BUF + n <= lo)
      by (destruct (blocks_below_hm R HIA hc _ _ _ LB HHc ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb) _ BIN) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    assert (WCC : wcover R LB LF (bv_unsigned sp) W CUR 32) by (apply wcover_inside; cbn [inside]; right; left; clear; lia);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ _ =>
      assert (CWPn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) PP 8)
        by (rewrite HTc; eapply client_wrange_mono; [exact CWP| intros b' Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; apply in_or_app; right; exact Hb'| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb']]) end;
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ _ =>
      assert (INHc : In (FB, 24) (Lh ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity);
      assert (INDc : In (FB + 32, 64 - 40) (Lh ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity) end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    unfold seq_cells in HCURC.

  Ltac open_pinv_mu INV hc cur :=
    open_pinv INV hc;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (WMU cur) mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB; pose proof (conj HHx I) as HH0 end end.
  (* [comment removed for export] *)
  Ltac fold_pinv INVn hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb :=
    lazymatch goal with MU : munch _ ?m0 ?mx, WM : wmono _ ?m0 ?mx, SRx : seqrep _ ?m0 _ _ _ _ _ _, NFx : (forall x, In x _ -> nodeF x), HHz : HM _ _ _ hc _ _ ?m0 /\ True, NDx : List.NoDup _ |- _ =>
      let HSR2 := fresh "HSR2" in
      pose proof (seqrep_mu _ hc _ _ _ _ SRx NFx (proj1 HHz) NDx MU WM) as HSR2;
      assert (INVn : pinv mx hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) by (unfold pinvx; spine; first [eassumption | match goal with |- ?g => idtac "FOLD-LEFT:" g end])
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L10719636406.2L34429891072.4L38310959932.6L39268637205.000000600B00X00YS1d2D0S1P3END1e2HES1P3END5nodes1e3HLN2E4S". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO CUR0 CWC CURLO SLOS SLOL SLO TOP SPH UW SP1 SP1M F64 FRSH CFB"] Lemma exit_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall r : Z,
    forall p' : Z,
    forall xra : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s3v : (bv 64),
    forall s4v : (bv 64),
    forall s5v : (bv 64),
    forall s6v : (bv 64),
    forall s8v : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 p'))]) ->
    ((P <= p') /\
    (p' <= END)) ->
    (((-12288) < r) /\
    (r <= 0)) ->
    (((r = 0) \/ (r = (-8320))) ->
    (p' = END)) ->
    (0 <= e) ->
    ((4 * e) <= (END - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 (Z_to_bv 64 FB) s3v s4v s5v s6v (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) s8v s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabdb4) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp' RR HENDx HE0 HE BUDFa HLN.
    assert (E4 : e <= (END - P) / 4) by (apply Z.div_le_lower_bound; [clear; lia| clear - HE; lia]).
    ddestruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2).
    assert (HCBs : (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END)) by (destruct HCB as [(E1 & E2)|K]; [left; exact (conj E1 (conj E2 (HNE E1)))| right; exact K]).
    destruct (seqrep_close asegs _ _ _ _ _ _ _ _ _ _ _ HSR HCURC HCBs) as (t & pd & l & p & HHEAD & HCB' & HCH).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    eapply A_x509_policies_B.pol_fin with (hq := hc) (nodes := nodes) (p' := p') (hct := t) (hcpad := pd) (hcl := l) (hcp := p);
      first [ exact HHc | exact HCSc | exact HTc | exact HSc | exact HFc | exact HVc | exact PRES | exact HPP | exact Hp' | exact HHEAD | exact HCB' | exact HCH | exact HND | exact RR | exact HENDx | exact CFB
            | eassumption
            | lazymatch goal with |- cells_size _ = _ => reflexivity end
            | lazymatch goal with
              | |- hfr _ _ _ _ <= _ => unfold A_x509_policies_B.FFRpol; unfold fr_charge in *; rewrite Z.max_r by (clear - D0; lia); clear - BUDFa HE0 E4 D0; nia
              | |- Z.of_nat (length _) <= _ => unfold A_x509_policies_B.CNTpol; clear - HLN E4; lia
              | |- forall x, In x nodes -> _ => intros x Hx; ddestruct (HNF x Hx) as (_ & _ & _ & _ & _ & _ & NLBx & _); exact NLBx
              end
            | match goal with |- ?g => idtac "EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L10946870795.9  L14400462254.191L17708004891.2  L19246787633.2  L20511565144.134L27111942217.1  L31929504131.134L35655538583.11 L36682633318.4  L38235734261.1  L40228640085.0  L51578300575.1  L51907746211.2  L56380991837.10 L60098763854.6  L62367585344.134L66151427842.16 L9080220944.4   L9356559676.16  Q13193667714.204Q48667079970.20400000D00E00L00M01201601X02102?02C02D02I02P02i03303X04204A05405b06YS1R2lo3LOS2FB3ALO2F1FS2rg2RRSS2sp2PP3CUR2bs2FB3sp15nodes3cur2rg2RRS2PPS2sp2PP3CUR2bs2FB3sp15nodes3cur2rgS1R3HIA1h2sp2lo3TOP5HTOPcS3END2rg2p'2RRS2loSS3CURS2rg2RRS1R3BUF2lo2bs3LOS3ALO3BCES1R2lo3LOSS2sp2PP3CUR2bs2FB3sp15nodes3cur2rg2RRS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma err_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall rg : Z,
    forall p' : Z,
    forall xra : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s2v : (bv 64),
    forall s3v : (bv 64),
    forall s4v : (bv 64),
    forall s5v : (bv 64),
    forall s6v : (bv 64),
    forall s8v : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 p'))]) ->
    ((P <= p') /\
    (p' <= END)) ->
    (((-127) < rg) /\
    (rg < 0)) ->
    (0 <= e) ->
    ((4 * e) <= (END - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17 s2v s3v s4v s5v s6v (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) s8v s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabda0) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp' RR HE0 HE BUDFa HLN.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 3 zstep.
    first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RR; lia)
          | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RR; lia))
          | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].
    zstep. zstep.
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    eapply exit_walk with (e := e) (p' := p'); first [ exact INV2 | exact HPP | eassumption | clear - RR; lia | match goal with |- ?g => idtac "ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac open_pinv_cur INV hc cur :=
    open_pinv_mu INV hc cur;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with CINx : cur = CUR \/ In cur _, OCx : aobj _ _ _ mx CUR 32, HHx : HM _ _ _ hc _ _ mx |- _ =>
        assert (OCN : aobj asegs AL (hcs asegs R HIA hc) mx cur 32)
          by (destruct CINx as [CE|CINn]; [rewrite CE; exact OCx| exact (hm_aobj_block asegs R HIA hc _ _ mx cur 32 HHx (in_or_app _ _ _ (or_intror (nLB_in _ _ CINn))))]) end;
      lazymatch goal with CINx : cur = CUR \/ In cur _, NFx : (forall x, In x _ -> nodeF x) |- _ =>
        assert (WCcur : wcover R LB LF (bv_unsigned sp) W cur 32)
          by (destruct CINx as [CE|CINn];
              [ rewrite CE; apply wcover_inside; cbn [inside]; right; left; clear; lia
              | destruct (NFx cur CINn) as (_ & _ & _ & _ & _ & _ & _ & NFRx);
                eapply (wcover_fresh R LB LF _ W cur 32 cur 32 NFRx); [clear; lia| clear; lia| let ALOx := fresh "ALOx" in pose proof (art_lo asegs R HIA) as ALOx; pose proof SLO as SLOx; unfold A_x509_policies_A.STKpol in SLOx; clear - ALOx SLOx LOS NS1 NB1 NEED0; lia] ]) end end.

  (* [comment removed for export] *)
  Definition LoopOblig (p : Z) : Prop := 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 p))]) ->
    (0 <= e) ->
    ((4 * e) <= (p - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) (Z_to_bv 64 END) (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabb90) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0130@D11532395422.202D15964341902.202D29401369980.202D31242237967.202D32827785284.202D57329886304.202D60109196847.202K14662993782.202K44164039966.202K48593550302.202K59713869701.202L10946870795.9  L14647789168.2  L1685717371.0   L22722541083.126L22927780832.185L26071006300.0  L27111942217.1  L31165784101.189L34603895532.0  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L48118080743.12 L48596171480.2  L51578300575.1  L56380991837.10 L56488151316.185L57130527895.2  L59251680703.12 L59454754158.126L59723830915.2  L60098763854.6  L61971934371.2  L62586168108.2  L62619108508.0  L66151427842.16 L9080220944.4   L9356559676.16  L9817099845.189 P57140489617.202P62587740714.202Q1101800120.199 Q11530185118.201Q11532395422.202Q13197863735.199Q26485828151.199Q29399418748.201Q29401369980.202Q33852546743.199Q35038668202.198Q42439443119.202Q42635497239.199Q43414146086.199Q43622973458.200Q48654498455.199Q49746415830.202Q60716042135.199Q62457807837.199Q66314508158.198Q67038978349.202Q68013150533.202Q8699115497.202 Q9077729369.199 Q9092350619.198 00000e00f01[01\01]01^02\03H04604b05N05b05c05d06\08:08;08?0:70:80:Q0:U0:Z0:_0:`0;E0;F0;K0;d0=B0=C0=U0>M0>N0>X0>_0>`0>a0?;0?J0@=0B30C50D?0D[0E?0Ec0FQ0G?0Gc0HG0I50IJ0J90K00L40LR0MI0NF0O=0OR0Og0Q10Qa0Rf0S;0SPS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1FSS2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0SS2PPS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur1p2Hp3CU03SPR4SP1R2F05BUFLOSS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0FS1P3END2bs1p2Hp2KeS2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0FS1R2lo3LOSS3END1pFSS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B22B32B54CUR03SLO3SPH2FB3sp15nodes3cur3CU03SPR4SP1R2F05BUFLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO BIN B1 B2 B3 B5 ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma fin_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall p : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 p))]) ->
    ((P <= p) /\
    (p <= END)) ->
    (0 <= e) ->
    ((4 * e) <= (END - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 (Z_to_bv 64 p) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) (Z_to_bv 64 END) (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) s9v s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabe60) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hp HE0 HE BUDFa HLN.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    do 11 zstep.
    idtac "FIN-STORED".
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Ke; zify_cond Ke.
    - idtac "FIN-OK".
      assert (PE : p = END) by (clear - Ke Hp B1 B2 B3 B5 B47; try kland Ke; rewrite ?Z.mod_small in Ke by lia; lia).
      destruct HK64 as [-> | ->].
      + eapply exit_walk with (e := e) (r := 0) (p' := p); first [ exact INV2 | eassumption | clear; lia | (intros _; exact PE) | match goal with |- ?g => idtac "FIN-LEFT:" g end ].
      + replace (Z_to_bv 64 18446744073709543296) with (Z_to_bv 64 (-8320)) by (apply bv_eq; vm_compute; reflexivity).
        eapply exit_walk with (e := e) (r := -8320) (p' := p); first [ exact INV2 | eassumption | clear; lia | (intros _; exact PE) | match goal with |- ?g => idtac "FIN2-LEFT:" g end ].
    - idtac "FIN-MISMATCH".
      (* [comment removed for export] *)
      do 3 zstep.
      eapply exit_walk with (e := e) (r := -9574) (p' := p); first [ exact INV2 | eassumption | clear; lia | match goal with |- ?g => idtac "FIN3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L10946870795.9  L24341865253.10 L27111942217.1  L34427793940.10 L35655538583.11 L36792362049.191L38235734261.1  L41202929119.191L47571963878.10 L49334199172.10 L51578300575.1  L56380991837.10 L56775170761.191L60098763854.6  L66151427842.16 L9080220944.4   L9356559676.16  Q10649498890.204Q10651748618.203Q13191590741.204Q13733106231.203Q16059191797.204Q17701933584.204Q34390149656.204Q39600066516.204Q45353769141.203Q48669156085.204Q53917669461.204Q61847600945.20400000D00K00O00b01;03503903_03`04804=04V06Z06d07>07M08@08T08h09V09j0:a0;50;60;70;K0<B0=00=jS1R2lo3LOS2FB3ALO2F1S3END1qS2PPS1P3END1e1q3HQE3HEQS1R3HIA1h2sp2lo3TOP5HTOPcS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur2pe3HPE3CU03SPR4SP1R2F05BUFLOS2loS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curSS1P3END1q2p03HP03HQ03HQES3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur1q2p03HP03HQ03HQE3CU03SPR4SP1R2F05BUFLOS1R2lo3LOSS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesFFS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB ALP PP0 CWP PPLO BIN B1 B3 B5 ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma tail_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    (P <= p0) ->
    (p0 < q) ->
    (q <= END) ->
    ((P <= pe) /\
    (pe <= END)) ->
    (0 <= e) ->
    ((4 * e) <= (q - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) (Z_to_bv 64 END) (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabd78) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQE HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof INV as INV0.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    - idtac "TAIL-LOOP".
      eapply (KLOOP q HQ0 HQE) with (e := e); first [ exact INV0 | exact HPP | eassumption | match goal with |- ?g => idtac "TAIL-LOOP-LEFT:" g end ].
    - idtac "TAIL-MISMATCH".
      (* [comment removed for export] *)
      do 4 zstep.
      replace (Z_to_bv 64 18446744073709542042) with (Z_to_bv 64 (-9574)) by (apply bv_eq; vm_compute; reflexivity).
      eapply exit_walk with (e := e) (r := -9574) (p' := q); first [ exact INV0 | exact HPP | eassumption | clear - HP0 HQ0 HQE HE0 HEQ; lia | match goal with |- ?g => idtac "TAIL-EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@C40858145355.233C60410007123.232D10636937134.233D16071854214.233D16901939902.233D2457516971.233 D28498761192.208D28498761192.235D32458870384.233D4451634193.208 D4451634193.235 D46794843979.233D60109196847.208D60109196847.235D60109446735.233D65008160014.233K20981739667.231K2431698795.208 K2431698795.235 K29378133114.233K30993319891.233K3337916572.208 K3337916572.235 K44164039966.208K44164039966.235K49541715106.231K65858155712.232K67298046963.231K9840090748.208 K9840090748.235 L10946870795.9  L11596596447.14 L12865196093.19 L13946884974.156L13946884974.218L14402536676.220L14402536676.3  L1685717371.0   L17967656726.42 L18489062900.25 L19664123645.18 L19698232010.42 L20612195849.133L20859530083.20 L20977711877.2  L21222158738.133L21222558998.156L21654730866.2  L22410214511.14 L22776206793.133L23182876091.2  L23348364344.20 L2419170461.2   L2621559066.1   L27111942217.1  L27830600341.208L27938279177.42 L29391009772.3  L30452454542.133L30507144274.2  L30997223346.3  L3319629563.14  L3323761050.2   L34429531785.19 L3484917920.42  L35030512882.133L35236225328.25 L35655538583.11 L35903316071.25 L36792364629.195L38235734261.1  L39166007313.133L40228640085.0  L40864281267.156L41110154015.25 L41202929119.192L41202929119.219L41251426164.1  L42383166414.156L42488948659.2  L43300347559.156L43305107741.25 L4349745007.20  L43843024033.0  L44168742175.3  L45186664561.3  L46502749028.3  L47870616696.2  L49233373885.2  L49526752708.2  L5021251703.1   L50678314462.3  L50804189104.133L50814821640.191L50816907467.195L51578300575.1  L53119540131.156L53271535775.192L53271535775.219L53483980942.156L53483980942.218L53506586542.218L53517060498.191L54261998223.2  L55195235631.25 L56380991837.10 L56777280798.191L56788144038.133L57387363123.42 L576250137.192  L576250137.219  L58033769229.14 L58046298131.20 L58972524609.3  L59308586248.2  L6008604205.3   L60098763854.6  L6031628760.2   L61594100401.156L61594246709.133L62013518575.42 L62275882349.3  L62417043471.19 L64179129035.1  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L8587938167.156 L881835912.0    L8941784606.156 L8942138010.133 L9080220944.4   L9356559676.16  L9717202392.42  L9748633241.2   L9835808138.2   N26872553873.232N48204456022.232N49450819242.232N60733400192.232O14912726833.232O18988691132.232O20866770946.233O22525005962.232O27557489321.230O30010457231.232O33449646875.231O3493317847.231 O37559489567.233O3821773283.233 O424351700.231  O44938202843.231O49701823576.232O50011839873.231O54119978487.231O55209884805.231O57031441090.231O64474006218.232O7902534110.230 P21647862485.231P23170010975.208P23170010975.235P30511339222.232P42484919333.232P45193435862.230P46492774851.230P47876372191.231P49230739482.232P50671478649.231P54268551240.208P54268551240.235P62260666314.231P66292560634.232P66818508295.233P67064334489.232P9764112383.231 Q10592389669.231Q10592533181.233Q10596742693.208Q10598691865.204Q10636937134.233Q10637080374.231Q10649498890.205Q10649498890.232Q10651748618.204Q11133374175.233Q11657053839.233Q13731015691.231Q13733106231.204Q14695702359.208Q14695702359.235Q16071854214.233Q17027695041.233Q17681074618.233Q17701933584.205Q17701933584.232Q19559239151.208Q21767670690.233Q23219026840.233Q26481632642.204Q27573751300.233Q2803826605.233 Q28496781288.207Q28496781288.234Q28498761192.208Q28498761192.235Q29775981542.233Q32681607669.233Q34377611452.233Q34390149656.205Q34390149656.232Q37216054521.205Q37216054521.232Q39600066516.205Q39600066516.232Q40251356518.208Q42439168719.233Q42439443119.208Q42439443119.235Q43479930840.233Q4451634193.208 Q4451634193.235 Q4453582353.207 Q4453582353.234 Q45317270253.233Q45353769141.204Q45360064137.231Q46794843979.233Q48118064779.233Q49746198710.233Q49746415830.208Q49746415830.235Q50283589684.231Q50294066696.204Q52711570354.233Q56530976407.233Q57828105177.233Q60703459362.204Q61556549392.206Q61556549392.233Q61847600945.205Q61847600945.232Q67038703949.233Q67038978349.208Q67038978349.235Q68013150533.208Q68013150533.235Q8699115497.208 Q8699115497.235 Q8699324297.233 Q9356559674.210 Q9632015376.208 Q9644583048.233 00000400800^02<03R03S04O05K06106m07i08O09T0:Y0;H0;n0<I0=:0=k0?30?O0@B0A50Ag0BY0Cb0D=0EF0F70Fh0G<0GS0H=0JQ0Ll0Lm0M80M90MU0NK0N\0Oc0Q<0QT0QU0QV0QW0QX0Qk0Ql0Qm0RP0RQ0RV0RZ0S@0TI0TJ0TK0TL0TM0T_0T`0UB0VF0Vo0Wo0XH0XW0Zj0Zn0\?0\@0\A0\P0]60]\0]`0_A0_B0`k0a90a[0a\0a]0a^0a_0a`0aa0ab0ac0ad0d00fC0hV0h[0iE0ik0jQ0ln0oR10810^10_11M11f14916E16V17<17b18I19A19M19S19^19h1:01:11:21;O1;P1;[1;\1;]1<71<81<91<:1<;1<<1<=1<>1<?1<N1=A1>R1>S1>T1>n1?P1?j1@c1@d1@e1@f1@g1@h1@i1@j1@k1@l1@m1@n1@o1A01A11A21A31A41A51A61A71B@1CI1D<1Do1Ej1Fe1Gf1Hg1IG1JX1Ki1LI1Le1Mb1N]1OX1Ol1P@1PT1Ph1Q<1QP1Qd1R81RL1R`1Ra1S51SI1SJ1SK1TB1TV1UQ1Ue1V91Vi1Wd1X81Xf1Xg1Y<1Yf1ZP1[:1[d1\@1\A1\B1\C1\D1\_1]:1];1]<1]P1]l1^a1_V1`S1a=1ag1bQ1c;1c<1cP1cd1d81dk1eU1fX1g[1go1hC1hD1hE1i31ij1jG1jd1k^1lX1mO1n_1oo20f21]22h24324e25?25V25mS2PPS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0FS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur4lenw1q2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2q43Lw42HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB3APP5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP3BUF2lo2bs3LFB2FB3sp15nodes4lenw1q2pe3x263APB2x33x273x323x334POSTS2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP2bs3LFB5nodes3cur4lenw1q4CPPa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur2q43Lw44CPPa2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur4lenw1q2pe3x264CFBa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur4lenw1q2pe3x264CPPa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB3APP5nodes2q43Lw42HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1S3END4lenw1q2pe3HQL3HPES1P3END4lenw1q2pe2p03HP03HQ03HPE2LR2q43Hq4S1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HPE2LR3CU03SPR4SP1R2F05BUFLO2q43Hq44Hq4aS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HPE2LR3CU03SPR4SP1R2F05BUFLO2q43Hq44Hq4aFS2rg3RRg2KzSS2PP2bs2FB3sp14lenw1q2pe3HQLS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO3SLO2FB3sp13SP14FBLOS2bs4lenw1q2pe2KqS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp15nodes3cur4lenw1q2p03HP03HQ02LR3CU03SPR4SP1R2F0S3END2pe2q43Lw43HPE4Hq4LFFFFS1P4lenw1e1q3HEQ2LRFFS1P4lenw1e1q2q43Lw43HEQ2LR3LR44Hq4aFS3sp1S2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FFFFS4lenw1q2p03HQ02LRFS1P3END4lenw1e1q2pe3HQL3HPE3HEQ2LRS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S2sp2PP3CUR2bs2FB3sp15nodes3cur4lenw1q2LRS1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO3SLO2FB3sp13SP14FBLO5BUFLOS1R3HIA1h2sp2lo3TOP5HTOPcS3BUF2bs2FB3APBS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS2loS2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp15nodes3cur1q2p03HP03HQ03CU03SPR4SP1R2F0SFS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2FBS2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp15nodes3cur4lenw1q2p03HP03HQ02LR3CU03SPR4SP1R2F02q44Hq4aFS2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp15nodes3cur4lenw1q2p03HP03HQ02LR3CU03SPR4SP1R2F02q43Lw43LR44Hq4aS2PP2bs2FB3APPS4lenw1q2p02q43Lw43HQ02LR3LR44Hq4aSFFFFFFFFS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS3CURS2sp2PP3CUR2bs2FB3sp15nodes3cur2q43Lw43LR4S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HPE2LR3CU03SPR4SP1R2F05BUFLO2q43Lw43LR44Hq4a4Hq4LS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HPE2LR3CU03SPR4SP1R2F05BUFLO2q43Lw43LR44Hq4a4Hq4LS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curFS1R3NS13NB15NEED02sp2lo2bs3SLO2FB3sp13SP14FBLOS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp15nodes3cur4lenw1q2pe2p03HP03HQ03HQL3HPE2LR3CU03SPR4SP1R2F05BUFLOS2PP2bs2FB3sp12F0S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1P3END4lenw1q2pe2p03HP03HQ03HQL3HPE2LRS1P3END4lenw1q2pe2p02q43Lw43HP03HQ03HPE2LR3LR44Hq4a4Hq4LS3BUF2bs3B47S1i2HiS2rg3RRg2KzS1R2lo3LOSS2sp3sp1FFS1R3NS13NB15NEED02sp2PP1P3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP14lenw1q2p03HP03HQ02LR3ALO3ACP2F0FS2rg3RRg2RNFFS2FB2r03F641q1r1H2H02q02H4FFFFFSFFS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02sp2PP3END3BUF2lo2bs3PP02B33SLO3LOS2FB3sp13SP12pe3HPE3ALO3ACP2F0FFS2LF2bs3LFB2FB5nodes3x341CS2LF2sp2bs3LFB3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x341CFFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodes2q43Lw42HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S2LF2PP2lo2bs3LFB4PPLO3sp15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes2q43Lw42HB5Ha_st5Hl_stS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2sp2bs3LFB3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2bs3LFB2FB5nodesFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS2LF2bs3LFB2FB5nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcFS2LF2bs3LFB3sp15nodesS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2sp2bs3LFB3sp13SP15nodesFFFFS2LF2PP2bs3LFB3PP05nodes2HBS2LF2PP2bs3LFB3PP05nodes2HBFFS2LF2bs3LFB2FB5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R2LF2PP3slo2bs3LFB4SLOS5nodes4lenw1q2HB5Ha_st5Hl_stS1R2LF2PP3slo2bs3LFB4SLOS5nodes2q43Lw42HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes4lenw1q2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes2q43Lw42HB5Ha_st5Hl_stFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS1R3HIA1h2LF2sp2PP2bs3LFB3TOP3sp15nodes4lenw1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP2bs3LFB3TOP3sp15nodes2q43Lw45HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodes2HB5Ha_stS2LF2PP2bs3LFB5nodes2HB5Ha_stS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB3SLO3LOS3sp13SP15nodes4lenw1q2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB3SLO3LOS3sp13SP15nodes2q43Lw42HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur4lenw1q2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2q43Lw42HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs3LFB3TOP3sp13SP15nodes4lenw1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs3LFB3TOP3sp13SP15nodes2q43Lw45HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma qual_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s3v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    (P <= p0) ->
    (p0 < q) ->
    ((q + (bv_unsigned lenw)) <= pe) ->
    (pe <= END) ->
    (0 <= e) ->
    ((4 * e) <= (q - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) s3v (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabcf0) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 14 zstep.
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kq; zify_cond Kq.
    { idtac "QUAL-NONE".
      eapply tail_walk with (e := e) (q := bv_unsigned lenw + q) (pe := pe) (p0 := p0);
        first [ exact INV2 | exact KLOOP | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR; lia | match goal with |- ?g => idtac "QUAL-TAIL-LEFT:" g end ]. }
    assert (QL : q + bv_unsigned lenw < pe) by (clear - Kq HP0 HQ0 HQL HPE LR B1 B3 B5 B47; try kland Kq; rewrite ?Z.mod_small in Kq by lia; lia).
    clear Kq.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "QUAL-GT".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := bv_unsigned lenw + q) (END := pe) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 HP0 HQ0 HQL HPE LR QL; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "QGT-LEFT:" g end ]).
    clear SPT OLEN.
    idtac "QUAL-GT-BACK".
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw4 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q4 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q4 <= pe |- _ => rename H into Hq4 end.
    pose proof (bv_unsigned_in_range 64 Lw4) as LR4. unfold bv_modulus in LR4. cbn [Z.pow Z.of_N Pos.pow] in LR4.
    fold_pinv INV3 hc nodes cur nt npad cl cp w0 w1 w2 Lw4 k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "QUAL-GT-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q4);
        first [ exact INV3 | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR Hq4 RRg RN; lia | match goal with |- ?g => idtac "QUAL-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq4a Hq4L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 13 zstep.
    fold_pinv INV4 hc nodes cur nt npad cl cp w0 w1 w2 Lw4 k64 ja jb.
    idtac "QUAL-SKIPPED".
    eapply tail_walk with (e := e) (q := bv_unsigned Lw4 + q4) (pe := pe) (p0 := p0);
      first [ exact INV4 | exact KLOOP | eassumption | clear - HP0 HQ0 HQL HPE HE0 HEQ LR Hq4 Hq4a Hq4L LR4; lia | match goal with |- ?g => idtac "QUAL-TAIL2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D10916531869.213D11532395422.214D15964341902.214D17452743891.213D19889830902.213D23155707565.213D29401369980.213D29401369980.214D31242237967.214D32827785284.214D48729998015.213D57329886304.214D60109196847.213D60109196847.214K14662993782.213K14662993782.214K44164039966.213K44164039966.214K48593550302.213K48593550302.214K59713869701.213K59713869701.214L10946870795.9  L14647789168.2  L1685717371.0   L22722541083.135L22925878376.197L22927780832.194L27111942217.1  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L44903346094.7  L45581944931.197L46512611463.197L48118080743.12 L48596171480.2  L4951167123.197 L51578300575.1  L56380991837.10 L57130527895.2  L59308660947.5  L59454754158.135L59456438371.197L59723830915.2  L60098763854.6  L62586168108.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.213P57140489617.214P62587740714.213P62587740714.214Q10914612381.212Q10916531869.213Q1101800120.211 Q11530185118.213Q11532395422.214Q12773147547.210Q13351507773.209Q26295627581.210Q27554188553.210Q29399418748.212Q29399418748.213Q29401369980.213Q29401369980.214Q30263103398.211Q3056822380.210 Q3067468761.211 Q38370982088.207Q38385314999.210Q38386200654.209Q41564835977.210Q42377995046.211Q42439443119.213Q42439443119.214Q43622973458.211Q43622973458.212Q46411729629.211Q49746415830.213Q49746415830.214Q52480275446.207Q53541741149.210Q59023939651.210Q60795410781.211Q65750499052.210Q65765526873.211Q67038978349.213Q67038978349.214Q68013150533.213Q68013150533.214Q7174379670.210 Q8172711389.210 Q8699115497.213 Q8699115497.214 Q8958231000.207 Q9916536454.210 00000e01c01d01e01f01g02\03Z03[03\03]03^04\05c06O07D08208i09U0:J0;60;k0<?0<@0<A0=90>W0@50@90@R0@V0@[0@`0@a0A>0B\0CB0Cg0Ch0DN0DS0Dl0Dm0EA0F90GW0GX0Gb0Gc0H=0HL0I?0JA0KL0LV0Mi0NM0O10OM0P:0Pg0Q<0QQ0Qb0R70R[0SH0Sl0TY0U]0V20VG0V\0W10WF0W[0X_0YN0ZF0Zd0[B0[W0\T0]Z0]o0^D0^`0_50_J0__0`i0b<0bl0ce0d>0dS0eX0ff0g70gLS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88FFFFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88FFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4oidp4CFBa2HB5Ha_st5Hl_st3k88S2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur4oidp5CBUFa2HB5Ha_st5Hl_st3k88S2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4oidp4CPPa2HB5Ha_st5Hl_st3k88S2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4oidp4CFBa2HB5Ha_st5Hl_st3k88S1R2lo3LOS2FB3ALO2F1FSS2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2PPS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS3END3BUF3k884oidp3HOB3HOE2KRS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS3CURS1R3BUF2lo2bs3LOS3ALO3BCEFS3BUF2B54oidp3HOB2E0S2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0FS1R2lo3LOSFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur4oidp3CLO2HB5Ha_st5Hl_st3k88S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur4oidp3CLO2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodesS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur2HB5Ha_stS2LF2bs3LFB5nodes3cur2HB5Ha_stS2LF2bs3LFB5nodes3curS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur4oidp5HTOPc2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur4oidp2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodes3cur3CU0S2LF2bs3LFB5nodes3curS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur4oidp5HTOPc2HB5Ha_st5Hl_st3k88S2LF2bs3LFB5nodesS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma fill_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall k88 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall oidp : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    (P <= p0) ->
    (p0 < q) ->
    ((q + (bv_unsigned lenw)) <= pe) ->
    (pe <= END) ->
    (BUF <= oidp) ->
    ((oidp + (bv_unsigned k88)) <= END) ->
    (0 <= e) ->
    ((4 * e) <= (q - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) k88 (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) (Z_to_bv 64 oidp) (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabca0) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 k88) as KR. unfold bv_modulus in KR. cbn [Z.pow Z.of_N Pos.pow] in KR.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    do 4 zstep.
    shadow_chk OCN cur 4.
    idtac "FILL-CHK".
    (* [comment removed for export] *)
    do 14 zstep.
    idtac "FILL-STORED".
    rewrite <- (Z_to_bv_bv_unsigned k88) in HCURC at 1.
    clear HCB.
    assert (HCB : (oidp = 0 /\ bv_unsigned k88 = 0) \/ (BUF <= oidp /\ 0 <= bv_unsigned k88 /\ oidp + bv_unsigned k88 <= END)) by (right; clear - HOB HOE KR; lia).
    fold_pinv INV2 hc nodes cur (Z_to_bv 64 6) npad (bv_unsigned k88) oidp w0 w1 w2 lenw k64 ja jb.
    eapply qual_walk with (e := e) (q := q) (pe := pe) (p0 := p0);
      first [ exact INV2 | exact KLOOP | eassumption | (intros E0; exfalso; clear - E0 HOB B5; lia) | match goal with |- ?g => idtac "FILL-QUAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10837002389.2 L10946870795.9 L12654381620.1 L1540877545.3  L19966991388.8 L21367331087.1 L23615739305.3 L24128180555.1 L31023889862.6 L32454903270.1 L37714553091.1 L38383890888.1 L44052539574.1 L45363093875.3 L46541147848.1 L50796875722.11L52045659405.3 L52442115986.7 L52992257876.1 L55628717916.1 L6203936179.1  L66151427842.16L67038720880.13L6899380056.1  L9631767084.2  00000800L00Q00]01;01?01I01M01c01g01j01o02402=02B02b02n03E03I03L03Q03k04]04a04hS3BUF2bsS1R2lo3LOS2FB3ALO2F1S3BUFS2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP15HTOPcS2FBS1R3HIA2hcS2FBS1R3HIA1h2sp3TOP5HTOPcS2FBS1AS3curS3curS2FB1c2HcS3sp1S1R3NS13NB15NEED02sp2lo3LOS4SLO'S2sp3sp13SP1S1R3HIA1h2hc2h23HVc3HV2S2FBS1AS3sp1S2FB2r03F641q1r1H2H02q02H4S1R3NS13NB15NEED02sp2lo3slo4SLOS4SLOL3sp13SP14SLO'S2FBS2FB2F0". (* [comment removed for export] *)
  #[using="NS1 NB1 NEED0 CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP LOS SP1 F64 FRSH CFB APC"] Lemma pinv_call : 
    (forall Lx' : (@list blk),
    forall hc : (@HST asegs R HIA),
    forall h2 : (@HST asegs R HIA),
    forall mc : ((bv 64) -> (@option (bv 8))),
    forall m2 : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    (@pinvx [] mc hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    (@presA asegs R ((@SSEQ (rev nodes)) ++ LB) ((FB, 64) :: LF) sp1 (@arl_stklo R) (@hstkhi asegs R HIA hc) [] mc m2) ->
    (@mem_inv asegs m2) ->
    (@stk asegs m2 lo sp1) ->
    ((@htop asegs R HIA h2) = (@htop asegs R HIA hc)) ->
    ((@hstkhi asegs R HIA h2) = (@hstkhi asegs R HIA hc)) ->
    ((@hflag asegs R HIA h2) = (@hflag asegs R HIA hc)) ->
    (forall x : Z,
    (@hcs asegs R HIA hc x) ->
    (@hcs asegs R HIA h2 x)) ->
    ((@havol asegs R HIA h2) <= (@havol asegs R HIA hc)) ->
    (@HM asegs R HIA h2 (Lx' ++ ((@SSEQ (rev nodes)) ++ LB)) ((FB, 64) :: LF) m2) ->
    (@pinvx Lx' m2 h2 nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb))
(* [comment removed for export] *).
  Proof.
    intros until jb. intros INV HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2 HH2.
    ddestruct INV as (HHc & HCSc & HTc & HSc & HFc & HVc & HND & HNF & HSR & HCURC & HCB & HK64 & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI & HBUF
                     & OPP & OBUF & OCUR & PRES & SS1 & SS2).
    pose proof (curP_of _ _ _ HNF HSR) as (CU0 & CUA8 & CLO & CPPa & CBUFa & CFBa & CWcur & CIN).
    pose proof (hcs_ok asegs R HIA hc) as CSOKc.
    pose proof (art_lo asegs R HIA) as ALO. pose proof SLO as SLO'. unfold A_x509_policies_A.STKpol in SLO'.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc. rewrite HTc, HSc in HTOPc.
    dpose FRSH as (F0 & F1 & F2 & F3).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (TOPCS : forall x, hcs asegs R HIA hc x -> x < hstkhi asegs R HIA hc) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF')).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (nLB nodes ++ fdata LF') sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    assert (INHc : In (FB, 24) (nLB nodes ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDc : In (FB + 32, 64 - 40) (nLB nodes ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R (nLB nodes) LF' (arl_stklo R) (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    assert (CRcur : client_range L (nLB nodes ++ fdata LF') sp1 cur 32).
    { destruct CIN as [->|CINn]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; apply nLB_in; exact CINn| clear; lia| clear; lia]. }
    unfold pinvx. spine.
    - exact HH2.
    - intros x Hx. apply HCS2. apply HCSc. exact Hx.
    - rewrite HT2. exact HTc.
    - rewrite HS2. exact HSc.
    - rewrite HF2. exact HFc.
    - clear - HV2 HVc. lia.
    - exact HND.
    - exact HNF.
    - eapply seqrep_mem; [exact HSR| intros b Hb; exact Hb|].
      intros A cs HA HR Hsz. eapply (presA_rw_cells asegs R); [exact HP2| exact HR| | exact I]. rewrite Hsz.
      destruct HA as [[-> _]|HA]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; apply nLB_in; exact (in_rl _ _ HA)| clear; lia| clear; lia].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact HCURC| exact CRcur| exact I].
    - exact HCB.
    - exact HK64.
    - eapply (presA_rw_cells asegs R); [exact HP2| exact FHD| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INHc| clear; lia| clear; lia]| exact I].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact HLEN| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INDc| clear; lia| clear; lia]| exact I].
    - eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) (nLB nodes) LF' sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m2 FB _ CSOKc);
        [ cbn [cells_size csize Nat.add]; eapply crange_sub; [eapply crange_mono; [exact HCSc| exact CFB]| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2
        | exact FSH | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact SAVE| apply client_range_stack; clear - SP1; lia| exact I].
    - eapply (presA_rw_cells asegs R); [exact HP2| exact RSL| apply client_range_stack; clear; lia| exact I].
    - eapply (presA_stk asegs R); [exact HP2| exact SThi| clear; lia| exact I].
    - exact ST2.
    - exact MI2.
    - eapply (presA_bytes_at asegs R); [exact HP2| exact HBUF| eapply client_range_block; [apply in_app_iff; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]| exact I].
    - eapply aobj_cs_mono; [exact HCS2|]. eapply (presA_aobj asegs R); [exact CSOKc| exact HP2| exact OPP| apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| exact TOPCS].
    - exact (hm_aobj_block asegs R HIA h2 _ _ m2 BUF n HH2 (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror BIN))))).
    - eapply aobj_cs_mono; [exact HCS2|]. eapply (presA_aobj asegs R); [exact CSOKc| exact HP2| exact OCUR| apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| exact TOPCS].
    - eapply (presW_hmono R HIA hc h2); [| exact HCS2| exact HS2].
      eapply (presW_call asegs R HIA hc LB LF _ _ W m mc m2 (nLB nodes) LF'); [exact PRES| exact HP2| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear - SP1; lia| clear - LOS SLO' NS1 NB1 NEED0; lia| clear; lia| intros x Hx; exact I].
    - eapply (presA_sshad asegs R); [exact HP2| exact SS1| exact SLOS| rewrite HSc; clear - HTOPc TOP SP1; lia].
    - eapply (presA_sshad asegs R); [exact HP2| exact SS2| clear - LOS SLO' SP1 NS1 NB1 NEED0; lia| rewrite HSc; clear - HTOPc TOP; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@D11532395422.202D15964341902.202D29401369980.202D31242237967.202D32827785284.202D57329886304.202D60109196847.202K14662993782.202K44164039966.202K48593550302.202K59713869701.202L10946870795.9  L13059311132.0  L14647789168.2  L1685717371.0   L24338315589.2  L27111942217.1  L35655538583.11 L38235734261.1  L38383890888.1  L44052539574.1  L44166661144.3  L48118080743.12 L48596171480.2  L51578300575.1  L56380991837.10 L57130527895.2  L59723830915.2  L60098763854.6  L62586168108.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.202P62587740714.202Q1101800120.199 Q11530185118.201Q11532395422.202Q13197863735.199Q29399418748.201Q29401369980.202Q35038668202.198Q42439443119.202Q43414146086.199Q43622973458.200Q48654498455.199Q49746415830.202Q62457807837.199Q66314508158.198Q67038978349.202Q68013150533.202Q8699115497.202 Q9077729369.199 Q9092350619.198 00000e00f01[01\01]01^02\03H04604b05N05b05c05d05e05l06006I06M06R06W06X07=07>07C07\07]07^07h07i08C08R09E0:G0;Q0;m0<Q0=50=c0>G0>k0?@0?o0A30AQ0BH0CE0CZ0Co0E90Ei0Fn0GC0GXS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur4CFBa2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1SFSS3END1qS2PPS1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curS3curFS1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS1R3BUF2lo2bs3LOS3ALO3BCEFFS1R2lo3LOSFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLO2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3cur2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 LFB PP0 CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APC"] Lemma null_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s3v : (bv 64),
    forall s9v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    ((P <= q) /\
    (q <= END)) ->
    (0 <= e) ->
    ((4 * e) <= (END - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR (Z_to_bv 64 0xabc84) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FB) s3v (Z_to_bv 64 PP) (Z_to_bv 64 ((@Z.shiftr (cur + 24) 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) s9v s10v (Z_to_bv 64 (cur + 24)) x28 x29 x30 x31) F (Z_to_bv 64 0xabc84) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP Hq HE0 HE BUDFa HLN.
    open_pinv_cur INV hc cur.
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "NULL-EXIT".
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    try replace (Z_to_bv 64 18446744073709542038) with (Z_to_bv 64 (-9578)) by (apply bv_eq; vm_compute; reflexivity).
    eapply exit_walk with (e := e) (r := -9578) (p' := q); first [ exact INV2 | eassumption | clear; lia | match goal with |- ?g => idtac "NULL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@D11532395422.228D15964341902.228D29401369980.228D31242237967.228D32827785284.228D57329886304.228D60109196847.228K14662993782.228K44164039966.228K48593550302.228K59713869701.228K64521742742.228L10946870795.9  L13747222400.3  L14647789168.2  L15756354262.7  L1685717371.0   L19609460064.3  L20838820200.3  L2676165540.3   L27111942217.1  L29765677068.208L34384972077.8  L35655538583.11 L38235734261.1  L38383890888.1  L38692635477.0  L39332637397.0  L40362990079.3  L41991340432.8  L44052539574.1  L44166661144.3  L47348856443.5  L48118080743.12 L48596171480.2  L51578300575.1  L5294437637.3   L56380991837.10 L57130527895.2  L5721395798.8   L59308636045.12 L59314923118.2  L59723830915.2  L60098763854.6  L62586168108.2  L64461871424.3  L64515273836.2  L66151427842.16 L9080220944.4   L9356559676.16  P57140489617.228P62587740714.228Q1101800120.225 Q11530185118.227Q11532395422.228Q24858287367.228Q29399418748.227Q29401369980.228Q35042489430.224Q42439443119.228Q43414146086.225Q43622973458.226Q49746415830.228Q54678164647.228Q62457807837.225Q66309932674.224Q67038978349.228Q68013150533.228Q8699115497.228 Q9077729369.225 Q9079886695.224 00000g00h01_01`01a01b02b03P04@04n05\06H06\06e06f07407507>07F07S07W08f08m09F09J09O09P09Q09]09o0:40:50:D0:i0:j0:o0;70;P0;Q0;[0;e0;j0;k0<50<60<>0<?0<Y0<h0=[0>_0?k0@G0@m0AS0BA0Bg0CM0Cb0DS0E]0F;0G:0H;0HP0He0J;0Jm0L40LI0L^S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur1N4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB5nodes3cur1N5CBUFa2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodes3cur1N4CPPa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodes3cur1N4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N5NCURW2HB5Ha_st5Hl_stS1R2lo3LOS2FB3ALO2F1S3CUR1N1KFS1R2lo3LOS3ALOSS3cur1N1KS2PP1N1KS5nodes1e3HLNS2PPS1R2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur1N3CU03ACV3SPR4SP1R2F03NF03NF1S1e3HE0S1R3HIA1h2sp2lo3TOP5HTOPcS2loS3curSSS3CUR1N4NCURS1P1e1q2p03HQ03HEQS3curFS1R2lo1N3NF12CES1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxFS3CURS2FB1N1KS1R3BUF2lo2bs3LOS3ALO3BCEFS1q2p03HQ0S1N3NF02KnS1N1KFS1R2lo3LOSFS2FB1N1KFS2FB2r03F641q1r1H2H02q02H4S2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO5nodes3cur1N3CLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur1N3CLO2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur3CU02HBS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS1R2LF3slo2bs3LFB4SLOS5nodes3cur1N2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur1N3CU04CUA83SPR4SP1R2F03NF0S2LF2bs3LFB5nodes3cur2HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes3cur1N5HTOPc2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3sp13SP15nodesS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS1R3NS13NB15NEED02LF2sp2lo3slo2bs3LFB4SLOS4SLOL3SLO3sp13SP15nodes3cur1N2HB5Ha_st5Hl_stS2LF2sp2PP2lo2bs3LFB2FB5nodes3cur1N2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes3cur1N5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPH LOS UW SP1 SP1M F64 FRSH CFB APP APC"] Lemma link_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall k88 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall N : Z,
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall oidp : Z,
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [(N, 32)] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    (~ (cp = 0)) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    ((N mod 16) = 0) ->
    (@fresh_apart R ((@SSEQ (rev nodes)) ++ LB) ((FB, 64) :: LF) N 32) ->
    (@rw_cells asegs mm N [(@CB 32%nat (@repeat (bv 8) (Z_to_bv 8 0) 32%nat))]) ->
    (P <= p0) ->
    ((p0 + 4) <= q) ->
    ((q + (bv_unsigned lenw)) <= pe) ->
    (pe <= END) ->
    (BUF <= oidp) ->
    ((oidp + (bv_unsigned k88)) <= END) ->
    (0 <= e) ->
    ((4 * e) <= (p0 - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + ((e + 1) * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR (Z_to_bv 64 0xabc84) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 N) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FB) k88 (Z_to_bv 64 PP) (Z_to_bv 64 ((@Z.shiftr (cur + 24) 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) (Z_to_bv 64 oidp) (Z_to_bv 64 (cur + 24)) x28 x29 x30 x31) F (Z_to_bv 64 0xabc84) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV CPN HPP N16 NFR NZ HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    open_pinv_cur INV hc cur.
    dpose NFR as (NF0 & NF1 & NF2 & NF3).
    assert (HCB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (clear - HCB CPN; destruct HCB as [(E & _)|K]; [exfalso; exact (CPN E)| exact K]).
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (nLB nodes ++ fdata LF')).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
    assert (NFR0 : fresh_apart R LB LF N 32).
    { split; [exact NF0|]. split; [exact NF1|]. split; [exact NF2|]. intros B j Hb. apply NF3. apply SUBq. exact Hb. }
    assert (CE : alloc_ceiling <= lo) by (clear - ALO LOS; lia).
    assert (NPP : PP + 8 <= N \/ N + 32 <= PP).
    { destruct (fresh_apart_client R LB LF lo PP 8 N 32 NFR0 (client_range_of_w L _ _ _ _ _ CWP) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia. }
    assert (NCUR : CUR + 32 <= N \/ N + 32 <= CUR).
    { destruct (fresh_apart_client R LB LF lo CUR 32 N 32 NFR0 (client_range_of_w L _ _ _ _ _ CWC) ltac:(clear; lia) ltac:(clear; lia) CE) as [K|K]; clear - K; lia. }
    assert (NFB : FB + 64 <= N \/ N + 32 <= FB).
    { destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ HAP].
      assert (NE : N <> FB) by (destruct (NF3 FB 24 ltac:(apply in_or_app; right; cbn; left; reflexivity)) as [K|K]; clear - K; lia).
      destruct (blocks_apart_in2 _ N 32 FB 64 HAP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) NE) as [K|K]; clear - K; lia. }
    assert (NCURW : N + 32 <= cur \/ cur + 32 <= N).
    { destruct CIN as [->|CINn]; [clear - NCUR; lia|]. destruct (NF3 cur 32 ltac:(apply in_or_app; left; apply nLB_in; exact CINn)) as [K|K]; clear - K; lia. }
    assert (NNI : ~ In N nodes).
    { intros HI. destruct (NF3 N 32 ltac:(apply in_or_app; left; apply nLB_in; exact HI)) as [K|K]; clear - K; lia. }
    assert (NLO : N + 32 <= lo) by (clear - NF1 CE; lia).
    assert (NFN : nodeF N).
    { unfold nodeF. spine; try assumption. intros B k Hb. unfold SEQ_SIZE. apply NF3. apply in_or_app. left. apply in_or_app. right. exact Hb. }
    (* [comment removed for export] *)
    do 4 zstep.
    idtac "LINK-STORED".
    (* [comment removed for export] *)
    zstep. if_cases Kn; zify_cond Kn.
    { exfalso. clear - Kn NF0 NLO SLO SPH NS1 NB1 NEED0. try kland Kn. rewrite ?Z.mod_small in Kn by lia. lia. }
    clear Kn.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    lazymatch goal with MU : munch _ ?m0 m3, WM : wmono _ ?m0 m3, HHz : HM _ _ _ hc _ _ ?m0 /\ True |- _ =>
      pose proof (seqrep_mu _ hc _ _ _ _ HSR HNF (proj1 HHz) HND MU WM) as SR3 end.
    lazymatch goal with H : rw_cells _ m3 N ?cs |- _ =>
      pose proof (rw_cells_reshape asegs m3 N cs
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H
                    ltac:(cbn; repeat split; reflexivity) ltac:(first [exact eq_refl | vm_compute; reflexivity])) as HNZ end.
    assert (INV3 : pinv m3 hc (nodes ++ [N]) N (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 w0 w1 w2 lenw k64 ja jb).
    { unfold pinvx. rewrite nLB_snoc. spine; first [ eassumption | exact HNZ
        | lazymatch goal with
          | |- _ \/ _ => left; split; reflexivity
          | |- List.NoDup _ => apply NoDup_app; [exact HND| repeat constructor; intros []| intros x Hx [<-|[]]; exact (NNI Hx)]
          | |- forall x, In x (nodes ++ [N]) -> nodeF x => intros x Hx; apply in_app_iff in Hx; destruct Hx as [Hx|[<-|[]]]; [exact (HNF x Hx)| exact NFN]
          | |- seqrep _ _ _ _ _ _ _ _ =>
              eapply seqrep_snoc with (cur := cur) (ct := nt) (cpad := npad) (cl := cl) (cp := cp);
                [ eapply seqrep_mem; [exact SR3| intros b Hb; right; exact Hb| intros A cs _ HR _; exact HR]
                | exact HCURC | exact (proj1 HCB2) | exact (proj1 (proj2 HCB2)) | exact (proj2 (proj2 HCB2)) | left; reflexivity | exact N16 | exact NF0 ]
          end
        | match goal with |- ?g => idtac "LINK-INV-LEFT:" g end ]. }
    idtac "LINK-INV".
    zstep. zstep.
    eapply fill_walk with (e := e + 1) (q := q) (pe := pe) (p0 := p0) (oidp := oidp);
      first [ exact INV3 | exact KLOOP | exact HPP | eassumption | rewrite length_app; cbn [length]; clear - HLN; lia | clear - HP0 HQ0 HE0 HEQ; lia | match goal with |- ?g => idtac "LINK-FILL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0@L10719636406.2  L10946870795.9  L1609905979.6   L19980016842.7  L22728571009.136L22923915520.197L26892418956.1  L27111942217.1  L32879090465.0  L34387002284.15 L34810683834.0  L35655538583.11 L36048514837.5  L38087549238.15 L38235734261.1  L38383890888.1  L38692635477.0  L39220637093.0  L39268637205.0  L44052539574.1  L45569510388.197L46646466118.12 L46646617831.4  L48118080743.12 L49336363269.15 L49603979340.15 L49799904432.3  L51578300575.1  L56380991837.10 L56485944020.199L56658999053.1  L5721395798.8   L58790154276.9  L59444003828.136L60042172946.15 L60098763854.6  L62037211595.12 L62908263739.8  L64700576064.12 L66151427842.16 L66617044166.9  L696052593.2    L9080220944.4   L9356559676.16  Q30263103398.211Q3067468761.211 Q3069291515.210 Q35036100202.212Q41569211166.210Q43414146086.213Q53545853386.210Q60795410781.211Q62457807837.213Q66311996606.212Q9077729369.213 Q9090470235.212 00000600J00_01701o03M03Q03U03V03c03d04=04N05=05A05F05G05H05I05N06l07U07a08F09309d0:00:50:N0;l0<00<:0<W0=O0=\0=f0>S0>e0?E0?o0@M0@U0@d0AW0B[0C00CE0CZ0Co0E30EH0E]0F20FG0F\0G1S1d2D0S1R2lo3LOS2FB3ALO2F1S1R3HIA1h4BUDV2hc3HVcS1R3HIA1h2sp3TOP3sp13SP1S2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2spS2PPSS5nodes1e3HE0SS1R3HIA1h2sp2lo3TOP5HTOPcS1R3HIA2hc2h23HV2S1R3HIA3NS13NB15NEED02sp2PP2lo4PPLO3SLO2hc1a2HaS2loS3curSSSS3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S1P3END4lenw1e1q2pe2p03HQ03HQL3HPE3HEQ2LRS1P3END1e2E1S1R3NS13NB15NEED02sp2lo3LOS4ALOx4SLOxS1P3END5nodes4lenw1q2pe2p03HP03HQ03HQL3HPE2LRS1R3HIA3NS13NB15NEED02sp3CUR2lo5CURLO3SLO2hc1a2HaS2sp3sp13SP1S3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp15nodes3cur3CU03CLO3SPR4SP1R2F0S2spS1q2p03HQ0S1R3NS13NB12sp2lo3SLO3sp13SP1S2sp2PP3CUR2bs3PP02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S5nodes1e3HLNS1R2lo3LOSS1R3NS13NB15NEED02sp2lo3slo4SLOS4SLOL3SLO3SPRS1P1e1q2p03HQ03HEQS3END3BUF2bs2B33B472B52cl2cp3HCBS2FB2r03F641q1r1H2H02q02H42sp3SPA3sp14SP1MS1R3HIA1h1d2hc1e5BUDFa2h24HFR2S2sp3SPRS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp15nodes3cur3CU04CUA83SPR4SP1R2F0S2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3curS2LF2bs3LFB5nodes3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma append_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall k88 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall oidp : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    (P <= p0) ->
    ((p0 + 4) <= q) ->
    ((q + (bv_unsigned lenw)) <= pe) ->
    (pe <= END) ->
    (BUF <= oidp) ->
    ((oidp + (bv_unsigned k88)) <= END) ->
    (0 <= e) ->
    ((4 * e) <= (p0 - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) k88 (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) (Z_to_bv 64 oidp) (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabc30) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HOB HOE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    pose proof INV as INV0.
    open_pinv_cur INV hc cur.
    assert (CPR : 0 <= cp < 2^64) by (clear - HCB B1 B2 B3 B47 B5; lia).
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kp; zify_cond Kp.
    { idtac "APP-INPLACE".
      eapply fill_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := oidp);
        first [ exact INV0 | exact KLOOP | eassumption | clear - HP0 HQ0 HE0 HEQ; lia | match goal with |- ?g => idtac "APP-FILL0-LEFT:" g end ]. }
    assert (CPN : cp <> 0) by (clear - Kp CPR; intros E; apply Kp; rewrite E; reflexivity).
    assert (HCB2 : BUF <= cp /\ 0 <= cl /\ cp + cl <= END) by (clear - HCB CPN; destruct HCB as [(E & _)|K]; [exfalso; exact (CPN E)| exact K]).
    clear Kp.
    (* [comment removed for export] *)
    do 11 zstep.
    idtac "APP-CALLOC".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    fold_pinv INVc hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | clear - SPR; lia| rewrite HSc; apply hstkhi_le64; clear - LOS SLO SPR NS1 NB1 NEED0; lia].
        intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO CURLO SLO NS1 NB1 NEED0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    assert (E1 : 4 * (e + 1) <= END - P) by (clear - HEQ HQ0 HQL HPE LR; lia).
    assert (E4 : e + 1 <= (END - P) / 4) by (apply Z.div_le_lower_bound; [clear; lia| clear - E1; lia]).
    (* [comment removed for export] *)
    zstep.
    replace (Z_to_bv 64 431236 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := hc) (LB := nLB nodes) (LF := LF') (cnt := 1) (sz := 32) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHc | exact HK1 | exact LOS | exact TPV | exact UW1 | exact STlo | exact MI | reflexivity
              | lazymatch goal with
                | |- lo <= sp1 - arl_need_malloc R => clear - SLO SP1 NS1 NB1 NEED0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 <= 1 => clear; lia
                | |- 0 <= 32 => clear; lia
                | |- 1 * 32 < AMAX => unfold AMAX; clear; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => rewrite (vchg_small (1 * 32)) by (unfold AMAX_SEC; clear; lia); clear - BUDV HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold A_x509_policies_B.FFRpol in BUDF; unfold fr_charge in *; rewrite Z.max_r in BUDF by (clear - D0; lia); clear - BUDF BUDFa HE0 E4 D0; nia
                end
              | c24_lit   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & r & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xabc84)) with (Z_to_bv 64 0xabc84 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (vchg_small (1 * 32)) in HV2 by (unfold AMAX_SEC; clear; lia). rewrite ?Z.mul_1_l in CASES.
    idtac "CALLOC-POST".
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    assert (BUD2 : hfr asegs R HIA h2 <= hfr asegs R HIA h + (e + 1) * fr_charge (d + 1)) by (clear - HFR2 BUDFa; lia).
    assert (HV2' : havol asegs R HIA h2 <= havol asegs R HIA hc) by (clear - HV2; lia).
    destruct CASES as [[Er HH2] | (N & Er & NAL & NFR & NSTK & HH2 & NZ)]; subst r.
    - idtac "APP-NULL".
      pose proof (pinv_call [] hc h2 mc m2 nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb INVc HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2' HH2) as INV2.
      assert (HPP2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 q)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HPP| | exact I]. cbn [cells_size csize Nat.add].
        eapply client_range_lower; [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
      eapply null_walk with (e := e + 1) (q := q);
        first [ exact INV2 | exact HPP2 | exact HNE | exact BUD2 | exact E1 | clear - HP0 HQ0 HQL HPE LR HE0 HLN; lia | match goal with |- ?g => idtac "APP-NULL-LEFT:" g end ].
    - idtac "APP-NODE".
      pose proof (pinv_call [(N, 32)] hc h2 mc m2 nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb INVc HP2 MI2 ST2 HT2 HS2 HF2 HCS2 HV2' HH2) as INV2.
      assert (HPP2 : rw_cells asegs m2 PP [C8 (Z_to_bv 64 q)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HPP| | exact I]. cbn [cells_size csize Nat.add].
        eapply client_range_lower; [| exact PPLO]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b' [] FB 64 LF); exact Hb]. }
      change (Z.to_nat 32) with 32%nat in NZ.
      eapply link_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := oidp) (N := N);
        first [ exact INV2 | exact HPP2 | exact CPN | exact NAL | exact NFR | exact NZ | exact KLOOP | exact BUD2 | eassumption | match goal with |- ?g => idtac "APP-LINK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L16526487874.96L19616048289.99L2192452093.95 L22676661558.96L24188363034.96L32883993289.99L38339916114.9900001T03804U06207S09:09oS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz3HB12H22H32HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12HL1i2Hi1HS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12H3S2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H22HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz3HB02H12HLS2LF2sp2PP3CUR1P3END3BUF2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D12FB3sp13APP3APC1B3bsx2P02Lz2H12H32HL1i2Hi1HS2LF2sp2PP3CUR2bs3LFB2FB3sp12mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  #[using="LF sp PP CUR P END BUF bs LFB PP0 B1 B2 B3 DPB CUR0 DCB D1 FB sp1 APP APC"] Lemma bytes_at_slice : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "PmX,P,(?.&40.)(1:.(?.&8.))PB,$3.Pbsx,(1;.(?.&8.))PP0,$3.PLz,$3.P,(33.$19.R5.R4.R3.)P,(5.R5.R3.)P,(5.=R3.)P,(5.(6.R5.R4.)(6.R7.(=.(>.(?.&8.)R6.))))(0.(33.$19.R9.R6.(51.(?.&8.)(52.R5.)(53.(?.&8.)(52.(3?.R6.R8.))R7.)))(2.$3.(=.(>.(?.&8.)(51.(?.&8.)(52.R5.)(53.(?.&8.)(52.(3?.R6.R8.))R7.))))R5.))")
(* [comment removed for export] *).
  Proof.
    (intros mX B bsx P0 Lz dd_H; ddestruct dd_H as (HB0 & HB1 & HB); intros H1 H2 H3).
    assert (HL : length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx)) = Z.to_nat Lz).
    { rewrite firstn_length, skipn_length. lia. }
    split; [| rewrite HL; lia]. split; [lia|]. split; [rewrite HL; lia|].
    intros i Hi. rewrite HL in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat Lz)); [| lia].
    rewrite nth_error_skipn. rewrite <- (HB (Z.to_nat (P0 - B) + i)%nat) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02J0@C17025492443.240D27847976046.240D3953997537.218 D3953997537.243 D60109446735.240D60189065437.218D60189065437.243L10376197750.19 L10946870795.9  L12126572370.2  L12252132089.3  L12478726249.10 L13176305223.2  L1326225569.0   L13360490265.2  L16507621472.3  L1685717371.0   L1703141276.218 L17696347041.15 L17698509571.7  L19980016842.7  L20478160884.19 L21218866939.2  L26532001206.3  L27111942217.1  L28632618922.2  L30994845580.4  L33594514891.2  L35655538583.11 L36416293148.1  L36463206329.4  L38235734261.1  L38259954321.2  L38736745103.19 L39268637205.0  L41202929119.199L41409160545.3  L44166924249.3  L46710299783.5  L46745494493.3  L51578300575.1  L52941874306.3  L53779026635.15 L55085943702.3  L56380991837.10 L576250137.199  L57698627611.2  L58790369554.10 L60098763854.6  L62107348008.19 L63735181319.218L66151427842.16 L881835912.0    L9080220944.4   L9356559676.16  L943633757.19   N26738689353.241N42129917801.241O1478916974.240 O17025492443.240O24745514321.240O36520195031.240O43849271089.240O50689527441.240O51241073393.240O56414299794.240O59625529265.240P12115299733.218P12115299733.243P12257878110.240P13366212030.240P16492167430.240P21212095580.240P28627113325.218P28627113325.243P31000317067.243P33597136077.218P33597136077.243P36414458843.243P36465839390.240P38261788758.218P38261788758.243P41419110342.240P44164039966.218P44164039966.243P46717128672.240P52940256805.240P55088519473.240P57713046236.218P57713046236.243Q10048018846.217Q10598707900.211Q10649498890.212Q10651733935.211Q13733123218.211Q15766564435.240Q17426747697.240Q17701933584.212Q19243646445.218Q19243646445.243Q25952160488.217Q25952160488.242Q28465177121.215Q28465177121.240Q31124869336.240Q32681824661.218Q32681824661.243Q33842004701.239Q33842016006.214Q34363165844.240Q34390149656.212Q34964382778.240Q37149073081.218Q37149073081.243Q39180574961.218Q39180574961.243Q39600066516.212Q42439168719.240Q42439443119.218Q42439443119.243Q42641838973.239Q42641850022.214Q45257319447.218Q45257319447.243Q45353786896.211Q45741809296.218Q45741809296.243Q47388052542.217Q48360113622.240Q49746198710.240Q49746415830.218Q49746415830.243Q50294081709.211Q52124784706.240Q5265442331.216 Q5265442331.241 Q55415036769.218Q55415036769.243Q56854244147.218Q56854244147.243Q60191312605.217Q60191312605.242Q61847600945.212Q62380812747.240Q67038703949.240Q67038978349.218Q67038978349.243Q68013150533.218Q68013150533.243Q8699115497.218 Q8699115497.243 Q8699324297.240 Q9356887103.220 Q9644583048.240 00000101P03504`05U07B09509T09h09i09j0:N0:V0:W0:X0:Y0:Z0;F0;`0<70<O0<P0<Q0<Z0<^0<_0<`0<a0=:0=;0=<0=@0=A0=n0=o0>U0>V0>W0>X0>c0>h0>i0?C0?D0?]0@C0@D0@c0@m0B50Ba0C;0C<0CK0D>0DB0Dm0EQ0ER0ES0ET0EU0EV0EW0EX0EY0EZ0Fd0H40HZ0IF0Il0Im0K=0LS0N?0OI0PY0Qm0RQ0Sa0U70U]0Vi0X70Y90Y_0ZD0Zo0[`0\]0]10]E0]Y0]m0^Q0_50_I0_J0_K0`H0aK0ah0bK0bL0bM0bN0cB0d00d10d20dk0f50gE0hO0i_0i`0jB0k10kf0lc0mZ0nf10810L10M10N11B11g12W13P14O14c14d15B15f16Q17B17C17D18J19V1:P1;21;o1=51>A1?f1AQ1BR1CY1DQ1E11ENFS1R3HIA1h2LF2sp2PP3CUR3BUF2lo2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur1q3HTc3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CUR3BUF2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur1q3HTc3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR3BUF2lo2bs3LFB3LOS2FB3sp15nodes3cur1qS1R3NS15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3NBC3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3CUR3BUF2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur1q3NBC3CU03SPR4SP1R2F02HB5Ha_st5Hl_stS1R2lo3slo2bs4SLOS4SLOL3ALO3ACVS1R2lo3LOS2FB3ALO2F1FFS3END3BUF2bs2B34lenw1q2pe3HQL3HPE2L4S2lo3sp1SFFSS2LF2sp2PP3CUR3BUF2bs3LFB2FB3sp15nodes3cur1qS1P3BUF2bs2B11q2p03HP03HQ0S1P3BUF2B11q2p03HP03HQ0S1R3HIA1h2sp3TOP3sp13SP1FFS4lenw2K4S2PPFFFS1R3HIA1h2sp2lo3TOP5HTOPcFFS2loFS3END3BUF2lo2bs2B34lenw1q2pe3HQL3HPE5BUFLO2L4SS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curFFFS2sp2lo3sp1S3CURFS3END2bs4lenw1q2pe3HQL3HPEFS1R3BUF2lo2bs3LOS3ALO3BCES2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curFS1R3NS15NEED02sp2lo3SLO3sp13SP1S1R2lo3LOSS1R3NS13NB15NEED02sp3END3BUF2lo2bs2B33SLO3SPH4lenw1q2pe3HQL3HPE5BUFLO2L4S2LF2sp2PP3CUR3BUF2bs3LFB2FB3sp15nodes3cur1qS2FB2r03F641q1r1H2H02q02H4SS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2bsS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1q3x271CS2LF3BUF2lo2bs3LFB3sp15nodes1q3x271CFFFFFFFFFS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS2LF2PP3BUF2lo2bs3LFB4PPLO3sp15nodes1qS1R2LF3BUF2lo2bs3LFB3LOS3sp15nodes1q3ALO3ACVS2LF3BUF2lo2bs3LFB3sp15nodes3cur1q3CLOFS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes1q3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3END3BUF2lo2bs3LFB2B33SLO3sp13SP15nodes4lenw1q2pe3HQL3HPE3NBC5BUFLO2L43HXL2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3NBC3CLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes3cur1q3NBC3CLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC3ALO3ACV2HB5Ha_st5Hl_stS2LF3BUF2lo2bs3LFB3sp15nodes1q5BUFLOS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3NBC3ALO2F12HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes1q3NBC3ALO2F12HB5Ha_st5Hl_stS2LF3BUF2lo2bs3LFB2FB3sp15nodes1q4FBLOS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes3NBC5BUFLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes1q3NBC5BUFLO2HB5Ha_st5Hl_stS2LF3END3BUF2lo2bs3LFB2B33sp15nodes4lenw1q2pe3HQL3HPE5BUFLO2L43HXLS2LF3BUF2lo2bs3LFB2FB3sp15nodes1q4FBLOS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1qS2LF2sp2bs3LFB3sp13SP15nodes2HB5Ha_st5Hl_stS2LF2sp3BUF2bs3LFB3sp13SP15nodes1q2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R2LF3BUF2lo2bs3LFB3LOS5nodes1q3ALOS2LF3CUR3BUF2lo2bs3LFB5CURLO5nodes1qS2LF2PP2bs3LFB5nodesFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB3sp15nodes4SP1R2HBS2LF3BUF2bs3LFB3sp15nodes1q4SP1R2HBFFFS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcFFS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC3ALO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC3ALO2HB5Ha_st5Hl_stFS1R2LF3BUF3slo2bs3LFB4SLOS5nodes1qS1R2LF3slo2bs3LFB4SLOS3sp15nodes2HB5Ha_st5Hl_stS1R2LF3BUF3slo2bs3LFB4SLOS3sp15nodes1q2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBCS1R3NS15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3CUR3BUF2lo2bs3LFB5CURLO3SLO3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS2LF2PP2bs3LFB5nodesFFS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS2LF2sp3BUF2lo2bs3LFB3sp13SP15nodes1qS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp15nodes1q5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF2bs3LFB3TOP3sp15nodes1q5HTOPc2HB5Ha_st5Hl_stS2LF2bs3LFB2FB5nodesFS2LF2bs3LFB3sp15nodes2HB5Ha_stS2LF3BUF2bs3LFB3sp15nodes1q2HB5Ha_stS2LF2sp2bs3LFB3sp13SP15nodes2HB5Ha_st5Hl_stS2LF2sp3BUF2bs3LFB3sp13SP15nodes1q2HB5Ha_st5Hl_stFFS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2PP3BUF2lo2bs3LFB4PPLO5nodes1qS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBCS1R3NS15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp3BUF2lo2bs3LFB3SLO3LOS3sp13SP15nodes1q3NBC2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3LOS2FB3sp13SP15nodes3cur3NBC3CLO3ALO2F14FBLO2HB5Ha_st5Hl_stS1R3NS15NEED02LF2sp2PP3BUF2lo2bs3LFB4PPLO3SLO3LOS2FB3sp13SP15nodes3cur1q3NBC3CLO3ALO2F14FBLO2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF3slo2bs3LFB3TOP3sp13SP15nodes1q5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3BUF3slo2bs3LFB3TOP3sp13SP15nodes1q5HTOPcS2LF3BUF2bs3LFB3sp15nodes1q4SP1RS2LF3BUF2bs3LFB2FB5nodes1q2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma oid_walk : 
    (forall hc : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall nodes : (@list Z),
    forall cur : Z,
    forall nt : (bv 64),
    forall npad : (bv 64),
    forall cl : Z,
    forall cp : Z,
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenw : (bv 64),
    forall k64 : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    forall e : Z,
    forall q : Z,
    forall pe : Z,
    forall p0 : Z,
    forall x1 : (bv 64),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall s2v : (bv 64),
    forall s10v : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    (@pinvx [] mm hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb) ->
    ((cp = 0) ->
    (nodes = [])) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 q))]) ->
    (P <= p0) ->
    ((p0 + 4) <= q) ->
    ((q + (bv_unsigned lenw)) <= pe) ->
    (pe <= END) ->
    (0 <= e) ->
    ((4 * e) <= (p0 - P)) ->
    ((@hfr asegs R HIA hc) <= ((@hfr asegs R HIA h) + (e * (@fr_charge (d + 1))))) ->
    ((@Z.of_nat (length nodes)) <= e) ->
    (forall p' : Z,
    (p0 < p') ->
    (p' <= END) ->
    (@LoopOblig p')) ->
    (@aevtA asegs (@KF asegs R HIA hc mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (@al_sb (@arl_AL R))) s2v (Z_to_bv 64 PP) (Z_to_bv 64 cur) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 ((@Z.shiftr PP 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 pe) s10v (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabbf8) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros INV HNE HPP HP0 HQ0 HQL HPE HE0 HEQ BUDFa HLN KLOOP.
    pose proof (bv_unsigned_in_range 64 lenw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    ddestruct OIDH as (IMGo & GSBo & MCI & RTC & NBC & ISH).
    open_pinv_mu INV hc cur.
    pose proof (hcs_img_cs R HIA hc IMGo GSBo) as ICS.
    (* [comment removed for export] *)
    do 5 zstep.
    fold_pinv INV1 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4.
    2:{ idtac "OID-LEN4".
        assert (L4 : bv_unsigned lenw = 4) by (clear - K4 LR; try kland K4; rewrite ?Z.mod_small in K4 by lia; lia).
        destruct (bytes_at_slice _ BUF bs q 4 HBUF ltac:(clear - HP0 HQ0 B1; lia) ltac:(clear; lia) ltac:(clear - HQL HPE L4 B3; lia)) as [HXS HXL].
        (* [comment removed for export] *)
        do 3 zstep.
        pose proof (artA_bcmp asegs R HIA) as SPB. rewrite MCI in SPB. unfold A_WRAP_BCMP in SPB.
        (* [comment removed for export] *)
        zstep.
        ro_str 156864 4%nat as RO. img_aobj 156864 4 as ORO.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc ?lbx _ mx |- _ =>
          acallxA_sp sp1
            (eapply SPB with (h := hc) (LB := lbx) (LF := LF') (P := 156864) (Q := q) (n := 4) (lo := lo) (qs := firstn (Z.to_nat 4) (skipn (Z.to_nat (q - BUF)) bs));
             rewrite ?(unsigned_lit sp1) by exact SP1R;
             first [ exact RO | exact HXS | exact ORO | exact HXL | exact HHx | eassumption | reflexivity
                   | (eapply aobj_sub; [exact OBUF | clear - HP0 HQ0 B1; lia | clear - HQL HPE L4 B3; lia])
                   | lazymatch goal with
                     | |- _ \/ _ => first [ left; clear - ACV ALO LOS HQL HPE L4 B3 BUFLO; lia | right; clear - HQL HPE L4 B3 BUFLO SLO SPH NS1 NB1 NEED0; lia ]
                     | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                     | |- _ => clear - SLO SP1 NS1 NB1 NEED0 NBC; lia
                     end
                   | match goal with |- ?g => idtac "BCMP-SIDE:" g end ]) end end.
        idtac "OID-BCMP-BACK".
        (* [comment removed for export] *)
        zstep. if_cases Km; zify_cond Km.
        { idtac "OID-ANY".
          fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw k64 ja jb.
          eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
            first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP1-LEFT:" g end ]. }
        idtac "OID-OTHER4".
        (* [comment removed for export] *)
        do 3 zstep.
        clear HK64. assert (HK64 : K56 = Z_to_bv 64 0 \/ K56 = K56) by (right; reflexivity).
        fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw (Z_to_bv 64 18446744073709543296) ja jb.
        eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
          first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP2-LEFT:" g end ]. }
    idtac "OID-OTHER".
    (* [comment removed for export] *)
    do 3 zstep.
    clear HK64. assert (HK64 : K56 = Z_to_bv 64 0 \/ K56 = K56) by (right; reflexivity).
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 lenw (Z_to_bv 64 18446744073709543296) ja jb.
    eapply append_walk with (e := e) (q := q) (pe := pe) (p0 := p0) (oidp := q);
      first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - HP0 HQ0 HQL HPE B1 B3 LR; lia | match goal with |- ?g => idtac "OID-APP3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04F0@C40858145355.225C40860242543.247C60407910007.248C60410007123.224D10636937134.225D10639034250.248D16069757090.248D16071854214.225D16899842714.248D16901939902.225D2455419791.248 D2457516971.225 D32456773204.248D32458870384.225D46792746863.248D46794843979.225D60109446735.225D60111543915.248D65008160014.225D65010257194.248K20981739667.223K20983836855.246K29378133114.225K29380230238.248K30993319891.225K30995417079.248K49539617926.246K49541715106.223K65856058596.248K65858155712.224K67298046963.223K67300144087.246L10660966143.41 L10946870795.9  L11641955660.149L11641955660.41 L14402536676.212L14402536676.235L14402536676.3  L17715532577.0  L18489062900.25 L19191282159.149L19698248394.35 L19710956874.41 L20944479544.11 L20944629842.35 L20977711877.2  L21222559382.149L21654730866.2  L25583009864.35 L2621559066.1   L27111942217.1  L27817884949.223L27830583957.200L27938262793.35 L27942858889.41 L29391009772.3  L29844563604.41 L30507144274.2  L30997223346.3  L31165784228.187L31947253699.149L34427793940.7  L34429531785.12 L34429531785.17 L3480346400.41  L3484934304.35  L35236225328.25 L35655538583.11 L35903316071.25 L38109766357.149L38235734261.1  L39109034636.149L40228640085.0  L41110154015.25 L41202929119.187L41202929119.211L41251426164.1  L42488948659.2  L43305107741.25 L44469587106.149L44469587106.210L45176358614.19 L45186664561.3  L46502749028.3  L47369315770.19 L47870616696.2  L49233373885.2  L49526752708.2  L5021251703.1   L50678314462.3  L51140783048.149L51140783048.210L51578300575.1  L52836486813.17 L53506585646.210L55195235631.25 L5603384057.19  L56380991837.10 L57383048371.41 L57387379507.35 L576250137.211  L58972524609.3  L59308586248.2  L6008604205.3   L60098763854.6  L6031628760.2   L61594100017.149L61643025177.12 L62275882349.3  L62417043471.12 L62417043471.17 L64179129035.1  L65657875233.0  L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67304579733.2  L7063233879.19  L881835912.0    L8941784478.149 L9080220944.4   L9356559676.16  L9748633241.2   L9817099972.187 N16222602423.247N21382570003.247N26872553873.224N42205538131.247N48204456022.224N49450819242.224N60733400192.224N66852175570.247O14912726833.224O14914823957.246O18988691132.224O18990788248.246O20866770946.225O20868868134.248O22525005962.224O22527103150.248O27557489321.222O27559586445.245O30010457231.224O30012554411.246O33449646875.223O33451744063.246O3491220723.246 O3493317847.223 O37557392443.248O37559489567.225O3821773283.225 O3823870407.248 O424351700.223  O426448880.246  O44938202843.223O44940300031.246O49699726460.246O49701823576.224O50009742757.246O50011839873.223O54119978487.223O54122075603.246O55209884805.223O55211981985.246O57031441090.223O57033538278.246O64471909102.246O64474006218.224O7902534110.222 O7904631290.245 P21647862485.223P21649959665.246P30511339222.224P30513436402.246P42484919333.224P42487016449.246P45191338738.245P45193435862.222P46490677735.245P46492774851.222P47874275067.246P47876372191.223P49228642366.246P49230739482.224P50671478649.223P50673575773.246P62260666314.223P62262763502.246P66292560634.224P66294657758.246P66816411171.248P66818508295.225P67064334489.224P67066431677.246P9762015195.246 P9764112383.223 Q10592389541.223Q10592533181.225Q10594630297.248Q10596726309.200Q10636937134.225Q10637079734.223Q10639034250.248Q10649498890.200Q10649498890.224Q10651748618.199Q11133374175.225Q11135471355.248Q11657053839.225Q11659151019.248Q13731016587.223Q13733106231.199Q16069757090.248Q16071854214.225Q17025597925.248Q17027695041.225Q17681074618.225Q17683171742.248Q17701933584.200Q17701933584.224Q19546780271.223Q19559222767.200Q21765573510.248Q21767670690.225Q23216929724.248Q23219026840.225Q27573751300.225Q27575848480.248Q2803826605.225 Q2805923721.248 Q29775981542.225Q29778078658.248Q32679510481.248Q32681607669.225Q34377611452.225Q34379708568.248Q34390149656.200Q34390149656.224Q39600066516.200Q39600066516.224Q40251340134.200Q40264043238.223Q42439168719.225Q42441265899.248Q43479930840.225Q43482028028.248Q45317270253.225Q45319367369.248Q45353769141.199Q45360063753.223Q46792746863.248Q46794843979.225Q48118064779.225Q48120161967.248Q49746198710.225Q49748295826.248Q50283590580.223Q52711570354.225Q52713667478.248Q56530976407.225Q56533073587.248Q57828105177.225Q57830202365.248Q61847600945.200Q61847600945.224Q67038703949.225Q67040801129.248Q8699324297.225 Q8701421485.248 Q9356559674.202 Q9356559674.225 Q9631998992.200 Q9644448656.223 Q9644583048.225 Q9646680236.248 00000400800<00@00f01L02j04H05^07407507607\08B08h09N0:=0:l0;R0<80<S0<n0>20?90?U0@10A90B>0BY0C40D90EA0FZ0Fn0GX0H10H20H30H>0H?0I50JR0KY0L`0Lm0MF0MG0MH0MI0NZ0N_0Nc0OI0Oo0Q80RA0RB0SX0SY0SZ0UR0US0Ue0V70VR0WV0XZ0YZ0Z30ZB0[W0[[0[\0[]0[l0\R0]80]<0]=0]K0_H0aL0aX0aY0aZ0an0ao0b00b10b20b30d90fF0fK0fo0gU0hC0hV0ho0i@0iQ0j70jC0jI0jT0j^0jf0jg0k:0k;0kF0kQ0kR0kS0kT0kn0ko0l00l10l20lC0lD0lE0lT0mG0mH0o>0o`10:10T11M11o12I13B13\13]13^13_13`13a13b13c13d13e13f13g13h13i13j13k13l13m13n13o14014114214314414514614714814914:14;14<14=14>14?14@14A14B14C14D15715j16]17P18K19F1:A1;<1<=1=>1>?1?@1?`1@@1@`1A@1A\1B81C51D21Dm1Eh1Fc1G^1H21HF1HZ1Hn1IB1IV1Ij1J>1JR1Jf1K:1KN1KO1KP1Kd1L81Lo1Mf1N:1NN1OI1PD1PX1Pl1Q\1RL1SG1TB1TV1Tj1Tk1Tl1UA1UV1V21VN1VO1VP1VQ1VR1VS1VT1VU1VV1Vj1W>1WZ1X61Y31Z01Z11Z21ZF1ZZ1Zn1[B1\51\h1]R1^<1^P1^Q1^R1^S1^T1_B1`01`j1ad1b[1cR1dD1e61eP1ej1fA1fX1fo1gFS2PPS2PPS2FBS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3LOS2FB3sp13SP15nodes3cur3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12hc5nodes3cur3HTc3CU03SPR4SP1R2F0FFS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP3END3BUF2lo2bs3LFB2FB3sp11p5nodes3x263APB2x33x273x323x334POSTS2LF2PP3BUF2lo2bs3LFB2FB3sp15nodes3x453APB2q13Lw13x333x463x473x485POST0S2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP3BUF2bs3LFB3DPB5nodesS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur3x454CFBa2q13Lw13x333x463x473x485POST0S2LF2PP3END2lo2bs3LFB2FB3sp11p5nodes3cur3x264CFBa2x33x273x323x334POSTS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP2bs3LFB2FB3APP5nodesS2LF2PP3END2lo2bs3LFB2FB3sp11p5nodes3cur3x264CPPa2x33x273x323x334POSTS2LF2PP2lo2bs3LFB2FB3sp15nodes3cur3x454CPPa2q13Lw13x333x463x473x485POST0S1R3NS13NB15NEED02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP11p2Hp3ALO3ACP2F02q14Hq1aS1R2lo3LOS2FB3ALO2F1S2sp2PP3CUR2bs2FB3sp15nodes3cur2q13Lw13LR1S2PP2bs2FB3sp12q13Lw13LR1FFS2rg3RRg2KzSS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO3SLO2FB3sp13SP14FBLOS2sp2PP3CUR1P3END3BUF2bs3PP02B12B54CUR02FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F02q13Lw13LR14Hq1aS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S3END2bs1p2KfS2PP1P3END2bs2FB3sp11p2HpFFFS1R3NS13NB15NEED02sp2PP1P3END3BUF2lo2bs3PP02B13SLO3LOS2FB3sp13SP11p2Hp3ALO3ACP2F0S3sp1S2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0S1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FS1R3NS13NB15NEED02sp2PP3END3BUF2lo2bs3PP02B33SLO3LOS2FB3sp13SP13ALO3ACP2F02q13Lw14Hq1LFFS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLOFS1P3END1p2Hp1e3HEQS1P3END1p2Hp1e3HEQS1P3END1p1e3HEQ2q13Hq14Hq1aS1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS13NB15NEED02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO3SLO2FB3sp13SP14FBLO5BUFLOS1R3HIA1h2sp2lo3TOP5HTOPcS3BUF2bs2FB3APBS2sp2PP3CUR1P3END3BUF2bs3PP02B12B54CUR02FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F02q14Hq1aS2loFSS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS2FBFS2PP2bs2FB3APPS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLO2q13Hq14Hq1aS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLO2q13Hq14Hq1aS1P3END1p2HpFFS2q13Lw12q23Lw24Hq2LFFFFFS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLO2q13Lw13LR14Hq1a4Hq1LS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SLO3SPH2FB3sp11p2Hp5nodes3cur3CU03SPR4SP1R2F05BUFLO2q13Lw13LR14Hq1a4Hq1LS3CURS1P3END1p2Hp2q13Lw14Hq1a4Hq1L2q23Hq2S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS1R3NS13NB15NEED02sp2lo2bs3SLO2FB3sp13SP14FBLOS1p2q14Hq1a2q24Hq2aS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S2PP2bs2FB3sp12F0S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3curS3BUF2bs3B47S1i2HiS2rg3RRg2KzS1R2lo3LOSS2sp3sp1FS1P3END1p2Hp2q13Hq1FS2rg3RRg2RNS2rg3RRg2RNFSFS2FB2r03F641q1r1H2H02q02H4FFFFS3END2q13Lw14Hq1LSFS2sp2lo3sp13SP1S1R3NS13NB15NEED02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B22B32B54CUR03SLO3SPH2FB3sp15nodes3cur3CU03SPR4SP1R2F05BUFLOS2LF2sp2bs3LFB3sp13SP15nodes3x491CS2LF2bs3LFB2FB5nodes3x491CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x491CS2LF2sp2bs3LFB3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x341CS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3x341CS2LF2bs3LFB2FB5nodes3x491CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB5nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO2FB3sp13SP15nodes4FBLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP15nodes3ALO2F1S2LF2PP2lo2bs3LFB4PPLO3sp15nodesS2LF2PP2lo2bs3LFB4PPLO3sp15nodesS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2lo2bs3LFB2FB3sp15nodes4FBLOS2LF2sp2bs3LFB3sp13SP15nodesS2LF2sp2bs3LFB3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15nodes5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP15nodes3cur3CLOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP15nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S2LF2sp2PP3CUR2bs3LFB2FB3sp15nodes3cur3SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodes3ALOS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesFFS2LF2bs3LFB3sp15nodesS2LF2bs3LFB3sp15nodesS2LF2sp2bs3LFB3sp13SP15nodesS2LF2sp2bs3LFB3sp13SP15nodesFFFFFFFFS2LF2bs3LFB2FB5nodesS2LF2bs3LFB2FB5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R2LF3slo2bs3LFB4SLOS5nodesS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP15nodesFFS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS2LF2PP2bs3LFB5nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS5nodes3ALOS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp15nodes5HTOPcS2LF2bs3LFB2FB5nodesFFFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp15nodes3cur3SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP15nodesS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP15nodes5HTOPcS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB3sp15nodes4SP1RS2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0S2LF2bs3LFB2FB5nodes2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pp,$3.P,(0.(5.VP,R1.)(5.R1.VEND,))P,Pp',$3.P,(1.R3.R1.)P,(5.R2.VEND,)(4<.R3.)(4<.R3.)")
(* [comment removed for export] *).
  Proof.
    intros p Hp KLOOP. unfold LoopOblig. intros until x31. intros INV HNE HPP HE0 HEQ BUDFa HLN.
    pose proof INV as INV0.
    open_pinv_mu INV hc cur.
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Kf; zify_cond Kf.
    { idtac "BODY-FIN".
      eapply fin_walk with (e := e) (p := p); first [ exact INV0 | exact HPP | eassumption | clear - Hp HE0 HEQ; lia | match goal with |- ?g => idtac "BODY-FIN-LEFT:" g end ]. }
    assert (PL : p < END) by (clear - Kf Hp B1 B3 B5 B47; try kland Kf; rewrite ?Z.mod_small in Kf by lia; lia).
    clear Kf.
    (* [comment removed for export] *)
    do 5 zstep.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "BODY-GT1".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 Hp PL; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "GT1-LEFT:" g end ]).
    clear SPT OLEN.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw1 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q1 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q1 <= END |- _ => rename H into Hq1 end.
    pose proof (bv_unsigned_in_range 64 Lw1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    fold_pinv INV1 hc nodes cur nt npad cl cp w0 w1 w2 Lw1 k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT1-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q1);
        first [ exact INV1 | eassumption | clear - Hp Hq1 HE0 HEQ RRg RN; lia | match goal with |- ?g => idtac "BODY-ERR1-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq1a Hq1L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 10 zstep.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 32) 1%nat as OLEN2 end.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "BODY-GT2".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := q1) (END := q1 + bv_unsigned Lw1) (BUF := BUF) (bs := bs) (tag := 6) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3 Hp PL Hq1 Hq1a Hq1L LR1; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "GT2-LEFT:" g end ]).
    clear SPT OLEN2.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw2 end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : q1 <= q2 <= _ |- _ => rename H into Hq2 end.
    pose proof (bv_unsigned_in_range 64 Lw2) as LR2. unfold bv_modulus in LR2. cbn [Z.pow Z.of_N Pos.pow] in LR2.
    fold_pinv INV2 hc nodes cur nt npad cl cp w0 w1 w2 Lw2 k64 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT2-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (e := e) (rg := rg) (p' := q2);
        first [ exact INV2 | eassumption | clear - Hp Hq1 Hq1a Hq1L Hq2 HE0 HEQ RRg RN; lia | match goal with |- ?g => idtac "BODY-ERR2-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq2a Hq2L]. clear HLg Kz RRg.
    idtac "BODY-OID".
    eapply oid_walk with (e := e) (q := q2) (pe := q1 + bv_unsigned Lw1) (p0 := p);
      first [ exact INV2 | exact KLOOP | exact HNE | eassumption | clear - Hp Hq1 Hq1a Hq1L Hq2 Hq2a Hq2L HE0 HEQ LR1 LR2; lia | match goal with |- ?g => idtac "BODY-OID-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26726586762.6L34758806549.7L59308579281.600000B00W00jS3END1k1p2Hk2p'2H1S1P3END1p2Hp2p'2H12H2S3END1p2Hk2p'2H12H2". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma tloop : forall (k : nat) (p : Z), END - p <= Z.of_nat k -> P <= p <= END -> LoopOblig p.
  Proof.
    induction k as [|k IH]; intros p Hk Hp.
    - apply body_walk; [exact Hp|]. intros p' H1 H2. exfalso. clear - Hk H1 H2. lia.
    - apply body_walk; [exact Hp|]. intros p' H1 H2. apply IH; [clear - Hk H1; lia| clear - Hp H1 H2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03d0@C40858145355.189C60410007123.188D10636937134.189D16071854214.189D2457516971.189 D32458870384.189D39565106411.189D39565106411.191D46794843979.189D60109446735.189D60189065437.189D60189065437.191D65008160014.189D68221095944.189K20981739667.187K29378133114.189K30993319891.189K32053909171.189K36557281826.189K65858155712.188L10946870795.9  L12126572370.2  L13439873762.129L14402538871.179L14402538871.3  L1685717371.0   L17705907808.2  L18489062900.25 L19244690506.2  L19698471166.32 L2033615896.2   L20507244345.130L20977711877.2  L21207887510.129L21654730866.2  L24338315589.2  L24342030815.4  L24417571617.0  L26144142753.2  L2621559066.1   L27111942217.1  L27818050065.163L27938633021.32 L28632618922.2  L29391009772.3  L30507144274.2  L30997223346.3  L31941952482.130L32051500981.2  L32205124685.129L34452444106.2  L3484572308.32  L35236225328.25 L35903316071.25 L36544860596.2  L38259954321.2  L39168444181.129L39268637205.0  L39280637297.0  L40228640085.0  L40281191306.3  L40825480686.8  L41110154015.25 L41202929119.179L41251426164.1  L42488948659.2  L43305107741.25 L43491718995.0  L44166924249.3  L44439421325.129L45186664561.3  L46502749028.3  L46860880206.178L47870616696.2  L49233373885.2  L5021251703.1   L50678314462.3  L50814659508.178L50814826676.129L50816905951.180L51211448694.129L51905649112.2  L53516896046.178L54316457420.5  L54323387852.2  L55195235631.25 L56380991837.10 L56777281698.129L56777638818.178L57238178314.129L57387012359.32 L576250137.179  L57698627611.2  L58972524609.3  L59308586248.2  L6008606654.3   L60098763854.6  L6031628760.2   L61600383281.129L61845134989.129L62275882349.3  L62371644961.130L62619108508.0  L64179129035.1  L65110679799.3  L65110778357.8  L65862516566.2  L66099424948.4  L66151427842.16 L66298372189.2  L66812728480.3  L67070089790.2  L67242908301.13 L881835912.0    L8927112606.129 L9356559676.16  L9817099845.180 O14912726833.188O18988691132.188O20866770946.189O22525005962.188O25735317723.189O27557489321.186O30010457231.188O33542776439.189O3493317847.187 O37559489567.189O3821773283.189 O424351700.187  O44938202843.187O49701823576.188O50011839873.187O53687452546.189O55209884805.187O64474006218.188O7902534110.186 P12115299733.189P12115299733.191P2044614335.189 P21647862485.187P28627113325.189P28627113325.191P30511339222.188P34450608397.189P34450608397.191P38261788758.189P38261788758.191P42484919333.188P44164039966.189P44164039966.191P45193435862.186P46492774851.186P47876372191.187P49230739482.188P50671478649.187P57713046236.189P57713046236.191P62260666314.187P66292560634.188P66818508295.189P67064334489.188Q10048380702.187Q10592533181.189Q10592581281.163Q10598857381.185Q10636937134.189Q10649498890.186Q10651584438.185Q11133374175.189Q11657053839.189Q13191593416.186Q13193308734.185Q13732682891.185Q16057206942.187Q16071854214.189Q17027695041.189Q17681074618.189Q17701933584.186Q19546688875.163Q21767670690.189Q23219026840.189Q24852143294.187Q25952160488.188Q25952160488.190Q26481470270.185Q26481778816.185Q27573751300.189Q2803826605.189 Q28465177121.186Q28465177121.188Q29775981542.189Q32681607669.189Q32681824661.189Q32681824661.191Q33842005717.187Q34390149656.186Q37149073081.189Q37149073081.191Q39180574961.189Q39180574961.191Q39600066516.186Q40263906786.163Q42439168719.189Q42439443119.189Q42439443119.191Q42641839989.187Q45353866761.185Q45741809296.189Q45741809296.191Q46794843979.189Q47387953854.187Q48118064779.189Q48667442078.185Q48669158504.186Q49746198710.189Q49746415830.189Q49746415830.191Q50294161588.185Q5265442331.187 Q5265442331.189 Q53915156798.187Q54692959518.187Q55415036769.189Q55415036769.191Q56530976407.189Q56854244147.189Q56854244147.191Q57828105177.189Q60191312605.188Q60191312605.190Q60703360670.185Q60703575328.185Q61847600945.186Q66730946590.187Q67038703949.189Q67038978349.189Q67038978349.191Q67877090750.187Q8699115497.189 Q8699115497.191 Q8699324297.189 Q9356559674.166 Q9644565652.163 Q9644583048.189 00000400800T01e01f02B03_05805T06907]09=09Y0:c0;80<60<L0<a0=70=L0=`0=a0>J0>K0>V0>W0>_0?V0?W0@_0@`0A<0A=0A>0A?0AF0AT0AU0A\0Aa0Ae0BA0CK0CL0CM0CN0CO0Cg0Ch0Ci0Cj0Do0F00F?0F@0FA0G<0G=0G>0G?0GH0GI0GX0H40H80H90HG0HH0HI0IJ0IK0IL0J^0J_0J`0Ja0Jb0LW0NE0P:0PW0P_0Q;0QH0QI0R80RQ0T90Uh0Ui0V:0VV0VW0Vc0Vi0W40W>0WF0WG0X00X10XM0XN0XO0XY0Xc0Xd0Xo0YI0YJ0YK0YL0Yl0Ym0Yn0Zb0\[0\\0\]0\^0\_0\`0\a0\b0\c0\d0\e0\f0\g0\h0\i0\j0\k0\l0\m0\n0^:0_?0`70`80aG0bR0c@0dN0eU0fd0go0h]0ik0k20kh0l^0mZ0nV0o00o\10A10[11111i12_13Q13_13m14;14I14W14e15315415[16B16P17B18418B19819F19l1:b1;01;W1<T1=J1>11>X1>Y1>h1??1?V1?l1?m1?n1?o1@V1@W1Ac1Bh1D41E91E:1EH1E^1FN1G71Gi1H71H81H91HG1Hn1I\1JN1K@1Kc1L\1MN1M\1N41NL1O31Oe1PQ1Q61Q71Q81Q91Q`1Rh1Si1T[1UM1V=1Vo1Wa1Xi1Yj1ZQ1[R1\L1]71]K1]\1]mS2PPS2FBS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03LOS2FB3sp13SP14SLO'3SPR4SP1R2F0FS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CUR3END2bs3LFB3PP04CUR03TOP2FB3sp13SP12h15Ehtop3SPR4SP1R2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12h15Ehtop3SPR4SP1R2F02HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp1S1R3NS13NB15NEED02LF2sp2PP3CUR3END2lo2bs3LFB3PP04CUR03LOS2FB3sp13SP14SLO'3SPR4SP1R2F02HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03LOS2FB3sp13SP14SLO'3SPR4SP1R2F02HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PP04CUR03TOP2FB3sp13SP12h15Ehtop3SPR4SP1R2F0S2LF2PP2bs3LFB2FB3APPS2LF2PP1P3END3BUF2lo2bs3LFB2FB3sp13x253APB2x23x263x273x324POSTS2LF2PP3BUF2bs3LFB3DPBS2LF2PP3CUR2bs3LFB2D1S2LF3CUR2bs3LFB2FB3APCS2LF2PP2bs3LFB2FB3APPS1R2lo3LOS2FB3ALO2F1FS2sp2PP3CUR2bs3ALP3PP02FB3sp13SPR4SP1R2F0FS2rg3RRg2KgSS2rg3RRgS1R3NS13NB15NEED02sp2PP2lo2bs4PPLO2FB3sp13SP14SLO'4FBLOSS1R3NS13NB15NEED02sp2PP2lo2bs3PP03LOS2FB3sp13SP14SP1M3ALO3ACP4SLO'2F02F8FS2sp2PP3CUR2bs2FB3sp12rg3RRgFFFS3END1qS3END2rg1q3RRgSS3END1qS3sp1S2PPS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1R3NS13NB15NEED02sp2PP2lo3slo2bs3PP04SLOS4SLOL2FB3sp13SP13ALO3ACP4SLO'2F0FFFFS2sp2PP3CUR2bs2FB3sp12rgFFFS1R3NS13NB15NEED02sp2PP2lo2bs3PP03LOS2FB3sp13SP14SP1M3ALO3ACP4SLO'2F0S1R3NS13NB15NEED02sp2PP3BUF2lo2bs4PPLO2FB3sp13SP14SLO'4FBLO5BUFLOS3BUF2bs2FB3APBFFS2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp13SPR4SP1R2F01q2HqSSSS1R3HIA1hSS2PP3BUF2bs3DPBS2LF2sp2PP3CUR2bs3LFB2FB3sp1S2FBFS2PP2bs2FB3APPSFS2sp2PP3CUR1P3BUF2bs3PP02B12B54CUR02FB3sp13SPR4SP1R2F01q2Lw2LR2HqFFS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04PPLO4CUR03SPH2FB3sp14SLO'3SPR4SP1R2F0FFFFS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw2LR2Hq3HqLS1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw2LR2Hq3HqLS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw2LR2Hq3HqLS2sp2PP3CUR2bs2FB3sp11q2Lw2LRS2rg3RRgS2LF2sp2PP3CUR2bs3LFB2FB3sp1S1P3END1q3HqrFS1R3NS13NB15NEED02sp2lo2bs2FB3sp13SP14SLO'4FBLOS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NB15NEED02sp2PP3CUR1P3END3BUF2lo2bs3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q3Hqr2HqS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q3Hqr2HqFS2PP2bs2FB3sp12F0S2LF2sp2PP3CUR2bs3LFB2FB3sp1FS3BUF2bs3B47S1i2HiS2rg3RRg2KgS1R2lo3LOSS2sp3sp1FS2sp2PP3CUR2bs3ALP3PP02FB3sp13SPR4SP1R2F0FS2sp2PP3CUR2bs2FB3sp12rg3RRgSFS1P3END2B2S1P3END2B2FS1R3HIA1h1dS2FB2r03F641q1r1H2H02q02H4FFFS1R3HIA1h2sp2lo3TOP3sp13SP14HTOPSFS1R3NS13NB15NEED02sp2lo3LOS3sp13SP13ALO3ACV4SLO'3SPRS1R3NS13NB15NEED02LF2sp2PP3CUR1P3END3BUF2lo2bs3LFB3PP02B12B32B54CUR03SPH2FB3sp14SLO'3SPR4SP1R2F05BUFLO1q2Lw3Hqr2LR2Hq3HqLFFFFFFFFFFFFFFFFFFFS1R3NS13NB15NEED02LF2sp2PP3END2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3sp13SP14SLO'FS1R3NS13NB15NEED02LF2sp3END2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO4SLO'S1R3NS13NB15NEED02LF2sp3CUR3END2lo2bs3LFB5CURLO3sp13SP14SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp3CUR2lo2bs3LFB5CURLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp3END2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB2FB4SLO'4FBLOS1R3NS13NB15NEED02LF2sp3END3BUF2lo2bs3LFB3sp13SP14SLO'5BUFLO2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3sp13SP14SLO'5BUFLO2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB2FB3sp13SP14SLO'4FBLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F1S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS2FB3sp13SP13ALO4SLO'2F1S2LF2PP2lo2bs3LFB4PPLO3sp1S2LF2sp3END2bs3LFB3sp13SP12HB5Ha_st5Hl_st2FBS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stS2LF2lo2bs3LFB2FB3sp14FBLOS2LF2sp2bs3LFB3sp13SP1S1R3NS13NB15NEED02LF2sp3BUF2lo2bs3LFB3sp13SP14SLO'5BUFLOS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2bs3LFB2FBFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS2LF2PP2bs3LFBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2PP2bs3LFBS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'S2LF2PP2bs3LFBS2LF2sp2PP3CUR2bs3LFB2FB3sp13SPR2F02F8S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP13ALO4SLO'S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3END2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_st2FBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS2LF2bs3LFB3sp1S2LF2bs3LFB3sp14SP1R2HBS2LF2bs3LFB3sp14SP1R2HBS2LF2sp2bs3LFB3sp13SP1FFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS1R3NS13NB15NEED02LF2sp2PP3END2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp2PP2lo2bs3LFB4PPLO3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp3END2lo2bs3LFB3LOS3sp13SP13ALO4SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP13ALO4SLO'2HB5Ha_st5Hl_stFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3END3slo2bs3LFB4SLOS3sp12HB5Ha_st5Hl_st2FBS1R2LF3slo2bs3LFB4SLOS3sp12HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2PP2bs3LFBFFS2LF2PP2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3ALO4SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3HIA1h2LF2sp2bs3LFB3TOP3sp14HTOPS1R3HIA1h2LF2sp3END2bs3LFB3TOP3sp14HTOP2HB5Ha_st5Hl_st2FBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp14HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB3sp12HB5Ha_stS2LF2bs3LFB3sp12HB5Ha_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2sp3END2bs3LFB3sp13SP12HB5Ha_st5Hl_st2FBS2LF2sp2bs3LFB3sp13SP12HB5Ha_st5Hl_stFFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NB15NEED02LF2sp3END2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp13SPR4SP1R2F0S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'S1R3NS13NB15NEED02LF2sp3END2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_st2FBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3LOS3sp13SP14SLO'2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3END3slo2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_st2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV SP1 SP1M F64 FRSH CFB APP APC"] Lemma hdr_walk : 
    (forall h1 : (@HST asegs R HIA),
    forall mm : ((bv 64) -> (@option (bv 8))),
    forall x5 : (bv 64),
    forall x6 : (bv 64),
    forall x7 : (bv 64),
    forall x10 : (bv 64),
    forall x11 : (bv 64),
    forall x12 : (bv 64),
    forall x13 : (bv 64),
    forall x14 : (bv 64),
    forall x15 : (bv 64),
    forall x16 : (bv 64),
    forall x17 : (bv 64),
    forall x28 : (bv 64),
    forall x29 : (bv 64),
    forall x30 : (bv 64),
    forall x31 : (bv 64),
    forall w0 : (bv 64),
    forall w1 : (bv 64),
    forall w2 : (bv 64),
    forall lenj : (bv 64),
    forall ja : (@list (bv 8)),
    forall jb : (@list (bv 8)),
    (@HM asegs R HIA h1 LB ((FB, 64) :: LF) mm) ->
    ((@hcs asegs R HIA h1) = (@hcs asegs R HIA h)) ->
    ((@htop asegs R HIA h1) = (@htop asegs R HIA h)) ->
    ((@hstkhi asegs R HIA h1) = (@hstkhi asegs R HIA h)) ->
    ((@hflag asegs R HIA h1) = (@hflag asegs R HIA h)) ->
    ((@havol asegs R HIA h1) = (@havol asegs R HIA h)) ->
    ((@hfr asegs R HIA h1) = (@hfr asegs R HIA h)) ->
    (@rw_cells asegs mm FB [(@C8 w0); (@C8 w1); (@C8 w2)]) ->
    (@rw_cells asegs mm (FB + 32) [(@C8 lenj)]) ->
    (@rw_cells asegs mm ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R))) [(@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 241)); (@C1 (Z_to_bv 8 0)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243)); (@C1 (Z_to_bv 8 243))]) ->
    (@rw_cells asegs mm ((bv_unsigned sp) + (-104)) [(@C8 s11); (@C8 s10); (@C8 s9); (@C8 s8); (@C8 s7); (@C8 s6); (@C8 s5); (@C8 s4); (@C8 s3); (@C8 s2); (@C8 s1); (@C8 s0); (@C8 ra)]) ->
    (@rw_cells asegs mm sp1 [(@CB 56%nat ja); (@C8 (Z_to_bv 64 (@al_sb (@arl_AL R)))); (@CB 16%nat jb); (@C8 (Z_to_bv 64 FB))]) ->
    (@stk asegs mm (sp1 + 88) ((bv_unsigned sp) + (-104))) ->
    (@stk asegs mm lo sp1) ->
    (@mem_inv asegs mm) ->
    (@rw_cells asegs mm PP [(@C8 (Z_to_bv 64 P))]) ->
    (@rw_cells asegs mm CUR (@seq_cells ct cpad 0 0 0)) ->
    (@bytes_at asegs mm BUF bs) ->
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA h) mm PP 8) ->
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA h) mm CUR 32) ->
    (@aobj asegs (@arl_AL R) (@hcs asegs R HIA h) mm BUF (@Z.of_nat (length bs))) ->
    (@presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [(PP, (PP + 8)); (CUR, (CUR + 32))] m mm) ->
    (@sshad asegs (@arl_AL R) mm slo sp1) ->
    (@sshad asegs (@arl_AL R) mm sp1 (bv_unsigned sp)) ->
    (@aevtA asegs (@KF asegs R HIA h1 mo0) (@seq_parser_postE asegs R HIA PHIpol FFRpol CNTpol (fun r : Z => ((r = 0) \/ (r = (-8320)))) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CUR P END BUF (END - P) lo slo d m mo0) (@MS (@mkR (Z_to_bv 64 0xaba48) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 FB) (Z_to_bv 64 END) (Z_to_bv 64 PP) (Z_to_bv 64 CUR) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 ((@Z.shiftr FB 3) + (@al_sb (@arl_AL R)))) (Z_to_bv 64 (@al_sb (@arl_AL R))) s9 s10 (Z_to_bv 64 FB) x28 x29 x30 x31) F (Z_to_bv 64 0xabae0) fc None mm (@seg_rom asegs))))
(* [comment removed for export] *).
  Proof.
    intros until jb. intros HH1 Ehcs Ehtop Estk Eflag Evol Efr FHD HLEN FSH SAVE RSL SThi STlo MI HPP HCUR HBUF OPP OCUR OBUF PRES0 SS1 SS2.
    apply (rw_cells_split_CB asegs mm sp1 [] 56 ja [C8 (Z_to_bv 64 (al_sb AL)); CB 16 jb; C8 (Z_to_bv 64 FB)] [8; 8; 8; 8; 8; 8; 8]%nat) in RSL; [| reflexivity].
    cbn [mk_CB_cells app] in RSL.
    cb8_at RSL 1%nat. cb8_at RSL 2%nat. cb8_at RSL 3%nat. cb8_at RSL 4%nat. cb8_at RSL 5%nat. cb8_at RSL 6%nat.
    rewrite <- Ehcs in OPP, OCUR, OBUF.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m mm PRES0 HCS1 Estk) as PRES. clear PRES0.
    (* [comment removed for export] *)
    assert (FINX : forall (mx : mem) (r p' : Z) (lw : word) (rs : list cell)
                     (yra y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 t3v t4v t5v t6v t8v t9v t10v y28 y29 y30 y31 : word),
               HM asegs R HIA h1 LB LF' mx -> rw_cells asegs mx FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mx (Z.shiftr FB 3 + al_sb AL) FSHG ->
               rw_cells asegs mx (bv_unsigned sp + -104) SAVEL ->
               rw_cells asegs mx sp1 rs -> cells_size rs = 88%nat ->
               stk asegs mx (sp1 + 88) (bv_unsigned sp + -104) -> stk asegs mx lo sp1 -> mem_inv asegs mx ->
               presW asegs R HIA h1 LB LF (bv_unsigned sp) (bv_unsigned sp) W m mx ->
               sshad asegs AL mx slo sp1 -> sshad asegs AL mx sp1 (bv_unsigned sp) ->
               rw_cells asegs mx PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> rw_cells asegs mx CUR (seq_cells ct cpad 0 0 0) -> -0x3000 < r <= 0 -> (r = 0 \/ r = -8320 -> p' = END) ->
               aevtA asegs (KF asegs R HIA h1 mo0) POST
                 (MS (mkR yra (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 (Z_to_bv 64 r) y13 y14 y15 y16 y17
                          (Z_to_bv 64 FB) t3v t4v t5v t6v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t8v t9v t10v (Z_to_bv 64 FB) y28 y29 y30 y31)
                     F (Z_to_bv 64 0xabdb4) fc None mx (seg_rom asegs))).
    { intros. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
      eapply A_x509_policies_B.pol_fin with (hq := h1) (nodes := @nil Z) (p' := p') (hct := ct) (hcpad := cpad) (hcl := 0) (hcp := 0);
        first [ eassumption | reflexivity | exact CFB
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => rewrite Evol; clear; lia
                | |- hfr _ _ _ _ <= _ => rewrite Efr; unfold A_x509_policies_B.FFRpol; clear - B2 D0; unfold fr_charge; pose proof (Z.div_pos (END - P) 4 ltac:(lia) ltac:(lia)); nia
                | |- Z.of_nat (length _) <= _ => unfold A_x509_policies_B.CNTpol; cbn [length Z.of_nat]; apply Z.div_pos; [clear - B2; lia| clear; lia]
                | |- _ \/ _ => left; repeat split; reflexivity
                | |- seq_chain _ _ _ _ _ _ => apply chain_nil
                | |- List.NoDup [] => constructor
                | |- forall x, In x [] -> _ => intros x []
                end
              | match goal with |- ?g => idtac "FINX-LEFT:" g end ]. }
    idtac "HDR-FINX".
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (cs_ok_sb _ _ CSOK1) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof SLO as SLO'. unfold A_x509_policies_A.STKpol in SLO'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    unfold seq_cells in HCUR.
    pose proof (hm_top asegs R HIA h1 _ _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 NB1 NEED0; lia).
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (sp1 - lo))
      by (rewrite Ehcs; eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SLO' SP1 NS1 NB1 NEED0 TOP HTOP; lia]).
    assert (SCS01 : crange (hcs asegs R HIA h1) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (rewrite Ehcs; exact (hcs_stack asegs R HIA h)).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 64) by (rewrite Ehcs; exact CFB).
    dpose FRSH as (F0 & F1 & F2 & F3).
    assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FBLO : FB + 64 <= lo) by (clear - F1 ALO LOS; lia).
    assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h1 LB _ mm LB HH1 ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (CWP1 : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h1) PP 8)
      by (rewrite Ehtop; eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
    assert (INHc : In (FB, 24) (LB ++ fdata LF')) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDc : In (FB + 32, 64 - 40) (LB ++ fdata LF')) by (apply in_or_app; right; cbn; right; left; reflexivity).
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    pose proof (hm_abase asegs R HIA h1 _ _ mg HH1) as ABg.
    pose proof GT as SPT. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT.
    idtac "HDR-GT".
    acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA h1) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- BUF + _ < 2 ^ 63 => clear - B47; lia
                           | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO' NS1 NB1 NEED0 F1 FBLO ALO LOS; lia
                           | |- _ => clear - SP1 SP1M SLO' NS1 NB1 NEED0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "HGT-LEFT:" g end ]).
    clear SPT OLEN.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q <= END |- _ => rename H into Hqr end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    idtac "HDR-GT-BACK".
    (* [comment removed for export] *)
    zstep. if_cases Kg; zify_cond Kg.
    2:{ idtac "HDR-GT-ERR".
        do 3 zstep.
        first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RRg; lia)
              | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RRg; lia))
              | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].
        zstep. pz_br.
        lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
        eapply FINX with (p' := q); first [ eassumption | reflexivity | clear - RRg; lia | match goal with |- ?g => idtac "HDR-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kg RRg; try kland Kg; rewrite ?unsigned_lit in Kg by lia; rewrite ?Z_to_bv_unsigned in Kg; unfold bv_wrap, bv_modulus in Kg; cbn [Z.pow Z.of_N Pos.pow] in Kg; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq HqL]. clear HLg Kg RRg.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mx HHx) as AB2 end end.
    (* [comment removed for export] *)
    do 20 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "HDR-EMPTY".
      zstep.
      lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      eapply FINX with (r := -9574) (p' := q); first [ eassumption | reflexivity | clear; lia | match goal with |- ?g => idtac "HDR-EMPTY-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases Ke; zify_cond Ke.
    { idtac "HDR-MISMATCH".
      lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      eapply FINX with (r := -9574) (p' := q); first [ eassumption | reflexivity | clear; lia | match goal with |- ?g => idtac "HDR-MM-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "HDR-LOOP".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
    lazymatch goal with H : rw_cells _ ml CUR _ |- _ => change (rw_cells asegs ml CUR (seq_cells ct cpad 0 0 0)) in H end.
    lazymatch goal with H : rw_cells _ ml sp1 (CB 8 ?j0 :: _) |- _ =>
    assert (INV : pinv ml h1 (@nil Z) CUR ct cpad 0 0 w0 w1 w2 Lw (Z_to_bv 64 0) j0 jb) end.
    { unfold pinvx. spine; first [ eassumption | reflexivity | exact HCS1 | exact I
        | lazymatch goal with
          | |- havol _ _ _ _ <= _ => rewrite Evol; clear; lia
          | |- List.NoDup [] => constructor
          | |- _ \/ _ => left; repeat split; reflexivity
          | |- forall x, In x [] -> nodeF x => let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; destruct Hy
          end
        | match goal with |- ?g => idtac "HDR-INV-LEFT:" g end ]. }
    eapply (tloop (Z.to_nat (END - q)) q) with (e := 0);
      first [ exact INV | eassumption | (intros _; reflexivity) | rewrite Efr; clear; lia | cbn [length Z.of_nat]; clear; lia | clear - Hq Hqr; lia | match goal with |- ?g => idtac "HDR-LOOP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L67922604617.0000001S". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 DPB ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDF BUDV"] Lemma main_call : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)P,(1?.$19.VR,VHIA,Vh,VLB,VLF,Vm,)P,(54.$19.VR,VHIA,Vh,Vmo0,)P,(25.$19.Vm,VPP,(17.$28.(29.(27.&40.VP,))(2:.$28.)))P,(25.$19.Vm,VCUR,(26.Vct,Vcpad,===))P,(33.$19.Vm,VBUF,Vbs,)P,(31.$19.Vm,Vlo,(2?.&40.Vsp,))P,(36.$19.(2=.VR,)Vm,Vslo,(2?.&40.Vsp,))P,(32.$19.Vm,)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)Vm,VPP,+8.)P,(34.$19.(2=.VR,)(20.$19.VR,VHIA,Vh,)Vm,VCUR,+20.)(55.$19.(44.$19.VR,VHIA,$45.$46.$47.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCUR,VP,VEND,VBUF,(3?.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(56.(48.(49.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(27.&40.VPP,)(27.&40.VEND,)(27.&40.VCUR,)R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(27.&40.$57.)Vfc,(4:.(?.&40.))Vm,(4;.$19.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HK0 HPP HCUR HBUF ST SS MI OPP OCUR.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_policies_A.pro_walk with (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (ct := ct) (cpad := cpad); first [ exact HH | exact HPP | exact HCUR | exact HBUF | exact ST | exact SS | exact MI | exact OPP | exact OCUR | exact OBUF | eassumption
                             | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    ddestruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & w0 & w1 & w2 & lenj
                   & ja & jb
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & HLEN & FSH & SAVE & RSL & SThi & STlo & MI1
                   & HPP1 & HCUR1 & HB1 & OPP1 & OCUR1 & OBUF1 & APP & APC & PRES0 & SS1 & SS2).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & _).
    intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    eapply hdr_walk with (FB := FB) (sp1 := sp1) (h1 := h1);
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact APP | exact APC | exact HH1 | exact PRES0 | eassumption
            | match goal with |- ?g => idtac "HDR-PRE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L47484010984.4L61435248169.200000=00DS1R3HIA1h3H36S2LF2H1". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH"] Theorem A_x509_policies_specE : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(58.$19.VR,VHIA,$45.$46.$47.(59.VR,)(5:.$5;.#4.)L,(?.&40.)$5<.Lr,$3.(7.(2.$3.R1.=)(2.$3.R1.-2080.))$57.)")
(* [comment removed for export] *).
  Proof.
    unfold seq_parser_stmtE. intros until cpad. intros; subst.
    eapply main_call with (bs := bs) (ct := ct) (cpad := cpad) (d := d) (slo := slo);
      first [ eassumption | reflexivity
            | lazymatch goal with
              | |- (length _ < 511)%nat => match goal with H : (length _ <= LFMAX_CRT + 4)%nat |- _ => clear - H; unfold LFMAX_CRT in H; lia end
              | |- havol _ _ _ _ <= AVOL_MAX => match goal with H : havol _ _ _ _ + PHIpol _ <= AVOL_MAX |- _ => unfold A_x509_policies_B.PHIpol in H; clear - H; lia end
              end
            | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG UARG SM0 NS1 NB1 NEED0 CALLOC GT OIDH"] Theorem A_x509_policies_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies ()) "(5=.$19.VR,VHIA,$45.$46.$47.(59.VR,)(5:.$5;.#4.)L,(?.&40.)$5<.$57.)")
(* [comment removed for export] *).
  Proof. exact (seq_parser_stmtE_A _ _ _ _ _ _ _ _ _ _ _ A_x509_policies_specE). Qed.
End Walk.

(* [comment removed for export] *)
