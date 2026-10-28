(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse P_x509_crt_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_get_san_A A_x509_crt_ext_stmt A_x509_crt_ext_A A_asn1_get_bool A_oid_x509_ext A_x509_get_ext_A A_x509_basic_A A_x509_key_usage_A A_x509_skid_A A_x509_ns_cert_type_A A_x509_crt_ext_area A_x509_crt_ext_B A_x509_crt_ext_C A_x509_crt_ext_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
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
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


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
Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L28392174091.155L29782099606.1  L34564696816.159L49085461534.158L61422585519.103L63887242734.157L66149329409.196L9354819225.167 00001H01I02002S02\03B03j05KS1R2LF2sp2PP3CRT3BUF2lo3slo2bs4LFB33LFB3PP04PPLO4CRT04SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0SS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp11HS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11HS2LF4LFB3S2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB3sp11HS2LF2bs4LFB33LFB2FB2r01H1q1r2H02H12q02H5S1R4STKc5STKc12LF2sp2PP3CRT2lo3slo2bs4LFB33LFB3PP04CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4".
Lemma xz_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac xz_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac xz_lia := xz_clear; lia.
Local Ltac xz_hyp E :=
  unfold c_ltu, c_lts, c_eq, bv_eqb, bv_ltu, bv_lts, bv_leu in E; cbn [negb] in E;
  repeat match type of E with
         | context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) in E by xz_lia
         | context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) in E by xz_lia
         end;
  first [ apply Z.ltb_lt in E | apply Z.ltb_ge in E | apply Z.eqb_eq in E | apply Z.eqb_neq in E
        | apply Z.leb_le in E | apply Z.leb_gt in E | idtac ].
Local Ltac xz_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; xz_lia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; xz_lia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; xz_lia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; xz_lia) ]
  | |- context [Z.eqb ?a ?b] =>
      first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; xz_lia)
            | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; xz_lia) ]
  end.
Local Ltac xz_base :=
  first [ reflexivity
        | apply Z.ltb_lt; xz_lia | apply Z.ltb_ge; xz_lia | apply Z.leb_le; xz_lia | apply Z.leb_gt; xz_lia
        | apply Z.eqb_eq; xz_lia | apply Z.eqb_neq; xz_lia ].
Local Ltac xz_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); xz_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); xz_rec
  | _ => xz_base
  end.
Local Ltac xz_lits :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by xz_lia
  | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) by xz_lia
  end.
Local Ltac xz_split :=
  repeat match goal with
  | |- context [if ?b then _ else _] => let E := fresh "EB" in destruct b eqn:E; cbv iota; xz_hyp E
  end.
Local Ltac xz_solve :=
  rewrite ?xz_land7;
  first [ reflexivity
        | unfold_cond; fold_lit_ux; rewrite ?xz_land7; xz_lits; xz_dec; xz_rec
        | unfold v_sltu, v_slt, v_xor, c_ltu, c_lts, c_eq; unfold_cond; xz_split; cbn [negb]; fold_lit_ux; rewrite ?xz_land7; xz_lits; xz_dec;
          first [ reflexivity | xz_rec | exfalso; xz_lia ] ].
Local Ltac xz_if :=
  match goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xaacd4 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; xz_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xaacd4) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; xz_solve]
  end.
Local Ltac xz_pre := repeat xz_if.
Local Ltac zstep ::= xz_pre; step; zsimp; xz_pre.
Local Ltac xzto L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end);
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => idtac | false => idtac "XZTO-STOP:" pc; fail 1 end
  | |- _ (MS _ _ ?pc _ _ _ _) => idtac "XZTO-STOP:" pc; fail 1
  end.
Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = 0x531fc.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.   (* [comment removed for export] *)
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GB : asn1_get_bool_stmtA asegs AL A_ASN1_GET_BOOL.
  Hypothesis OIDH : oid_rt_hyps R HIA.
  Hypothesis GETEXT : x509_get_ext_stmtA asegs R HIA A_X509_GET_EXT.
  Hypothesis BASIC : x509_basic_stmtA asegs R HIA A_X509_BASIC.
  Hypothesis KUSE : x509_ku_stmtA asegs R HIA A_X509_KEY_USAGE.
  Hypothesis SKID : x509_skid_stmtA asegs R HIA A_X509_SKID.
  Hypothesis NSCT : x509_ns_stmtA asegs R HIA A_X509_NS_CERT_TYPE.
  (* [comment removed for export] *)
  Variables (PHIq PHIs PHIp PHIk : Z -> Z) (FFRq FFRs FFRp FFRk : Z -> Z -> Z) (CNTq CNTs CNTp CNTk : Z -> Z) (STKq STKs STKp STKk : Z).
  Hypothesis SEQOF : seq_parser_stmtE asegs R HIA PHIq FFRq CNTq STKq (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0) 0x9a658.
  Hypothesis GSAN : seq_parser_stmtE asegs R HIA PHIs FFRs CNTs STKs (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0) 0xaf3ec.
  Hypothesis GPOL : seq_parser_stmtE asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0 \/ r = -8320) 0xab9cc.
  Hypothesis AKID : x509_akid_stmtE asegs R HIA PHIk FFRk CNTk STKk (LFMAX_CRT + 4) 0xab564.
  (* [comment removed for export] *)
  Hypothesis STKc1 : 256 <= STKc.
  Hypothesis STKc2 : arl_need_amem R + 128 <= STKc.
  Hypothesis STKc3 : OID_X509_EXT_STACK_A + arl_need_bcmp R + 128 <= STKc.
  Hypothesis STKcq : STKq <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKcs : STKs <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKcp : STKp <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKck : STKk <= STKc + 48 + arl_need_smalloc R.
  (* [comment removed for export] *)
  Variables (PHIx : Z -> Z) (FFRx : Z -> Z -> Z) (CNTx : Z -> Z).
  Hypothesis PHIx0 : forall a, 0 <= a -> 0 <= PHIx a.
  Hypothesis FFRx0 : forall a e, 0 <= a -> 0 <= FFRx a e.
  Hypothesis CNTx0 : forall a, 0 <= a -> 0 <= CNTx a.
  Hypothesis PHIx_mono : forall a b, 0 <= a <= b -> PHIx a <= PHIx b.
  Hypothesis FFRx_mono : forall a b e, 0 <= a <= b -> FFRx a e <= FFRx b e.
  Hypothesis CNTx_mono : forall a b, 0 <= a <= b -> CNTx a <= CNTx b.
  Hypothesis PHIx_sadd : forall a b, 0 <= a -> 0 <= b -> PHIx a + PHIx b <= PHIx (a + b).
  Hypothesis FFRx_sadd : forall a b e, 0 <= a -> 0 <= b -> FFRx a e + FFRx b e <= FFRx (a + b) e.
  Hypothesis CNTx_sadd : forall a b, 0 <= a -> 0 <= b -> CNTx a + CNTx b <= CNTx (a + b).
  Hypothesis PHIq_le : forall a, 0 <= a -> PHIq a <= PHIx a.  Hypothesis FFRq_le : forall a e, 0 <= a -> FFRq a (e + 1) <= FFRx a e.  Hypothesis CNTq_le : forall a, 0 <= a -> CNTq a <= CNTx a.
  Hypothesis PHIs_le : forall a, 0 <= a -> PHIs a <= PHIx a.  Hypothesis FFRs_le : forall a e, 0 <= a -> FFRs a (e + 1) <= FFRx a e.  Hypothesis CNTs_le : forall a, 0 <= a -> CNTs a <= CNTx a.
  Hypothesis PHIp_le : forall a, 0 <= a -> PHIp a <= PHIx a.  Hypothesis FFRp_le : forall a e, 0 <= a -> FFRp a (e + 1) <= FFRx a e.  Hypothesis CNTp_le : forall a, 0 <= a -> CNTp a <= CNTx a.
  Hypothesis PHIk_le : forall a, 0 <= a -> PHIk a <= PHIx a.  Hypothesis FFRk_le : forall a e, 0 <= a -> FFRk a (e + 1) <= FFRx a e.  Hypothesis CNTk_le : forall a, 0 <= a -> CNTk a <= CNTx a.

  Local Notation STKx := (A_x509_crt_ext_A.STKx R STKc).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CRT P END BUF lo slo : Z) (bs : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB3 : (length LF <= LFMAX_CRT + 3)%nat.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L61422585519.103000009S2LF4LFB3". (* [comment removed for export] *)
  Let LFB : (length LF < 511)%nat. Proof. unfold LFMAX_CRT in LFB3. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (CRT + 424) EXT_SIZE.
  Hypothesis CRTLO : CRT + 424 + EXT_SIZE <= lo.
  Hypothesis DXB : CRT + 424 + EXT_SIZE <= BUF \/ BUF + n <= CRT + 424.
  Hypothesis D1 : PP + 8 <= CRT + 424 \/ CRT + 424 + EXT_SIZE <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
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
    unfold A_UAR_GOT in UARG; unfold A_x509_crt_ext_A.STKx, EXT_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CRT + 424, CRT + 424 + 272)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHX := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Variable mo0 : Model.
  Variable d : Z.
  Hypothesis NDL : List.NoDup (map fst LB).

  Local Notation POST := (x509_crt_ext_postA asegs R HIA PHIx FFRx CNTx h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END CRT (END - P) lo slo d m mo0).
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis BUDV : havol asegs R HIA h + PHIx (END - P) <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRx (END - P) d <= FR_MAX.

  Section Body.
  Variables (FB sp1 : Z) (a4e : word).
  Hypothesis SP1 : bv_unsigned sp - 304 <= sp1 <= bv_unsigned sp - 288.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 256.
  Hypothesis CFB : crange CS FB 256.
  Hypothesis APP : FB + 256 <= PP \/ PP + 8 <= FB.
  Hypothesis APC : FB + 256 <= CRT + 424 \/ CRT + 424 + 272 <= FB.
  Local Notation LF' := ((FB, 256) :: LF).
  Hypothesis BUFLO : BUF + n <= lo.
  Let SPR : 0 <= bv_unsigned sp < 2^64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn [Z.pow Z.of_N Pos.pow] in H. exact H. Qed.
  Let ALO : alloc_ceiling <= arl_stklo R := art_lo asegs R HIA.
  Let ACV : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 := alloc_ceiling_val R.
  Let F0 : 0 < FB. Proof. exact (proj1 FRSH). Qed.
  Let F1 : FB + 256 <= alloc_ceiling. Proof. exact (proj1 (proj2 FRSH)). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L28392174091.15500001HS1R2LF2sp2PP3CRT3BUF2lo3slo2bs4LFB33LFB3PP04PPLO4CRT04SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0". (* [comment removed for export] *)
  Let FBLO : FB + 256 <= lo. Proof. pose proof F1. pose proof ALO. pose proof LOS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L66149329409.19600000XS2LF2bs4LFB33LFB2FB2r01H1q1r2H02H12q02H5". (* [comment removed for export] *)
  Let F8 : FB mod 8 = 0. Proof. pose proof F64. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Let APB : FB + 256 <= BUF \/ BUF + n <= FB. Proof. apply (proj2 (proj2 (proj2 FRSH))). apply in_app_iff. left. exact BIN. Qed.
  Let SLOu : lo <= bv_unsigned sp - (336 + 48 + STKc + arl_need_smalloc R). Proof. exact SLO. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L63887242734.15700000VS2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB3sp11H". (* [comment removed for export] *)
  Let CRTLOu : CRT + 696 <= lo. Proof. pose proof CRTLO as H. unfold EXT_SIZE in H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L49085461534.15800000SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11H". (* [comment removed for export] *)
  Let D1u : PP + 8 <= CRT + 424 \/ CRT + 696 <= PP. Proof. pose proof D1 as H. unfold EXT_SIZE in H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L34564696816.15900000WS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp11H". (* [comment removed for export] *)
  Let DXBu : CRT + 696 <= BUF \/ BUF + n <= CRT + 424. Proof. pose proof DXB as H. unfold EXT_SIZE in H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L9354819225.16700001QS1R4STKc5STKc12LF2sp2PP3CRT2lo3slo2bs4LFB33LFB3PP04CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4". (* [comment removed for export] *)
  Let SP1R : 0 <= sp1 < 2^64.
  Proof. pose proof SLO as S. unfold A_x509_crt_ext_A.STKx in S. pose proof SPR. pose proof SP1. pose proof LOS. pose proof ALO. pose proof ACV. pose proof NS1. pose proof STKc0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Tactic Notation "xl" hyp_list(Hs) :=
    (clear - Hs B1 B2 B3 B47 B5 B30 D1 DPB DXB ALC ALP PP0 CRT0 PPLO CRTLO SLO SLOS SLOL TOP SPA SPH SP1 SP1M F64 APP APC NS1 NA1 NB1 STKc0 STKc1 STKc2 STKc3
               STKcq STKcs STKcp STKck BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SP1R LOS SLOu CRTLOu D1u DXBu);
    unfold A_x509_crt_ext_A.STKx, EXT_SIZE, SEQ_SIZE in *; first [lia | Z.div_mod_to_equations; lia].
  Ltac rt2 :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    unfold A_UAR_GOT in UARG; unfold A_x509_crt_ext_A.STKx, EXT_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0.
  (* [comment removed for export] *)
  Tactic Notation "xside" hyp_list(Hs) :=
    lazymatch goal with
    | |- (length _ < 512)%nat => cbn [length]; clear - LFB3; unfold LFMAX_CRT in *; lia
    | |- (length _ <= _)%nat => cbn [length]; clear - LFB3; unfold LFMAX_CRT in *; lia
    | |- client_range _ _ _ BUF _ => eapply client_range_block; [eassumption| clear; lia| clear; lia]
    | |- client_range _ _ _ _ _ => solve_client_range
    | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
    | |- aobj _ _ _ _ _ _ => match goal with H : aobj _ _ _ _ _ _ |- _ => eapply aobj_sub; [exact H| xl Hs| xl Hs] end
    | |- _ => xl Hs
    end.

  (* [comment removed for export] *)
  Local Notation FLOC lenw j1 otg opd olen op j2 crit j3 et j4 :=
    [C8 lenw; CB 24 j1; C4 otg; C4 opd; C8 olen; C8 op; CB 40 j2; C4 crit; CB 12 j3; C4 et; CB 100 j4].
  (* [comment removed for export] *)
  Local Notation FSHB := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].


  (* [comment removed for export] *)
  Ltac switch_h hc h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2 :=
    let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
    intros mo1 [HK1 MF1]; apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ mo1 (conj (proj2 (HKI2 mo1) HK1) MF1)); clear mo1 HK1 MF1;
    lazymatch goal with PRx : presW _ _ _ hc _ _ _ _ _ _ _ |- _ =>
      apply (presW_hmono R HIA hc h2) in PRx; [| intros ? Hxx; rewrite Ehcs2; exact Hxx| exact Estk2] end;
    rewrite <- Ehcs2 in *;
    lazymatch goal with HTx : htop asegs R HIA hc = htop asegs R HIA h |- _ => rewrite <- Ehtop2 in HTx end;
    lazymatch goal with HSx : hstkhi asegs R HIA hc = hstkhi asegs R HIA h |- _ => rewrite <- Estk2 in HSx end;
    lazymatch goal with HFx : hflag asegs R HIA hc = hflag asegs R HIA h |- _ => rewrite <- Eflag2 in HFx end;
    repeat match goal with CWx : client_wrange _ _ _ (htop asegs R HIA hc) _ _ |- _ => rewrite <- Ehtop2 in CWx end;
    repeat match goal with LW : ainv_laws _ _ |- _ => clear LW end; repeat match goal with KW : kinv_laws _ _ _ |- _ => clear KW end;
    pose proof (AIh_laws asegs R HIA h2) as LAWS; pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.


  (* [comment removed for export] *)
  Ltac pres_call HP :=
    lazymatch type of HP with presA _ _ ?LBc ?LFc ?SPc ?SSPc ?TOPc ?Wc ?mA ?mB =>
    lazymatch goal with PRx : presW _ _ _ ?hx LB LF _ _ _ _ mA |- _ =>
      apply (presW_call asegs R HIA hx LB LF _ _ W m mA mB LBc LFc SPc SSPc TOPc Wc) in PRx;
      [| exact HP| intros ? Hbb; first [exact Hbb | apply in_or_app; right; exact Hbb]| intros ? Hbb; first [exact Hbb | right; exact Hbb]| xl| xl| clear; lia
       | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [outside] in Hx |- *; clear - Hx; lia ]
    end end.

  Section Loop.
  Variable ENDX : Z.            (* [comment removed for export] *)
  Hypothesis EX1 : P <= ENDX.
  Hypothesis EX2 : ENDX <= END.

  (* [comment removed for export] *)
  Local Notation RSLK ja :=
    [C8 (Z_to_bv 64 18446744073709542042); C8 (Z_to_bv 64 (CRT + 648)); C8 (Z_to_bv 64 (CRT + 644)); C8 (Z_to_bv 64 (CRT + 656));
     C8 (Z_to_bv 64 (CRT + 688)); C8 (Z_to_bv 64 (CRT + 652)); C8 (Z_to_bv 64 (CRT + 480)); C8 (Z_to_bv 64 (CRT + 504));
     C8 (Z_to_bv 64 (CRT + 448)); C8 (Z_to_bv 64 (CRT + 608)); C8 (Z_to_bv 64 2048); C8 (Z_to_bv 64 (al_sb AL));
     C8 a4e; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 CRT); C8 (Z_to_bv 64 (FB + 72));
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ENDX); C8 (Z_to_bv 64 (FB + 144)); C8 (Z_to_bv 64 (FB + 128));
     CB 16 ja; C8 (Z_to_bv 64 FB)].
  Local Notation WMU := [(PP, PP + 8); (CRT + 424, CRT + 424 + 272); (FB, FB + 256); (lo, bv_unsigned sp);
                         (Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 32)].

  (* [comment removed for export] *)
  Definition xinv (Lx : list blk) (mm : mem) (hc : HST asegs R HIA) (X : xst) (floc fsh : list cell) (w0 w1 w2 k16 : word) (ja jb : list byte) : Prop :=
    HM asegs R HIA hc (Lx ++ LB) LF' mm
    /\ (forall x, CS x -> hcs asegs R HIA hc x) /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h
    /\ hflag asegs R HIA hc = hflag asegs R HIA h
    /\ xown asegs mm (Lx ++ LB) X /\ Permutation Lx (xblocks X)
    /\ xcells asegs CRT mm X
    /\ rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] /\ rw_cells asegs mm (FB + 32) floc
    /\ rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) fsh
    /\ rw_cells asegs mm (bv_unsigned sp + -104) SAVEL
    /\ rw_cells asegs mm sp1 (RSLK ja)
    /\ stk asegs mm (sp1 + 184) (bv_unsigned sp + -104) /\ stk asegs mm lo sp1 /\ mem_inv asegs mm /\ bytes_at asegs mm BUF bs
    /\ aobj asegs AL (hcs asegs R HIA hc) mm PP 8 /\ aobj asegs AL (hcs asegs R HIA hc) mm BUF n /\ aobj asegs AL (hcs asegs R HIA hc) mm (CRT + 424) 272
    /\ presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) W m mm
    /\ sshad asegs AL mm slo sp1 /\ sshad asegs AL mm sp1 (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition BUD (hc : HST asegs R HIA) (Lx : list blk) (bp : Z) : Prop :=
    havol asegs R HIA hc <= havol asegs R HIA h + PHIx (bp - P)
    /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRx (bp - P) d
    /\ Z.of_nat (length Lx) <= CNTx (bp - P).
  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L15754108151.175L15754108151.176L21832524781.181L29784460291.172L31465411412.181L33826088087.181L44015173491.172L52850699608.181L63368168617.173L65667496749.174L8518889475.172 00002404804`05A05i08508V09>09_0:@0:cS1R2LF2sp2PP3CRT1P3END3BUF2lo3slo2bs4LFB33LFB3PP02B12B22B33DPB4CRT04SLOS4SLOL2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21HS1R2LF2sp2PP3CRT1P3END3BUF2lo3slo2bs4LFB33LFB3PP02B12B22B33DPB4CRT04SLOS4SLOL2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21HS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x1k2A2S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x1k2A3S1R2LF2sp2PP3CRT1P3END3BUF2lo3slo2bs4LFB33LFB3PP02B12B22B33DPB4CRT04SLOS4SLOL2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21x1k3Bce1HS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x1k2A1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 DIMG STKc1 sp P END BUF slo bs LFB3 LFB PP0 CWP BIN B1 B2 B3 DPB CRT0 CWX DXB D1 SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APP APC SPR ALO ACV F0 APB D1u DXBu SP1R ENDX EX1 EX2"] Lemma lx_apart : forall (hc : HST asegs R HIA) Lx mq x k, HM asegs R HIA hc (Lx ++ LB) LF' mq -> (forall y, CS y -> hcs asegs R HIA hc y) -> In (x, k) Lx -> 0 < k ->
    (x + k <= PP \/ PP + 8 <= x) /\ (x + k <= CRT + 424 \/ CRT + 424 + 272 <= x) /\ (x + k <= FB \/ FB + 256 <= x) /\ x + k <= lo
    /\ (x + k <= Z.shiftr FB 3 + al_sb AL \/ Z.shiftr FB 3 + al_sb AL + 32 <= x).
  Proof.
    intros hc Lx mq x k HH HCSq HIN Hk.
    assert (A5 : x + k <= Z.shiftr FB 3 + al_sb AL \/ Z.shiftr FB 3 + al_sb AL + 32 <= x).
    { eapply apart_client_shadow with (CS := hcs asegs R HIA hc) (c := FB) (k := 32);
        [ exact (hcs_ok asegs R HIA hc) | eapply (hm_blocks_cs asegs R HIA hc _ _ _ HH); apply in_app_iff; left; apply in_app_iff; left; exact HIN
        | eapply crange_mono; [exact HCSq| exact CFB]
        | unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia | exact Hk | lia ]. }
    pose proof (obj_apart_new R HIA hc Lx LB LF LF' mq lo (htop asegs R HIA h) PP 8 x k DIMG HH ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(pose proof ALO; pose proof LOS; lia) ltac:(lia) HIN Hk) as A1.
    pose proof (obj_apart_new R HIA hc Lx LB LF LF' mq lo (htop asegs R HIA h) (CRT + 424) 272 x k DIMG HH ltac:(intros fb Hfb; right; exact Hfb) CWX ltac:(pose proof ALO; pose proof LOS; lia) ltac:(lia) HIN Hk) as A2.
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [BR HAP]. rewrite Forall_forall in BR.
    ddestruct (BR (x, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HIN)) as (_ & _ & Bce & _). cbn [fst snd] in Bce.
    pose proof (blocks_apart_app_lr (Lx ++ LB) LF' x k FB 256 HAP ltac:(apply in_app_iff; left; exact HIN) ltac:(left; reflexivity)) as A3.
    pose proof ALO. pose proof LOS. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact A5].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L44015431570.194L7305978910.199 00000T01@S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12csS2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB3sp11x2cs2A4". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 DIMG STKc1 P END BUF slo bs LFB3 LFB PP0 CWP BIN B1 B2 B3 DPB CRT0 CWX DXB D1 SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APP APC SPR ALO ACV F0 APB D1u DXBu SP1R ENDX EX1 EX2"] Lemma xown_mu : forall (hc : HST asegs R HIA) Lx mm mm' X,
    xown asegs mm (Lx ++ LB) X -> Permutation Lx (xblocks X) -> HM asegs R HIA hc (Lx ++ LB) LF' mm -> (forall y, CS y -> hcs asegs R HIA hc y) ->
    munch WMU mm mm' -> wmono asegs mm mm' -> xown asegs mm' (Lx ++ LB) X.
  Proof.
    intros hc Lx mm mm' X XO PERM HH HCSq MU WM.
    assert (NODES : forall x, In (x, SEQ_SIZE) (Lx ++ LB) -> In (x, SEQ_SIZE) (xblocks X) -> In (x, SEQ_SIZE) Lx).
    { intros x _ Hx. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hx]. }
    ddestruct XO as ((E1 & Q1) & (E2 & Q2) & (E3 & Q3) & (E4 & Q4) & REST).
    assert (INS : forall l x, In x l -> In (x, SEQ_SIZE) (SSEQ l)) by (intros l x Hx; unfold SSEQ; apply (in_map (fun a => (a, SEQ_SIZE))); exact Hx).
    assert (T : forall a nodes, (forall x, In x nodes -> In (x, SEQ_SIZE) (xblocks X)) -> seq_chain asegs (fun _ => True) mm (Lx ++ LB) a nodes -> seq_chain asegs (fun _ => True) mm' (Lx ++ LB) a nodes).
    { intros a nodes HX HC. eapply chain_mem; [exact HC| intros x Hx; eapply chain_nodes_in; [exact HC| exact Hx]|].
      intros x cs Hx HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz. cbn [disjoint_from].
      assert (XL : In (x, SEQ_SIZE) Lx) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| apply HX; exact Hx]).
      ddestruct (lx_apart hc Lx mm x SEQ_SIZE HH HCSq XL ltac:(unfold SEQ_SIZE; lia)) as (A1 & A2 & A3 & A4 & A5). unfold SEQ_SIZE in *. repeat split; (assumption || lia) (* [comment removed for export] *). }
    unfold xblocks in T.
    refine (conj (conj E1 (T _ _ _ Q1)) (conj (conj E2 (T _ _ _ Q2)) (conj (conj E3 (T _ _ _ Q3)) (conj (conj E4 (T _ _ _ Q4)) REST)))).
    - intros x Hx. apply in_or_app; right; apply in_or_app; left. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left. apply INS. exact Hx.
    - intros x Hx. apply in_or_app; left. apply INS. exact Hx.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LoopOblig (p : Z) : Prop :=
    forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
           (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 s6v s7v s9v x28 x29 x30 x31 : word),
      xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p)] ->
      BUD hc Lx p ->
      aevtA asegs (KF asegs R HIA hc mo0) POST
       (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 (Z_to_bv 64 (CRT + 640)) x15 x16 x17
                (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 ENDX) (Z_to_bv 64 (FB + 32)) s6v s7v
                (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) s9v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
            F (Z_to_bv 64 0xaa8c4) fc None mm (seg_rom asegs)).


  (* [comment removed for export] *)
  Ltac open_xinv INV hc :=
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & XO & PERM & XC & FHD & FLOCc & FSH & SAVE & RSL & SThi & STlo & MI & HBUF & OPP & OBUF & OEXT & PRES & SS1 & SS2);
    unfold xcells, wbuf, CrtExtStmts.akid_cells, seq_cells in XC; cbn [app] in XC;
    destruct XC as (XV & XS & XK & XA & XW & XP & XE & XU & XN);
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (cs_ok_sb _ _ CSOKc) as SB64;
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo0) as KINV;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOPc; rewrite HTc, HSc in HTOPc;
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo))
      by (eapply crange_mono; [exact HCSc| eapply crange_sub; [exact SCS0| exact LOS| xl HTOPc]]);
    assert (SCS1c : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| xl]);
    assert (SCS0c : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    assert (WCX : wcover R LB LF (bv_unsigned sp) W (CRT + 424) 272) by (apply wcover_inside; cbn [inside]; right; left; clear; lia);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ _ =>
      assert (SUBh : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata LF'))
        by (intros b' Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; exact Hb'| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb']);
      assert (CWPn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) PP 8) by (rewrite HTc; eapply client_wrange_mono; [exact CWP| exact SUBh]);
      assert (CWXn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) (CRT + 424) 272) by (rewrite HTc; eapply client_wrange_mono; [exact CWX| exact SUBh]);
      assert (CWPh : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBh]);
      assert (CWXh : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA h) (CRT + 424) 272) by (eapply client_wrange_mono; [exact CWX| exact SUBh]);
      assert (CRPs : client_range L (Lh ++ fdata LF') sp1 PP 8) by (eapply (client_range_wsep L (LB ++ fdata LF) _ lo _ sp1 _ _ CWP); [exact SUBh| left; exact PPLO]);
      assert (CRXs : client_range L (Lh ++ fdata LF') sp1 (CRT + 424) 272) by (eapply (client_range_wsep L (LB ++ fdata LF) _ lo _ sp1 _ _ CWX); [exact SUBh| left; xl]);
      lazymatch type of HHc with HM _ _ _ _ (?Lxx ++ LB) _ ?mq =>
        pose proof (fresh_apart_grow R HIA hc Lxx LB LF mq FB 256 FRSH HHc) as FRSHc;
        destruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lxx ++ LB) LF mq FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
          as (_ & INF & INHc & INDc & AP & _ & _ & _ & SBND & APS); change (256 / 8) with 32 in SBND, APS end;
      assert (BINc : In (BUF, n) (Lh ++ fdata LF')) by (apply SUBh; apply in_app_iff; left; exact BIN)
    end;
    pose proof (art_stk_high asegs R HIA) as STKH.

  Ltac open_xinv_mu INV hc :=
    open_xinv INV hc;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl WMU mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB; pose proof (conj HHx I) as HH0 end end.

  (* [comment removed for export] *)
  Tactic Notation "fold_xinv" ident(INVn) constr(hc) constr(Lx) constr(X) constr(floc) constr(fsh) constr(w0) constr(w1) constr(w2) constr(k16) constr(ja) constr(jb) :=
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end);
    lazymatch goal with MU : munch _ ?m0 ?mx, WM : wmono _ ?m0 ?mx, XOx : xown _ ?m0 _ _, PMx : Permutation _ _, HHz : HM _ _ _ hc _ _ ?m0 /\ True |- _ =>
      let XO2 := fresh "XO2" in
      lazymatch goal with HCz : (forall x, CS x -> hcs asegs R HIA hc x) |- _ => pose proof (xown_mu hc _ _ _ _ XOx PMx (proj1 HHz) HCz MU WM) as XO2 end;
      assert (INVn : xinv Lx mx hc X floc fsh w0 w1 w2 k16 ja jb)
        by (unfold xinv, xcells, wbuf, CrtExtStmts.akid_cells, seq_cells;
            cbn [app x_v1 x_v2 x_v3 x_v4 x_sct x_scp x_scl x_sp x_sn x_snodes x_k1 x_k2 x_k3 x_k4 x_a1 x_a2 x_a3 x_a4 x_act x_acp x_acl x_ap x_an x_anodes
                 x_r1 x_r2 x_r3 x_r4 x_w1 x_w2 x_w3 x_w4 x_pct x_pcp x_pcl x_pp x_pn x_pnodes x_et x_ca x_mp x_ku x_ect x_ecp x_ecl x_ep x_en x_enodes x_ns x_seen
                 setku setns setbc setsk seteku setsan setpol setakid setet xst_v3 xst_zero];
            spine; first [eassumption | solve [spine; eassumption] | match goal with |- ?g => idtac "FOLD-LEFT:" g end])
    end.

  (* [comment removed for export] *)
  Tactic Notation "fold_xinv_at" ident(INVn) constr(mx) constr(hc) constr(Lx) constr(X) constr(floc) constr(fsh) constr(w0) constr(w1) constr(w2) constr(k16) constr(ja) constr(jb) :=
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end);
    assert (INVn : xinv Lx mx hc X floc fsh w0 w1 w2 k16 ja jb)
      by (unfold xinv, xcells, wbuf, CrtExtStmts.akid_cells, seq_cells;
          cbn [app x_v1 x_v2 x_v3 x_v4 x_sct x_scp x_scl x_sp x_sn x_snodes x_k1 x_k2 x_k3 x_k4 x_a1 x_a2 x_a3 x_a4 x_act x_acp x_acl x_ap x_an x_anodes
               x_r1 x_r2 x_r3 x_r4 x_w1 x_w2 x_w3 x_w4 x_pct x_pcp x_pcl x_pp x_pn x_pnodes x_et x_ca x_mp x_ku x_ect x_ecp x_ecl x_ep x_en x_enodes x_ns x_seen
               setku setns setbc setsk seteku setsan setpol setakid setet xst_v3 xst_zero];
          spine; first [eassumption | solve [spine; eassumption] | match goal with |- ?g => idtac "FOLD-LEFT:" g end]).

  (* [comment removed for export] *)
  Ltac joinc H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mq ?A1 ?cs1 => lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      let Hj := fresh "J" in
      assert (Hj : rw_cells sg mq A1 (cs1 ++ cs2))
        by (apply (proj2 (rw_cells_app sg mq A1 cs1 cs2)); split; [exact H1|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with A2 by (clear; lia) end; exact H2);
      clear H1 H2; rename Hj into H1; cbn [app] in H1 end end.


  (* [comment removed for export] *)
  Ltac gt_call OLENx FLENx p0z e0z lenpz tagz Hs :=
    let SPT := fresh "SPT" in
    pose proof GT as SPT; unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ ?hc _ _ mx |- _ =>
      acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := lenpz) (P := p0z) (END := e0z) (BUF := BUF) (bs := bs) (tag := tagz) (lo := lo);
                     rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                     try (exact (art_alwf asegs R HIA));
                     first [ exact OLENx | exact FLENx | solve_crange | Hs
                           | match goal with |- ?g => idtac "GT-LEFT:" g end ]) end end;
    clear SPT.


  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L14406737544.210L19246787633.2  L20509319872.160L31939843611.160L40228640085.0  L51907746211.2  L62369502168.160L64412859763.2  00000100200M00e00f00m01H01OFSS2sp2PP3CRT2bs2FB3sp12rg2RRS2sp2PP3CRT2bs2FB3sp12rgSS2rg2RRS2sp2PP3CRT2bs2FB3sp12rg2RRS2rg2RR".
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 PP0 CWP PPLO BIN B1 B2 B3 B47 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma err_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (rg p' bp : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    -0x7f < rg < 0 -> BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaacc4) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_D.err_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_D.err_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_D.err_walk ]; eassumption.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@C40858145355.309C60410007123.308D10636937134.309D16071854214.309D16901939902.309D2457516971.309 D32458870384.309D39243574473.309D46794843979.309D60109446735.309D66237350158.309K1093189274.307 K12719279130.307K16483843482.307K17012660943.307K20040736922.307K20981739667.307K24527616463.307K26389978266.307K27873714767.307K28081892559.307K29378133114.309K30993319891.309K33674735898.307K41744454554.307K42309482703.307K45300827802.307K49805008847.307K53361377999.307K54996069696.308K56707495759.307K62527904282.307K65858155712.308K67776174415.307L10039789130.189L10039789130.298L10044042153.299L10079012065.2  L10323762809.81 L1103920410.2   L12729978778.2  L12865196093.88 L12867456647.85 L13527341863.85 L13529531805.88 L13636442081.2  L13946884974.189L13946884974.298L14402536676.3  L14402536676.300L15940222605.299L16482024986.2  L17025536345.2  L17698511111.81 L18501743953.81 L19700477810.81 L20038394650.2  L20407675145.189L20977711877.2  L21122558689.2  L21230010724.3  L21654730866.2  L24514671193.2  L24697106893.189L24882004373.71 L2621559066.1   L26375085850.2  L27111942217.1  L27832549545.283L27877616089.2  L27940752049.81 L28068947801.2  L29391009772.3  L29680655011.1  L30507144274.2  L30997223346.3  L31320619992.2  L32749673313.2  L33685467802.2  L3482445080.81  L35248710037.81 L35655538583.72 L35916062914.81 L36307103329.2  L38235734261.1  L40058613985.2  L40228640085.0  L4086203097.189 L41114250170.81 L41202929119.299L41251426164.1  L41755152410.2  L42296603481.2  L42383166414.189L42488948659.2  L43317526968.81 L45193043736.24 L45311526170.2  L45382656977.84 L47870616696.2  L48937103345.300L49233373885.2  L49800647769.2  L5021251703.1   L50678314462.3  L53357021529.2  L53506586542.298L53530411688.1  L53704106081.2  L55008356054.2  L55182816650.81 L55504905889.0  L5659140096.84  L56719719641.2  L5685787249.3   L57083180513.2  L57389346443.81 L576250137.299  L58972694988.81 L59308586248.2  L6008604205.3   L60558678699.1  L61774255627.2  L62275882349.3  L62417043471.88 L62513011098.2  L62873986039.1  L64179129035.1  L64850595401.0  L65331221217.2  L656832749.85   L65862516566.2  L66298372189.2  L66812728480.3  L67070089790.2  L67763426009.2  L866928845.84   L881835912.0    L9090702513.71  N15340698282.308N18792612241.308N26872553873.308N48204456022.308N60733400192.308N66590330291.308O12232075104.307O14559438816.307O14912726833.308O151759997.307  O15540865262.307O16086026184.308O16723931389.307O18988691132.308O20866770946.309O21058125422.307O22525005962.308O2463212925.307 O24727989486.307O25722042592.307O25895279840.307O30010457231.308O34618340093.307O3493317847.307 O37559489567.309O37860830077.307O3821773283.309 O41222319070.306O424351700.307  O43490832480.307O44938202843.307O45423855982.307O46148948448.307O4719021806.307 O49076961262.307O49701823576.308O50011839873.307O52019636960.307O55209884805.307O55738917358.307O59000851965.307O59916692861.307O61256669038.307O64251960330.308O64474006218.308O66521921705.306O66725143264.307O6754613856.307 O6815798909.307 O8878376686.307 O9125703549.307 P10069038662.307P13625410886.307P21137750086.307P21231604675.306P21647862485.307P30511339222.308P32763840966.307P36322327750.307P40051745350.307P42484919333.308P47876372191.307P49230739482.308P50671478649.307P53719298758.307P5671676118.306 P57084798790.307P61788423340.308P62260666314.307P65345388614.307P66292560634.308P66818508295.309P67064334489.308Q10592389669.307Q10592533181.309Q10598691865.283Q10636937134.309Q10637080374.307Q10649498890.308Q11133374175.309Q11657053839.309Q13731015691.307Q15673955380.307Q16071854214.309Q16178735000.309Q17027695041.309Q17681074618.309Q17701933584.308Q18824847950.308Q19561451475.283Q21767670690.309Q27573751300.309Q2803826605.309 Q29775981542.309Q3166354565.308 Q32681607669.309Q36985122307.309Q39600066516.308Q40904410655.309Q40916972731.308Q42439168719.309Q45360064137.307Q46794843979.309Q48118064779.309Q49746198710.309Q5638148954.283 Q56530976407.309Q57828105177.309Q60314416515.309Q6132825310.309 Q61847600945.308Q67026529334.308Q67038703949.309Q8699324297.309 Q9356559674.286 Q9633965612.283 Q9644583048.309 00000400800Y02003=03>03_03`04A04k05L05g06B06]07807S07m08H08c09>09Y0:40:O0:j0;E0;`0<;0<V0=10=K0=f0>A0>[0?60AH0Cf0FD0FE0Gj0Gk0Gl0J80LD0NF0PH0PI0RU0Tm0U80U90W[0W\0W]0Y[0\Z0^[0^\0^]0^^0^_0^`0^a0^b0`80`V0`[0`\0``0aA0aB0c]0c^0c_0cd0ce0cf0cn0co0d00f30h90ik0jH0jI0jM0jN0jO0jo0kL0km0l10l20l30m>0m?0mX0mn0mo0nW0nX0o90o:0o;0o<0o=0o>0o_0oc0od0oe12`12a14V14W14X14Y15115R15o16516@16D16E16F16l16m17117217317417I17J17K17L17M17N19<19=19Y1:21:31:L1:m1;g1=11=21=31=41=51=61=71=81=91=:1=;1=<1==1=>1=?1=@1=A1=B1=C1=D1=E1=F1=G1=H1=I1=J1=K1=L1=M1=N1=O1=P1=Q1=R1=S1=T1=U1=V1=W1=X1=Y1=Z1=[1=\1=]1=^1>]1?\1@[1AW1AX1BL1CK1DJ1EI1F=1G91H51HT1IS1JU1KT1LP1Lo1Mn1NI1OG1PC1PV1Pi1Q<1QO1Qb1R51RH1RI1R\1Ro1Sg1T:1TM1UI1U\1VI1W41X01X11XE1X`1Xa1Xb1Xc1Xd1Xe1Xf1YA1YT1Yg1Z[1[D1[W1[X1\E1]D1]E1^?1_71_o1``1a91aO1aeS2PPS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTcFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3BUF2bs4LFB33LFB2FB3APBS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LFS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e43HE4FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02bp2e43HQ03HE43HBP2q43Hq44Hq4aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02bp2e43HQ03HE43HBP2q43Hq44Hq4aS2rg3RRg2KzFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43Hq43LR44Hq4a4Hq4LFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFFFFFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R1q2p02bp3HQ03HBP2q43Lw43LR44Hq4aS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S3sp1FS2PPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFS3CRTFFS2sp3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs2FB3sp13APBFS2loFSS2sp2PP3CRT2bs2FB3sp12q43Lw43LR4S2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2FBFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R1q2p03HP03HQ02q44Hq4aFS2sp2PP3CRT2bs2FB3sp13APPS2bs2e42q43Lw44Hq4L2KmFS2sp2PP3CRT2bs2D12FB3sp13D1u1q2e42q43Hq4FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2FBFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4SS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02bp3HQ03HBP2q44Hq4aFFFS2sp2PP3CRT2bs2FB3sp12F0S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT3BUF2bs3B472FB3sp1S1i2HiS2rg3RRg2KzS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNFS2FBFSFS2sp2PP3CRT2bs2FB3sp1FFFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p03HQ02q44Hq4aSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2LF2bs4LFB33LFB2FB3x341CFS2LF2bs4LFB33LFB2FB3x341CS2LF2sp2bs4LFB33LFB3sp13SP13x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu3x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2lo2bs4LFB33LFB2FB3sp14FBLOS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP1S1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBFS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOuFS2LF2bs4LFB33LFB3sp1S2LF2sp2bs4LFB33LFB3sp13SP1FFFFFFS1R2LF3slo2bs4LFB33LFB4SLOSS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPcS2LF2bs4LFB33LFB2FBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB3sp14SP1RS2LF2bs4LFB33LFB2FB2F0S2LF2bs4LFB33LFB2FB2F0".
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma octet_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (OL OP q p0 bp e4 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e4 -> e4 <= ENDX -> BUD hc Lx bp -> P <= bp <= p0 ->
    BUF <= OP -> 0 <= OL -> OP + OL <= e4 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e4) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaa9bc) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_D.octet_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_D.octet_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_D.octet_walk ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06<0@C40858145355.313C51712377427.312D10636937134.313D24582091142.313D28498761192.287D33317801621.286D33317801621.287D35749367497.313D40338479819.286D40338479819.287D4451634193.287 D46794843979.313D49496112240.313D55184611262.313D57793146470.286D57793146470.287D60109196847.287D60109446735.313D64280614944.286D64280614944.287D67666003371.313D717153038.313  K10093203181.287K1093189274.311 K12226132804.286K12226132804.287K12406281821.286K12406281821.287K12719279130.311K13517334159.311K16483843482.311K16863439631.311K17397425005.287K18972714752.312K1945250781.286 K1945250781.287 K19727149789.286K19727149789.287K20040736922.311K20981739667.311K23551032557.287K2431698795.287 K26389978266.311K27222706653.286K27222706653.287K30840574317.287K30993319891.313K33674735898.311K37953334125.287K38603332111.311K41744454554.311K42157607183.311K44164039966.286K44164039966.287K45300827802.311K45507919247.311K45578736733.286K45578736733.287K48924907741.286K48924907741.287K49064812687.311K49655786511.311K49978975725.287K52308700509.286K52308700509.287K52576198765.287K52829345295.311K58743820992.312K59993490141.286K59993490141.287K60822670701.287K62527904282.311K62860102458.313K63150298333.286K63150298333.287K65858155712.311K9136277101.287 K9368417295.311 K9840090748.287 L10091109645.2  L1030661972.167 L10323825918.83 L1041429731.83  L10663055041.87 L1103920410.2   L11333811117.3  L12221849778.2  L12271194856.1  L12410523051.2  L12729978778.2  L12969013307.167L13334634337.2  L13513501977.2  L13529531805.90 L14098513515.71 L14447004729.2  L14636542328.2  L15756275188.83 L15844971277.83 L15951833776.167L15953618141.274L1617159359.71  L16482024986.2  L1685717371.0   L16876183705.2  L17086144993.2  L17382748301.2  L18959903894.2  L1932750891.2   L19405429046.83 L19714617643.2  L20038394650.2  L20546686880.3  L20977711877.2  L21222158738.167L21230010724.3  L21791022168.87 L21866712442.1  L22159243031.71 L23082226047.83 L23182876091.2  L23540543245.2  L24054617783.1  L2419170461.2   L24882004373.71 L26186798411.2  L26375085850.2  L27111942217.1  L27218465323.2  L27650499371.1  L29375747288.2  L29680655011.1  L29774146353.3  L30507144274.2  L30731637089.2  L30851056269.2  L30929952171.1  L30997223346.3  L32361341480.1  L33685467802.2  L33740837294.0  L34093934305.2  L3482382239.83  L35098291383.1  L35115138294.71 L35455319922.2  L35655538583.72 L35915999813.83 L36533104100.167L3740020506.87  L37963823245.2  L38109584849.167L38235734261.1  L3849235095.71  L38591107481.2  L40419466676.1  L41114181949.83 L41202929119.275L41755152410.2  L42145383065.2  L42358752225.2  L44061217931.2  L44168158952.3  L44168742175.3  L44470039462.167L44471926219.274L45121863851.1  L45311526170.2  L45512275481.2  L45574590379.2  L46106660189.2  L48121417749.2  L48842827546.274L48937534251.2  L49068649241.2  L49651296153.2  L49964299789.2  L50678314462.3  L51578009499.1  L52296038059.2  L52565717901.2  L52783746038.87 L52816403865.2  L52836486813.90 L53224598113.2  L53271535775.275L53504509255.274L53888385548.83 L54261998223.2  L55114843957.83 L55343106074.275L55826019809.2  L56847218714.1  L57933456208.303L57935548298.302L58342748128.71 L58747656534.2  L58972627787.83 L59980994859.2  L60828966541.2  L6106346273.0   L61207844268.83 L61310511514.275L61594246709.167L6198624755.2   L62513011098.2  L62847746220.3  L63162830635.2  L63557664125.2  L64038109431.1  L64179129035.1  L64850595401.0  L65153465678.274L65289245065.284L65693950831.1  L65852273371.167L65862516566.2  L66660965579.90 L66869566433.2  L67070089790.2  L7656564418.83  L7738195705.2   L8470911054.275 L881835912.0    L8821851361.2   L8942138010.167 L9090702513.71  L9134183821.2   L9372385177.2   L9644563342.71  L9835808138.2   N15340698282.312N18792612241.312N26872553873.312N48204456022.312N60733400192.312N66590330291.312O11135157987.313O11169429742.311O12232075104.311O1261297262.311 O13443133934.311O14559438816.311O14664926154.311O14912726833.311O18086641154.313O18988691132.311O19311540702.310O22525005962.311O25627060590.311O25722042592.311O25895279840.311O26607118461.311O30870739931.311O31855893893.311O33254904445.311O33655933768.311O3493317847.311 O35563760509.311O37559489567.313O4028702351.311 O42178264558.311O4257610376.312 O43490832480.311O4485969646.311 O46148948448.311O47747662589.311O48233649620.311O50011839873.311O50038152189.311O52019636960.311O52086365294.311O53951749322.312O54421585546.312O55539665277.311O56496609880.311O57620671869.311O62222087037.311O64266106862.311O66521921705.310O66725143264.311O6754613856.311 O67738280189.311O6778540014.311 P11331234058.311P13323636166.311P14461423358.286P14461423358.287P14639119327.311P17087673158.311P20539858183.313P21231604675.310P23170010975.287P26175735788.312P29767350678.310P30511339222.311P30724801478.311P34103948358.311P35461131733.311P42348810566.311P44067980844.311P46116577274.311P50671478649.311P53226125510.311P54268551240.287P55827605318.311P6202460773.311 P63564427226.311P66862729542.311P67064334489.311P7750690063.286 P7750690063.287 P8811845190.311 Q10636937134.313Q10639328735.283Q10649498890.284Q10752139055.286Q10752139055.287Q11697867869.283Q13728816866.283Q16423463334.284Q17027695041.313Q17701933584.284Q17757173815.283Q17757173815.284Q22647423948.283Q23170048734.313Q23833424641.286Q24582091142.313Q27663313085.313Q27726666371.313Q28496781288.286Q28498761192.287Q28694295695.313Q32681607669.313Q32681824661.286Q32681824661.287Q34671242405.282Q36508117400.313Q37216054521.284Q37640988321.286Q39460178071.313Q39600066516.284Q40686361676.283Q40904410655.313Q40916972731.284Q42439168719.313Q42439443119.286Q42439443119.287Q43204903389.283Q43507281668.313Q4451634193.287 Q4453582353.286 Q45357732960.283Q46794843979.313Q46922786263.286Q46922786263.287Q48117823211.286Q48117823211.287Q48118064779.313Q49698585326.284Q49698585326.285Q49746198710.313Q49746415830.286Q49746415830.287Q520211124.282  Q52744951088.285Q52744951088.286Q52747231024.286Q52747231024.287Q53354853794.286Q53354853794.287Q54386358946.313Q55408699622.313Q55943643907.313Q57426677977.313Q60529412798.287Q61556549392.285Q61847600945.284Q65188245677.313Q65424847505.285Q65424847505.286Q65426765969.286Q65426765969.287Q67038703949.313Q67038978349.286Q67038978349.287Q68013150533.286Q68013150533.287Q7136501407.313 Q8699115497.286 Q8699115497.287 Q8699324297.313 Q9153544378.313 Q9356559660.290 Q9644583048.313 00000400800Y02002g02h02i02j02k02l03c04D04e06206b07U08U09?09o0:b0:c0;D0<50<P0=90=e0>O0?<0?W0@20@M0@h0AY0B30B]0CJ0D40Da0E<0EV0FG0G70GR0H<0Hi0IZ0J50JP0KA0K\0L70LR0M<0N40NO0Nj0OT0PA0Pk0QX0R30RN0S?0Si0TV0UG0Ub0V<0Vf0WS0XD0X_0Y:0Yd0ZQ0Zk0[\0\70\g0\h0]H0^m0_J0a[0a\0a]0a^0ab0ac0ad0c00c10c20eD0e\0e]0e^0h<0h^0jh0m>0oS0oT0oU0oV0oW0oX0oY0oZ12;12<12=12>12?12@12A12e12i14l15E15F15G15K15L15j15k15l16016116516=16B16C16D16E16F16J16K16O16P16Q16R18[18\1911921:d1;A1;B1=X1=Y1>]1>a1@[1@\1@`1A=1A^1A_1A`1Aa1Ab1Ac1Ad1Cn1FD1FH1FI1FJ1FK1FL1FT1G51G61G71G81G91G:1G>1G?1G@1Gm1Gn1JC1JD1Je1KF1K^1K_1Mf1NG1NH1NM1NN1NO1Nd1Ne1OB1OC1OD1OE1Ob1PC1PD1PE1PF1PG1PH1PI1PM1PN1PO1Q01QV1QZ1Q[1Q\1RB1RC1RD1TK1TL1Tm1Tn1To1U01UL1UM1UN1Uf1Ug1V@1VA1VZ1W;1X51Y?1Y@1YA1YB1YC1YD1YE1YF1YG1YH1YI1YJ1YK1YL1YM1YN1YO1YP1YQ1YR1YS1YT1YU1YV1YW1YX1YY1YZ1Y[1Y\1Y]1Y^1Y_1Y`1Ya1Yb1Yc1Yd1Ye1Yf1Yg1Yh1Yi1Yj1Yk1Yl1Ym1Yn1ZM1[L1\W1]e1^a1_`1`^1aZ1bd1c`1db1eV1fU1gT1gU1hT1iP1ik1jJ1kI1l[1mZ1nN1oJ20I21E22H23N24M24`25325F25G25H25[25n25o26B26U26n27G27Z27[28H29@29S2:R2;;2;d2;e2;f2;g2;h2<;2<N2<h2=`2=a2=b2>52>62>72>R2??2@62@I2@J2A32A\2Ao2BB2BC2BD2CJ2DS2EG2Ec2F?2Fh2Gc2Hh2I;2I]2JB2Jd2KI2KJ2KK2LG2Lb2Lc2MP2MQ2Mm2Ng2O;2O]2PB2Pd2QI2RA2SK2T_2UP2VH2V[2W^2Xk2Y\2ZX2[12[GS2PPS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13Lw12q12HB5Ha_st5Hl_stFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13Lw12q12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12q12HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp13Lw12q12HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12q12HB5Ha_st5Hl_stFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_stS2LF3BUF2bs4LFB33LFB2FB3APB2q12HB5Ha_st5Hl_st2PP3DPB3Lw1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3BUF2bs4LFB33LFB2FB3APBS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APPS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APP3Lw12q12HB5Ha_st5Hl_stFS2sp2PP3CRT2bs2FB3sp13Lw12q13LR1S2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e43HE4S2sp2PP3CRT2lo2bs4PPLO2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HE43HBP3LR12q23Hq2FFFS2FBFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R3Lw12q12p03HP03HQ03LR1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2S2sp2PP3CRT2lo2bs2FB3sp1FFS1R2sp2PP3CRT1P3END3BUF2lo3slo2bs3PP02B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13APP3APC3SPR3ALO2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP02B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP14SP1M3APP3APC3SPR3ALO3ACV2F03APB4SLOu3D1u4DXBu4SP1RFSFFFFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1FFFFFFS2sp2PP3CRT2bs2D12FB3sp13D1u3Lw13LR1S2FBS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP02B12B22B33DPB4CRT03DXB2D14SLOL2FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp13APPFFS2FBFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FFS2PPFS2FBS2sp3sp1S3CRTFFFFS2FBFS2FBFSFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1FS2sp2PP3CRT2bs2FB3sp1FS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs2FB3sp13APBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2FS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R2q12p03HP03HQ0S2loS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RFS2FBS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S2FBFFFFS3Lw12q1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u3Lw12q12e42q23Hq2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2bs2FB3sp12F0FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS3sp1FFS2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT3BUF2bs3B472FB3sp1FFSS2sp2PP3CRT2lo2bs2FB3sp14FBLOS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFFS2FBFSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11i2HiS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rb3RRb2RNFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SFFS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS2sp2PP3CRT2bs2FB3sp12F0FS2LF2bs4LFB33LFB2FB3x341CFS2LF2bs4LFB33LFB2FB3x341CS2LF2sp2bs4LFB33LFB3sp13SP13x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu3x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF2lo2bs4LFB33LFB2FB3sp14FBLOS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu3Lw12q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2sp2bs4LFB33LFB3sp13SP1S2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu3Lw12q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBFS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FB2F02HBS2LF2bs4LFB33LFB2FB2F02HBS2LF2bs4LFB33LFB2FBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stFFFFS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFB3PP02HBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS2LF2bs4LFB33LFB2FBFFS1R2LF3slo2bs4LFB33LFB4SLOSS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_stS1R2LF3slo2bs4LFB33LFB4SLOS2FB2q12HB5Ha_st5Hl_st2PP3Lw1S2LF2bs4LFB33LFB2FBFS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOuS2LF2bs4LFB33LFB2FB2HB5Ha_stS2LF2bs4LFB33LFB2FB2HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPcS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12q15HTOPc2HB5Ha_st5Hl_st2PP3Lw1S2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOuS2LF2sp2bs4LFB33LFB3sp13SP1FS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS2LF2bs4LFB33LFB3sp1S2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2q12HB5Ha_st5Hl_st2PP3Lw1S1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_st3Lw1S2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12q15HTOPc2HB5Ha_st5Hl_st2PP3Lw1S1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2bs4LFB33LFB3sp14SP1RS2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT GB OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma mid_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd Lw1 op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q1 p0 bp e4 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s9v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd Lw1 op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q1)] ->
    P <= p0 -> p0 < q1 -> q1 + bv_unsigned Lw1 <= e4 -> e4 <= ENDX -> BUD hc Lx bp -> P <= bp <= p0 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e4) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) s9v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaa95c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQL HE4 HBUD HBP KLOOP.
    pose proof (bv_unsigned_in_range 64 Lw1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    open_xinv_mu INV hc.
    replace Lw1 with (Z_to_bv 64 (bv_unsigned Lw1)) in FLOCc by (apply Z_to_bv_bv_unsigned).
    assert (OSL : aobj asegs AL (hcs asegs R HIA hc) mm (sp1 - 48) (8 * Z.of_nat 1)).
    { pose proof SS1 as SSx. destruct SSx as (_ & _ & SSg).
      eapply aobj_of_zero_shadow with (B := sp1 - 48) (A := sp1 - 48) (g0 := 0%nat) (n := 1%nat) (cs := [C1 (Z_to_bv 8 0)]);
        [ exact CSOKc | eapply crange_sub; [exact SCS1c| xl| xl] | xl | xl | apply SSg; xl | intros i Hi; destruct i as [|i]; [reflexivity| lia] ]. }
    change (8 * Z.of_nat 1) with 8 in OSL.
    (* [comment removed for export] *)
    do 16 zstep.
    idtac "MID-A".
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?e)] |- _ => replace e with (q1 + bv_unsigned Lw1) in H by (clear; lia) end.
    lazymatch type of FLOCc with rw_cells _ _ _ [_; _; C4 ?tgw; _; _; _; _; _; _; _; _] => set (otg6 := tgw) in FLOCc; clearbody otg6 end.
    fold_xinv INV1 hc Lx X (FLOC lenw j1 otg6 opd (Z_to_bv 64 (bv_unsigned Lw1)) (Z_to_bv 64 q1) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    assert (OCRIT : aobj asegs AL (hcs asegs R HIA hc) mg (FB + 128) 4).
    { eapply (aobj_of_part_shadow_sh asegs AL (hcs asegs R HIA hc) mg FB _ (FB + 128) 16%nat 4 CSOKc FSH);
        [eapply crange_sub; [exact CFBc| clear; lia| clear; lia]| exact F8| xl| clear; lia| clear; lia| reflexivity]. }
    chunk_split FLOCc 7%nat FLa FLb. chunk_split FLb 1%nat FCR FLc.
    replace (FB + 32 + 96) with (FB + 128) in * by (clear; lia). replace (FB + 128 + 4) with (FB + 132) in * by (clear; lia).
    pose proof GB as SPB. unfold asn1_get_bool_stmtA, A_ASN1_GET_BOOL in SPB.
    idtac "MID-GB".
    acallxA_sp sp1 (eapply SPB with (CS := hcs asegs R HIA hc) (PP := PP) (VALP := FB + 128) (P := q1 + bv_unsigned Lw1) (END := e4) (BUF := BUF) (bs := bs) (lo := lo) (valv := crit);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ exact OCRIT | exact FCR | solve_crange | xl HP0 HQ0 HQL HE4 EX1 EX2 LR1
                         | match goal with |- ?g => idtac "GB-LEFT:" g end ]).
    clear SPB.
    idtac "MID-GB-BACK".
    match goal with H : rw_cells _ _ (FB + 128) [C4 ?cv] |- _ => rename cv into crit2; rename H into FCR end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rb end.
    match goal with H : _ < rb <= 0 |- _ => rename H into RRb end.
    match goal with H : _ <= q2 <= e4 |- _ => rename H into Hq2 end.
    joinc FLa FCR. joinc FLa FLc.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg6 opd (Z_to_bv 64 (bv_unsigned Lw1)) (Z_to_bv 64 q1) j2 crit2 j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K98; zify_cond K98.
    { idtac "MID-NOBOOL".
      eapply octet_walk with (q := q2) (p0 := p0) (bp := bp) (e4 := e4) (OL := bv_unsigned Lw1) (OP := q1);
        first [ exact INV2 | exact KLOOP | eassumption | xl HP0 HQ0 HQL HE4 EX1 EX2 LR1 Hq2 HBP | match goal with |- ?g => idtac "MID-OCT1-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. if_cases Kb; zify_cond Kb.
    { idtac "MID-GB-ERR".
      assert (RN : rb <> 0) by (clear - Kb RRb; intros ->; apply Kb; reflexivity).
      eapply err_walk with (rg := rb) (p' := q2) (bp := bp);
        first [ exact INV2 | eassumption | xl HP0 HQ0 HQL HE4 EX1 EX2 LR1 Hq2 RRb RN HBP | match goal with |- ?g => idtac "MID-ERR-LEFT:" g end ]. }
    idtac "MID-BOOL".
    eapply octet_walk with (q := q2) (p0 := p0) (bp := bp) (e4 := e4) (OL := bv_unsigned Lw1) (OP := q1);
      first [ exact INV2 | exact KLOOP | eassumption | xl HP0 HQ0 HQL HE4 EX1 EX2 LR1 Hq2 HBP | match goal with |- ?g => idtac "MID-OCT2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0>60@C17025492443.314C23922862675.315C40860242540.359C40860242543.335C54716835444.360C60407910007.336D10051067940.295D10639034249.360D10639034250.336D12007639820.360D15167092818.295D15181789897.315D16069757089.360D16069757090.336D16899842713.360D16899842714.336D21198918766.360D2455419791.336 D24860224160.316D27847976046.315D32118226965.316D32456773204.336D39172463691.316D39245671661.336D45941514153.360D46792746860.360D46792746863.336D56525861611.295D56536395888.315D57793146470.316D5977889584.295 D5984197035.315 D60109446735.315D60111543912.360D60111543915.336D62557220311.360D6359981838.315 D66239447338.336K10528470632.358K1091092157.358 K1091092158.334 K11279907944.358K12226132804.316K12406281821.316K12717182013.358K12717182014.334K16485940669.358K16485940670.334K17014758123.334K18289619279.315K18774905704.358K1945250781.316 K19727149789.316K20042834109.358K20042834110.334K20983836852.358K20983836855.334K21848089679.315K24525519339.334K24934862056.358K25612096975.315K25644846817.315K26387881149.358K26387881150.334K27222706653.316K2725917647.315 K27871617643.334K28083989739.334K29380230238.336K29718646631.360K30995417076.360K30995417079.336K33672638781.358K33672638782.334K35305884239.315K35791180904.358K40515338856.358K41742357437.358K41742357438.334K42311579883.334K42628394703.315K44073300328.358K44164039966.316K45298730685.358K45298730686.334K45578736733.316K48924907741.316K49807106027.334K50870635471.315K51307378141.360K52308700509.316K53363475179.334K54998166884.336K56709592939.334K59993490141.316K62299668967.360K62525807165.358K62525807166.334K63150298333.316K64331061711.315K64816380904.358K65584587240.358K65856058596.336K65856058599.359K67778271595.334K67886910671.315K6992036218.315 K9992062130.315 L10079012065.2  L10166012279.1  L10526539225.2  L1066678333.2   L1074142290.76  L11035350155.2  L1103920410.2   L11285837785.2  L12221849778.2  L12252132089.3  L12366868378.304L12410523051.2  L12729978778.2  L13176305223.2  L13236461722.304L13636442081.2  L13947844548.3  L14371014045.81 L14371014045.87 L14402536676.3  L14402536676.326L14402536676.349L14447004729.2  L14508908083.2  L15822417165.1  L15934535645.1  L16357593602.195L16357593602.324L16482024986.2  L16772787627.1  L1685717371.0   L17025536345.2  L1717856206.195 L1717856206.324 L17618613065.87 L17901108232.82 L18301909721.2  L18491248361.82 L18503839381.76 L18560700843.1  L18789947609.2  L19103996075.1  L1932750891.2   L19698382006.76 L19714617643.2  L19965341035.71 L20038394650.2  L20977711877.2  L21122558689.2  L21218866939.2  L21222559510.195L21230010724.3  L21654730866.2  L21814628209.3  L21860380633.2  L21866712442.1  L22212138180.3  L22941438733.1  L2396446490.195 L23978865473.195L24023900370.0  L24514671193.2  L24796913220.3  L24882004373.71 L24945510233.2  L25582886452.76 L25608068697.2  L25639998743.2  L2621559066.1   L26375085850.2  L27111942217.1  L27218465323.2  L2730473561.2   L27803524787.2  L27817441514.287L27817441514.288L27832386217.310L27877616089.2  L27938656629.76 L27942859017.82 L28068947801.2  L29391009772.3  L29680655011.1  L29719275082.82 L29724706006.2  L30222833085.292L30507144274.2  L30997223346.3  L31116369961.87 L31320619992.2  L32749673313.2  L32755215223.1  L32866598340.3  L33685467802.2  L3480346272.82  L3484548828.76  L35234028077.82 L35246619217.76 L35309781465.2  L35655538583.72 L35797835737.2  L35905575802.82 L35918166790.76 L36279126350.311L36307103329.2  L36463206329.4  L37221859762.82 L38235734261.1  L39263166881.0  L39327145395.82 L39432216734.82 L3949650929.3   L40058613985.2  L40228640085.0  L40500365785.2  L41112145922.82 L41116348542.76 L41202929119.325L41251426164.1  L41409160545.3  L41755152410.2  L42157884193.0  L42296603481.2  L42411609006.0  L42488948659.2  L42615973209.2  L42747432695.1  L42888316781.71 L42932240884.1  L43315436156.76 L4370579368.1   L43927446468.3  L44058852057.2  L44168158952.3  L45176358486.87 L45311526170.2  L45574590379.2  L4606099115.1   L46301709303.1  L47200528500.1  L47289743172.3  L47441473005.3  L47870616696.2  L47904391685.195L48022350876.311L48843152936.1  L48937534251.2  L49207136770.3  L49233373885.2  L49800647769.2  L50065846443.87 L5021251703.1   L50678314462.3  L50770721805.195L50770721805.82 L50883575897.2  L50925318027.2  L51318226540.3  L52296038059.2  L52941874306.3  L53357021529.2  L53506586030.324L53530411688.1  L53704106081.2  L54390426909.81 L54504511085.3  L55008356054.2  L55085943702.3  L55180717646.76 L55342919976.1  L5660843561.76  L56664292285.2  L56719719641.2  L5685787249.3   L57016247721.71 L57083180513.2  L57387251023.76 L57394714052.3  L576250137.325  L58800644485.71 L58974794248.76 L58987369076.82 L59308586248.2  L59980994859.2  L6008604205.3   L60558678699.1  L61310308520.1  L61594099889.195L61643025177.87 L61774255627.2  L61778427895.1  L62275882349.3  L62306126422.2  L62353614618.87 L62417043471.81 L62417043471.87 L62513011098.2  L6266671209.195 L62873986039.1  L63162830635.2  L64009471222.1  L64179129035.1  L64335090265.2  L64686745924.3  L64818164174.304L64822898777.2  L64850595401.0  L65331221217.2  L65594780249.2  L65642230468.3  L65862516566.2  L66298372189.2  L66812728480.3  L66925338641.289L67070089790.2  L67763426009.2  L67891464025.2  L6979816172.3   L7244092893.3   L7484103457.0   L7738195705.2   L8136662222.304 L8171953640.287 L8171953640.288 L881835912.0    L8941784094.195 L9090702513.71  L9225258773.333 L9476030541.71  L988506752.82   L9988165412.2   N10400473443.315N14342935073.315N15139586140.359N21881295695.359N23667955994.335N25297080393.335N29731080008.315N34470429922.335N34515723252.315N34870951589.335N38481866511.315N4182430466.315 N4217864246.359 N47900433899.359N54376292405.359N59706724824.335N62331351520.359N63610817641.335O10378001882.358O12233548996.315O12234172228.334O12234172231.358O14175554244.315O14561535940.334O14561535943.358O1478916974.315 O14914823957.334O14914823958.358O153857113.334  O15542962377.358O15542962378.334O16088123372.336O16620552189.315O16726028505.334O17025492443.314O17044154330.358O17758872154.358O18990788248.334O18990788251.358O20059408765.315O20458779460.315O20868868134.336O21056028233.358O21056028234.334O22138318205.315O22527103149.359O22527103150.336O22557709658.358O23922862675.315O24352547140.315O2465310041.334 O24725892297.358O24725892298.334O25719945412.334O25719945415.358O25893182660.334O25893182663.358O28802357117.315O29946971610.358O30012554411.334O3078286936.315 O31587119912.358O32216486618.358O33083286018.315O34052634180.315O34616242905.334O3491220720.358 O3491220723.334 O37557392440.360O37557392443.336O37858732889.334O3823870404.360 O3823870407.336 O38899942618.358O40034824061.315O40562546687.358O41224416250.333O426448880.334  O43492929604.334O43492929607.358O43849271089.315O44940300028.358O44940300031.334O45421758793.358O45421758794.334O45947445700.315O46146851268.334O46146851271.358O4721118921.358 O4721118922.334 O47737000900.315O48262126959.360O4864412762.358 O49074864073.358O49074864074.334O49585648037.360O49699726460.334O50009742757.334O50009742758.358O50401764781.360O50689527441.315O5099699757.360 O51150049554.315O52021734084.334O52021734087.358O52218726141.315O53449798340.315O55211981985.334O55211981986.358O55518239188.314O55741014473.358O55741014474.334O56414299794.315O57734935677.315O57957320900.315O58998754777.334O59625529265.315O59918789977.334O60978474237.315O61254571849.358O61254571850.334O63529321950.313O64249863214.336O64417349245.315O64471909101.358O64471909102.334O65469896563.358O65963309679.359O66524018829.333O66524018830.357O66723046084.334O66723046087.358O66812877810.315O67171060367.315O6756710980.334 O6756710983.358 O6817896025.334 O6971443577.357 O7859127258.358 O8876279497.358 O8876279498.334 O9123606361.334 P10066941537.358P10066941538.334P1063054013.358 P11023336971.360P12257878110.315P13623313761.358P13623313762.334P13953656163.315P14461423358.316P14498256258.358P1637532236.318 P21135652961.358P21135652962.334P21212095580.314P21233701860.357P21233701863.333P21649959665.334P21649959666.358P21821398486.313P22197995107.315P24812063971.315P25644846817.315P27816465701.315P30513436401.358P30513436402.334P324046647.294  P324046647.295  P324046647.318  P32761743841.358P32761743842.334P32881815395.315P36320230625.358P36320230626.334P36465839390.315P38605639612.294P38605639612.295P38605639612.318P3953275249.357 P40053842529.358P40053842530.334P41419110342.315P42487016449.334P43934249315.315P47284020707.315P47436775277.358P47874275064.358P47874275067.334P49191944357.315P49211061452.294P49211061452.295P49211061452.318P49228642366.334P50673575773.334P50673575774.358P50930023691.359P52940256805.315P53717201633.358P53717201634.334P54497641674.314P55088519473.315P56666925338.315P5673773298.333 P57086895969.358P57086895970.334P57379456867.315P61786326152.336P62262763502.334P64680999907.315P65343291489.358P65343291490.334P65640603747.315P66294657757.358P66294657758.334P66816411168.360P66816411171.336P67066431677.334P67066431678.358P7740881908.294 P7740881908.295 P7740881908.318 P7750690063.316 P7903954312.294 P7903954312.295 P7903954312.318 Q10024872496.312Q10195749203.289Q10592318618.281Q10592389157.333Q10594415773.315Q10594630297.336Q10598528537.310Q10637079862.333Q10639034249.360Q10639034250.336Q10639171022.278Q10649498890.334Q10821824020.294Q10821824020.295Q10821824020.318Q11093001477.289Q11135471355.336Q11659151019.336Q11796756721.289Q11988014288.288Q12658605510.294Q12658605510.295Q12658605510.296Q12658605510.297Q12658605510.318Q12658605510.320Q13241170297.291Q13731016203.333Q14143836712.360Q14705649756.284Q14742886208.360Q14751535315.289Q15258109527.316Q15616052641.312Q15766564435.315Q15944836594.288Q16069757089.360Q16069757090.336Q16180832188.336Q16355141072.288Q16909570643.289Q17025597925.336Q17025597926.360Q17558758360.290Q17683171741.360Q17683171742.336Q17701933584.334Q17716263636.278Q1895155614.313 Q1897215223.333 Q19546780655.333Q19561677163.289Q19561680339.310Q19955343048.360Q19955343051.336Q20187357108.333Q20517146075.291Q21365000441.313Q21765573509.360Q21765573510.336Q21797099320.312Q22374337363.289Q22516600531.289Q23232684382.286Q23441368885.312Q23613318552.315Q2363337691.291 Q24257074651.291Q24862400672.315Q25166423590.294Q25166423590.295Q25166423590.318Q25166729441.360Q25166729442.336Q25168511142.316Q25168826566.315Q2605063902.315 Q26314584654.294Q26314584654.295Q26314584654.318Q26316671538.275Q26318654066.315Q26432625456.360Q26729481055.285Q26892573131.279Q27118626695.312Q27575848480.336Q27575848483.360Q27665131166.312Q27863312744.333Q27865799639.360Q2805923721.336 Q2805923722.360 Q28449463941.334Q2863532638.286 Q28666805532.314Q29097057975.313Q29322743127.360Q29324722152.333Q29732604428.274Q29778078657.360Q29778078658.336Q30265210969.313Q30319892460.312Q30387997187.333Q30441621865.280Q30645011775.360Q31124869336.315Q31339371283.289Q3166354565.334 Q32437204119.315Q32452805332.310Q32456773204.336Q32457080912.315Q32459013352.333Q32679510481.336Q32679510482.360Q32681607669.315Q32681824661.316Q32959886801.287Q3317830712.314 Q3339752862.281 Q342032561.312  Q34268448600.290Q34363165844.315Q3444200401.287 Q34667034333.313Q34669522109.315Q34671389857.289Q34877581972.289Q34952600272.288Q34964382778.315Q35164442047.360Q35378271416.312Q35895740379.291Q36652444704.315Q36759522011.291Q36768752385.333Q36983025188.360Q36983025191.336Q37039215513.315Q37065061723.291Q37654045871.316Q38555981400.290Q39328755025.287Q39408379774.284Q39600066516.334Q39885187281.314Q40332524508.284Q40513116131.312Q40586814278.309Q40686657050.360Q40688626853.333Q40906507832.360Q40906507835.336Q40916972731.334Q40974010456.290Q41527591263.315Q41635797459.289Q4174339024.288 Q42295909976.290Q42301876062.315Q42352164051.312Q42439168719.315Q42439443119.316Q42441265896.360Q42441265899.336Q42441548847.294Q42441548847.295Q42441548847.318Q42757159386.310Q44113183171.336Q44298944140.275Q44298944140.290Q44298944140.310Q44298944140.313Q44301027056.294Q44301027056.295Q44301027056.318Q4473570896.288 Q44876980066.289Q45439978169.315Q45445507793.287Q45482765142.296Q45482765142.297Q45482765142.320Q45742292654.312Q45806042497.333Q45904387664.315Q46591526104.290Q46792746860.360Q46792746863.336Q47061991091.315Q47375526168.314Q47549834995.312Q47604779231.314Q48117823211.316Q48118064779.315Q48119910507.294Q48119910507.295Q48119910507.318Q48120161964.360Q48120161967.336Q48189903665.312Q48234175664.315Q48360113622.315Q4845047677.285 Q49494258259.312Q49698585326.314Q49746198710.315Q49746415830.316Q49748295825.360Q49748295826.336Q49748522582.294Q49748522582.295Q49748522582.318Q50324780992.360Q50445979747.312Q51379872473.289Q51653344654.333Q51959565846.280Q52387815135.285Q52690940469.290Q52690940469.310Q52747231024.316Q53317345084.336Q53328907473.287Q53466943967.315Q53581667916.312Q53678142858.312Q53774309119.283Q53850310965.313Q54196455217.289Q54196504185.309Q54200699147.289Q54295544543.314Q54785822014.289Q54856420359.312Q55401488351.315Q5540636085.313 Q5596578838.294 Q5596578838.295 Q5596578838.318 Q56186208347.291Q56452622865.315Q56454570001.316Q56525680748.289Q56533073587.336Q56536395888.315Q56538360336.313Q56900949851.291Q57209973095.315Q57830202365.336Q57830202366.360Q5857658577.314 Q58972088534.282Q59391892184.290Q59422879440.315Q59617550414.312Q59617553652.289Q59621696206.289Q59621745542.309Q59991740767.285Q60316513700.360Q60316513703.336Q60422877723.313Q60746685720.315Q6126053922.316 Q6134922490.336 Q61500136060.286Q61543209836.312Q61847600945.334Q6190817072.336 Q6190817075.360 Q6191098356.294 Q6191098356.295 Q6191098356.318 Q6192914196.315 Q6193188724.316 Q62380812747.315Q62555250536.333Q62557220311.360Q62603800435.287Q62635101267.289Q63236532495.312Q63435846322.290Q63435846322.310Q63435846322.313Q63488537438.286Q64228675114.293Q64228675114.294Q64228675114.317Q64411644381.283Q65430079568.288Q6562449867.309 Q65892967672.360Q66901779611.290Q66901779611.310Q66901779611.313Q66922076282.290Q66995821912.290Q67028497104.279Q67038703949.315Q67038978349.316Q67040801129.336Q67040801130.360Q67041068973.294Q67041068973.295Q67041068973.318Q67126152652.274Q68011063237.294Q68011063237.295Q68011063237.318Q68013150533.316Q6824367933.310 Q68336587110.333Q6912043752.282 Q705497310.286  Q7830203611.291 Q8126701711.315 Q8626407545.360 Q8699115497.316 Q8699324297.315 Q8701202793.294 Q8701202793.295 Q8701202793.318 Q8701421485.336 Q8701421486.360 Q9356559649.295 Q9356559674.313 Q9356559674.337 Q9633866796.310 Q9633867924.289 Q9644448272.333 Q9644583048.315 Q9646680236.336 Q9646680239.360 00000100200600:00>00B00j01R02:02;02<02=03[05906M07a07b07c08Z0:10:20:Z0:[0:\0;D0;l0<T0=<0=d0>[0>\0>]0?N0@?0A00AX0B@0Bh0CJ0Cl0DN0E00E`0FQ0G30GU0H70HY0I;0I]0J?0K00Ka0LC0Le0MF0Mg0NI0Nk0OM0Oo0P00PR0Q40Qe0RG0Ri0SK0Sm0TN0U00UR0V40VV0W80WZ0X<0X^0Y@0Yb0ZD0Zf0[W0\90\[0]L0^=0^_0_A0_c0`T0a60aW0b90bj0cK0cm0dO0e@0eb0fD0ff0gG0gh0hJ0hl0iN0io0j00j10j20j30j[0j\0j]0j^0j_0j`0kH0kI0kJ0kR0l:0l;0l<0mg0o^0oi0oj0ok0ol0om10110412714M14N14R14S14T16N18[1:h1<l1<m1?o1B[1B_1B`1Bd1Be1DS1DT1FA1FB1FC1FD1FE1FF1FG1FH1FI1FJ1FN1FO1FS1G[1G\1G]1G^1G_1H=1H>1Ij1Ik1Il1J11J21J61J71J81J91K<1L?1Lg1Lh1O01QN1QO1QP1QU1SY1SZ1T;1T<1T=1Tj1U21U31U71U81U91W?1Xo1[51];1]<1^n1^o1_L1_i1a41a51a61d41d81d91dQ1f;1f<1f=1f>1f?1f\1g91ga1ge1gf1gg1gh1gi1gj1gk1gl1h01hg1hk1iD1iH1iI1iJ1iK1j31j41j51j91j=1jA1jB1jC1jD1kT1kU1kY1kZ1k[1k\1k]1lE1lF1lG1lg1mN1mO1mP1mQ1mR1mS1mT1n<1n@1nA20320420520622^22b24@24A24B24C24X24Y25125225Z27T28128N28T28U28`28d28h28i2;42;52;92;:2;;2;j2<P2=62=72=82=<2==2=>2=?2=@2=A2=i2=j2=k2=l2=m2=n2=o2>02>12>R2>S2>T2>U2>V2>a2>b2>c2?K2?L2?M2?N2?O2?k2@S2A02AI2AJ2Aj2B`2C@2C`2E12EY2F92F:2Fe2GE2GF2Gj2Hk2Hl2J=2J]2KE2LF2LG2LH2LI2LJ2LK2LL2LM2LN2LO2LP2LQ2LR2LS2LT2LU2LV2LW2LX2LY2LZ2L[2L\2L]2L^2L_2L`2La2Lb2Lc2Ld2Le2Lf2Lg2Lh2Li2Lj2Lk2Ll2Lm2Ln2Lo2M02M12M22M32M42M52M62M72M82M92M:2M;2M<2M=2M>2M?2M@2MA2MB2MC2MD2ME2MF2MG2MH2MI2MJ2MK2ML2MM2MN2MO2MP2MQ2MR2MS2MT2MU2MV2MW2MX2MY2MZ2M[2M\2M]2M^2M_2M`2Ma2Mb2Mc2Md2Me2Mf2Mg2Mh2Mi2Mj2Mk2Ml2Mm2Mn2Mo2N02N12N22N32N42N52N62N72N82N92N:2N;2N<2N=2N>2N?2N@2NA2NB2OH2PN2QQ2RT2S:2T@2UF2Uo2WA2X<2Xm2Z32[92[:2\=2]@2]A2]B2^K2_42_]2_^2`Y2aT2bO2cM2dK2eP2fV2g\2hE2iK2jQ2k92kk2l]2mV2n_2oe30k31Q32L33533^34D35G36J37037b38T39M3:P3;63;\3<_3=E3>K3?Q3@73@\3A_3Bh3Cn3E43E]3F`3GF3Go3I53J;3Jd3KF3Kh3Lm3N23O53P83Pi3QZ3RR3S\3Tm3V>3WV3WW3WX3X<3XV3YA3Y[3Z53ZO3Zi3[C3[j3\D3]23]`3^U3^h3_B3_C3_k3_l3`Z3aH3bM3cR3dG3eS3f;3fU3fV3fW3fX3g@3gA3g[3h?3hg3if3je3k?3k@3kA3k[3l53l63m93n<3nV3o=3oh40C41541`42R42S42T42U42V42W43Z44]45745845945:45U45o46046146Z46[46\46]46^46_46`46a46b47L48648g49?49d49e49f4:e4:f4:g4:h4;B4;\4<64<Q4<l4<m4<n4=Y4>94>:4>;4>N4?04?R4?S4?m4@G4AI4Ac4Ad4B74B84B94BS4Bm4CX4D24D34D44D54D64D74D84D\4E64E74E84E94Ed4F>4FQ4Fd4Fe4G`4Ga4Gb4Gc4HL4HM4Hg4Hh4Hi4Hj4Hk4Hl4Hm4IU4J=4J>4Ji4KQ4Kk4LE4L_4M94M:4M;4M<4M=4M>4M?4M@4MA4Ml4NF4Nh4O\4P>4P`4QS4RF4S@4SA4S[4T34TK4Tj4UI4V34V]4WN4WO4WP4WQ4WR4XW4Y\4Zh4[B4[C4[D4[E4[_4\94\:4\;4\V4]A4^N4_I4`U4aa4c44co4dj4dk4dl4eQ4f94fS4g64gf4hh4iX4jH4kI4lJ4mR4ml4nF4nY4o44ok50S50k51J52352452552O52j53E53m54L54_55955L55M55`56:56c56d56e56f56g56h57Q58:58M58N58h59S5:;5:U5;I5<=5<h5=L5>45>55>65>75>85>95>:5?@5@F5@e5@f5@g5@h5AP5Aj5Bk5CF5Ca5DO5E=5F25FM5G:5G\5H65HP5I85I95I:5I;5I<5I=5I>5JN5K^5M55M]5NE5N_5O95OQ5P05PO5Q75Q85RB5SA5TR5UQ5VP5W`5Y05ZG5ZZ5[Q5\H5]F5^>5^X5^Y5_=5_e5_f5_g5_h5a25aj5c35d<5eL5fD5g<5g\5h<5h\5i95iO5il5jI5jf5kCFFS2PPS2PPS2FBS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFFS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2hb3LHBS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBFS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP3BUF2bs4LFB33LFB3DPB2hb3LHBS2LF2PP3BUF2bs4LFB33LFB3DPB2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBFFFFS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFS2lo3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2HpS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Hq04Hq0aS2rg3RRg2KzFFFFS2FBS1lS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21p2Hp2q03Lw03LR04Hq0a4Hq0LS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21p2Hp2hb3LHB2q03Lw03LR04Hq0a4Hq0LFS2FBSFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21p2Hp2q03Hq04Hq0aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21p2Hp2hb3LHB2q03Hq04Hq0aS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21p2Hp2q03Lw03Hq04Hq0a4Hq0L2q13Hq14Hq1aS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS2FBFS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21p2HpFS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1RFFFFFFFFFS2FBFS2FBS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R4ENDX1p2Hp2q04Hq0aFSFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21p2HpFFS3sp1FS2PPFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFFS3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT2bs2D12FB3sp13D1u4ENDX2q03Lw04Hq0LS2sp3sp1FS2FBFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2HpS1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RS1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RFS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2sp2PP3CRT3BUF2bs2FB3sp13APBS2sp2PP3CRT3BUF2bs2FB3sp13APBS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_st5SAEst5CM8st2x32HxFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS2loSS2sp2PP3CRT2bs2FB3sp12F0S2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22q03Lw04Hq0LFFSFS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2FBFFSFSFFS2FBS1R2sp2PP3CRT2bs3PP04CRT02D12FB3sp13SPR3ACV2F13D1u4SP1RS2FBS2sp2PP3CRT2bs2FB3sp13APPS2FBFFFS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFS2FBS2FBS2FBFFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R4ENDX1p2Hp2q03Lw03LR04Hq0aFS2FBFFFFS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFS2sp2PP3CRT2bs2FB3sp12q03Lw03LR0S2sp2PP3CRT2bs2D12FB3sp13D1u2q03Lw03LR0FFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Hq0FFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS2FBS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX2FFFS2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT2bs2FB3sp12F0FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS1R3NS14STKc5STKc22sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2sp2PP3CRT3BUF2bs3B472FB3sp1S2sp2PP3CRT3BUF2bs3B472FB3sp1S1i2HiFS2rg3RRg2KzS2FBS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0L2q13Hq1FS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2q03Lw02q13Lw14Hq1LS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNFFS2FBFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFSFFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2sp2lo3sp1SFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFSFS2sp2PP3CRT2lo2bs2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2sp2PP3CRT2lo2bs2FB3sp14FBLOS2sp2PP3CRT2bs2FB3sp13APPFS2LF2bs4LFB33LFB2FB2hb3LHB3x261CS1R2LF2lo2bs4LFB33LFB3LOS2FB3sp13ALO2hb4SBND3LHB3x261CS2LF2bs4LFB33LFB2FB2hb3LHB3x621CS2LF2bs4LFB33LFB2FB2hb3LHB3x621CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2hb4SBND3LHB3x471CS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHB3x471CS2LF2bs4LFB33LFB2FB2hb3LHB3x261CFS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHB3x261CS2LF2bs4LFB33LFB2FB2hb3LHB3x471CFS2LF2lo2bs4LFB33LFB3sp12hb3LHB3x261CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHB3x621CFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2hb4SBND3LHB3x621CS2LF2bs4LFB33LFB2FB2hb3LHB3x471CS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHB3x621CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHB3x471CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3BUF2lo2bs4LFB33LFB3sp15BUFLO2hb3LHBS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2hb3LHBFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2lo2bs4LFB33LFB3LOS3ALO2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F82hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F82hb3LHBFFFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFFS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFFFFFFFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBS2LF3CRT2lo2bs4LFB33LFB6CRTLOu2hb3LHBFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stFFFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2F02hb3LHB2HBFFS2LF2bs4LFB33LFB2FBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB4SLOu2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFS2LF2bs4LFB33LFB2FBFFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHBFFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstFFFFS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FB2hb3LHBFFFS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBFFS2LF2bs4LFB33LFB3sp12hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBFFS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12hb5HTOPc3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12hb5HTOPc3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB3sp12hb3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBFS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFFFFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1R2hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stS2LF2PP2lo2bs4LFB33LFB4PPLO2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12hb5HTOPc3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12hb5HTOPc3LHB2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F0S2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHB". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma body_walk : forall p, P <= p < ENDX -> (forall p', p < p' -> p' < ENDX -> LoopOblig p') -> LoopOblig p.
  Proof.
    intros p Hp KLOOP. unfold LoopOblig. intros until x31. intros INV HPP HBUD.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 8 zstep.
    idtac "BODY-A".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    frame_aobj FSH (FB + 64) 3%nat as OOID.
    chunk_split FLOCc 2%nat FL0 FL1. chunk_split FL1 4%nat FOID FL2.
    replace (FB + 32 + 32) with (FB + 64) in * by (clear; lia). replace (FB + 64 + 24) with (FB + 88) in * by (clear; lia).
    lazymatch type of FOID with rw_cells _ _ _ ?cs =>
      apply (rw_cells_CB_of asegs mg (FB + 64) cs ltac:(cbn; lia)) in FOID; cbn [cells_size csize Nat.add] in FOID;
      lazymatch type of FOID with rw_cells _ _ _ [CB _ ?bb] => set (hb := bb) in FOID; clearbody hb end;
      pose proof FOID as HBL; apply (u8arr_of_rw_cells asegs) in FOID end.
    assert (LHB : length hb = 24%nat) by (destruct HBL as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    clear HBL.
    pose proof (artA_amemset asegs R HIA 0x68258) as SPM.
    idtac "BODY-MEMSET".
    lazymatch goal with HHx : HM _ _ _ hc ?lbx _ mg |- _ =>
      acallxA_sp sp1
        (eapply SPM with (h := hc) (LB := lbx) (LF := LF') (DST := FB + 64) (v := 0) (n := 24) (lo := lo) (ds := hb);
         rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc;
         first [ exact HHx | exact FOID | exact OOID | eassumption | reflexivity | exact LOS
               | lazymatch goal with
                 | |- _ = arl_amemset R \/ _ => left; rewrite AMS; reflexivity
                 | |- Z.of_nat (length _) = 24 => rewrite LHB; reflexivity
                 | |- crange _ lo _ => exact SCS1c
                 | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
                 | |- _ => xl
                 end
               | match goal with |- ?g => idtac "MS-LEFT:" g end ]) end.
    idtac "BODY-MEMSET-BACK".
    clear SPM.
    (match goal with H : u8arr _ _ (FB + 64) _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; change (Z.to_nat 24) with 24%nat in H; rename H into HZ end).
    (match goal with H : ?x = Z_to_bv 64 (FB + 64) |- _ => subst x end).
    lazymatch type of HZ with rw_cells _ ?mx _ ?cs =>
      pose proof (rw_cells_reshape asegs mx (FB + 64) cs
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] HZ
                    ltac:(cbn; repeat split; reflexivity) ltac:(first [exact eq_refl | vm_compute; reflexivity])) as FOIDz end.
    clear HZ.
    (* [comment removed for export] *)
    do 7 zstep.
    idtac "BODY-B".
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    joinc FL0 FOIDz. joinc FL0 FL2.
    (* [comment removed for export] *)
    do 5 zstep.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    chunk_split FL0 1%nat FLEN FLr. replace (FB + 32 + 8) with (FB + 40) in FLr by (clear; lia).
    idtac "BODY-GT1".
    gt_call OLEN FLEN p ENDX (FB + 32) 48 ltac:(xl Hp EX1 EX2).
    idtac "BODY-GT1-BACK".
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw0; rename H into FLEN end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q0; rename H into HPP0 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q0 <= ENDX |- _ => rename H into Hq0 end.
    pose proof (bv_unsigned_in_range 64 Lw0) as LR0. unfold bv_modulus in LR0. cbn [Z.pow Z.of_N Pos.pow] in LR0.
    joinc FLEN FLr.
    fold_xinv INV2 hc Lx X (FLOC Lw0 j1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) j2 (Z_to_bv 64 0) j3 (Z_to_bv 64 0) j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT1-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (rg := rg) (p' := q0) (bp := p);
        first [ exact INV2 | eassumption | xl Hp EX1 EX2 Hq0 RRg RN | match goal with |- ?g => idtac "BODY-ERR1-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq0a Hq0L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 16 zstep.
    frame_aobj FSH (FB + 72) 1%nat as OOL.
    chunk_split FLEN 4%nat FLa FLb. chunk_split FLb 1%nat FOL FLc.
    replace (FB + 32 + 40) with (FB + 72) in * by (clear; lia). replace (FB + 72 + 8) with (FB + 80) in * by (clear; lia).
    idtac "BODY-GT2".
    gt_call OOL FOL q0 (q0 + bv_unsigned Lw0) (FB + 72) 6 ltac:(xl Hp EX1 EX2 Hq0 Hq0a Hq0L LR0).
    idtac "BODY-GT2-BACK".
    match goal with H : rw_cells _ _ (FB + 72) [C8 ?lq] |- _ => rename lq into Lw1; rename H into FOL end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q1; rename H into HPP1 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q1 <= _ |- _ => rename H into Hq1 end.
    joinc FLa FOL. joinc FLa FLc.
    fold_xinv INV3 hc Lx X (FLOC Lw0 j1 (Z_to_bv 64 0) (Z_to_bv 64 0) Lw1 (Z_to_bv 64 0) j2 (Z_to_bv 64 0) j3 (Z_to_bv 64 0) j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "BODY-GT2-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (rg := rg) (p' := q1) (bp := p);
        first [ exact INV3 | eassumption | xl Hp EX1 EX2 Hq0 Hq0a Hq0L LR0 Hq1 RRg RN | match goal with |- ?g => idtac "BODY-ERR2-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq1a Hq1L]. clear HLg Kz RRg.
    idtac "BODY-MID".
    eapply mid_walk with (q1 := q1) (p0 := p) (bp := p) (e4 := q0 + bv_unsigned Lw0);
      first [ exact INV3 | exact KLOOP | eassumption | xl Hp EX1 EX2 Hq0 Hq0a Hq0L LR0 Hq1 Hq1a Hq1L | match goal with |- ?g => idtac "BODY-MID-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L11764860278.6L23883943945.7L59308587155.500000C00Y00iS4ENDX1k1p2Hk2p'2H1S1P4ENDX1p2Hp2p'2H12H2S1P4ENDX1p2Hk2Hp". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma tloop : forall (k : nat) (p : Z), ENDX - p <= Z.of_nat k -> P <= p < ENDX -> LoopOblig p.
  Proof.
    induction k as [|k IH]; intros p Hk Hp.
    - exfalso. clear - Hk Hp. lia.
    - apply body_walk; [exact Hp|]. intros p' H1 H2. apply IH; [clear - Hk H1; lia| clear - Hp H1 H2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Loop.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0530@D10651567411.267D10836317929.299D12656313659.299D13253490115.267D17704051241.267D24128083136.299D27806942224.305D27806942224.306D32454803565.299D3267863928.299 D35883161687.299D3883966340.299 D39256548052.299D50244182904.306D52043936183.299D54246127327.299D56896494561.267D59473897855.301D60189065437.305D60189065437.306D6205886729.299 D68411668694.299D6899608275.299 D903115207.299  L10178881292.7  L10549786651.2  L1056244802.71  L10837002389.2  L1103920410.2   L1107925502.293 L1107965600.294 L11311055387.2  L11668953649.258L12126572370.2  L12654381620.1  L12729978778.2  L13000859167.71 L13238797400.71 L14402535660.291L14402535660.3  L14662949908.71 L1530387784.71  L15414642072.191L15846663084.71 L16482024986.2  L1685717371.0   L17225908493.1  L19965341035.71 L20038394650.2  L20977711877.2  L21222559353.191L21230010724.3  L21555046091.71 L22147449930.191L22932634144.73 L23581863231.2  L24882004373.71 L25054447057.257L25271426382.16 L26375085850.2  L27325864010.71 L27786096167.113L27796237965.71 L27858612815.3  L28090575245.1  L28632618922.2  L29241073293.1  L29813167690.293L30507144274.2  L30997223346.3  L31873504466.71 L3241370779.2   L32604013069.1  L32896879501.292L32951616581.4  L33685467802.2  L3480690494.71  L35655538625.72 L35822393883.2  L35905690340.71 L36035727278.2  L36963958045.2  L37782719358.160L38056808157.3  L38235734261.1  L38259954321.2  L39166355450.191L40228640085.0  L41112523164.71 L41202929119.258L41202929119.293L41334146114.2  L41755152410.2  L4196854811.2   L43519627435.2  L4354989341.160 L43892210075.2  L44166924249.3  L45311526170.2  L46743867632.71 L46868055498.293L4855685921.0   L48937103345.294L51201023259.2  L51489524058.71 L51500665912.16 L52067411348.294L52758021441.71 L53516896046.292L54318674701.1  L56243510247.191L56468645943.294L56777638818.292L56787775565.191L56902789754.71 L57037598615.71 L57628700040.4  L57692209838.317L57698627611.2  L58987451370.71 L6008603173.3   L60672126733.1  L61286871247.71 L61594100190.191L61626430581.191L61637265306.292L61638990714.293L61639226404.294L62081227363.4  L64205045955.191L64850595401.0  L65110679799.3  L65378998541.1  L65519092066.292L65862516566.2  L67070089790.2  L6713521051.8   L6798276507.2   L7330750477.1   L7696713571.3   L7753760539.2   L8941784433.191 L9090702513.71  L9190709528.5   L9397308949.7   L9817097297.258 P1043593561.299 P10540088028.305P10540088028.306P1106161799.299 P11322327260.305P11322327260.306P12115299733.305P12115299733.306P12732252679.299P16479777671.299P18391008132.299P19974019408.299P20036415111.299P20977680014.299P23095784836.299P26376999559.299P26652418180.299P28627113325.305P28627113325.306P30997907918.299P3252643420.305 P3252643420.306 P32814192132.299P33687453447.299P35832092892.305P35832092892.306P36964055190.299P38056382625.299P38261788758.305P38261788758.306P41334243785.299P41757433223.299P4207603420.305 P4207603420.306 P43677085060.299P43901909852.305P43901909852.306P44164039966.305P44164039966.306P45313542279.299P48371079044.299P51191324636.305P51191324636.306P51927712388.299P57713046236.305P57713046236.306P65862482653.299P6809023836.305 P6809023836.306 P7763983836.305 P7763983836.306 P8676795140.299 Q10048380702.302Q10160764996.306Q10649389620.266Q10649498890.302Q10651584438.301Q1106161799.299 Q11282309114.302Q12555692702.301Q12555692702.302Q12732252679.299Q12933971006.302Q13193308734.302Q13732682891.301Q15985628819.301Q16057206942.302Q16479777671.299Q17701933584.302Q17722859966.302Q18567054366.302Q18826805037.302Q19559354218.299Q20036415111.299Q20977680014.299Q21227806174.299Q23583809698.299Q23829118526.302Q23903427537.301Q24281037434.302Q24592544158.302Q24852143294.302Q25585260574.301Q25816364734.301Q25952160488.304Q25952160488.305Q26376999559.299Q26481470270.302Q27861610229.299Q28465177121.302Q28465177121.303Q29516740158.301Q30506752203.299Q30602945310.301Q30997907918.299Q31619352177.301Q32681824661.305Q32681824661.306Q33687453447.299Q33813839279.302Q33839800254.302Q35702454078.301Q35702454078.302Q36630502558.302Q36964055190.299Q37288026488.302Q37636909982.302Q38056382625.299Q38833220926.302Q38920838907.301Q39180574961.305Q39180574961.306Q39600066516.302Q39824755247.302Q40916972731.302Q41334243785.299Q41757433223.299Q42439443119.305Q42439443119.306Q42639330846.302Q43517348881.299Q43629399377.306Q43649290398.302Q44847628683.301Q44858487396.301Q44860571864.302Q44949809470.302Q45313542279.299Q45353866761.301Q45356129163.266Q45741809296.305Q45741809296.306Q47387953854.302Q48667442078.302Q49625511898.306Q49746415830.305Q49746415830.306Q50246429048.305Q50449559544.302Q50869415908.301Q50871508312.302Q51221331390.301Q519278494.301  Q5265442331.303 Q5265442331.304 Q53796808704.303Q53799279550.301Q53839787668.301Q53915156798.302Q54692959518.302Q55415036769.305Q55415036769.306Q59578101107.301Q60191312605.304Q60191312605.305Q60546513284.303Q60668057790.302Q60703360670.302Q61018498547.301Q61847600945.302Q6205886729.299 Q63209333152.303Q63211573790.301Q64171619443.301Q6530087198.302 Q65862482653.299Q66459454699.299Q66730946590.302Q67028250965.302Q67038978349.305Q67038978349.306Q67068921476.299Q67877090750.302Q8699115497.305 Q8699115497.306 Q8933037170.299 Q9631868565.299 00000Q01601[02<02]03>04f06D06e06f06g06h06i08O09409U0:60:\0<L0>20>S0>T0?50?60?M0?N0?k0@30@40B60D80D90Eh0Ei0En0Eo0Ge0H:0H;0HF0J<0JU0JV0K80K90K:0K?0Ll0Lm0Ln0Lo0M00MN0Mo0NR0NS0O10PK0P[0P\0RT0RU0RV0RW0R\0R]0Rb0SC0SD0SE0Te0Tf0Tk0VE0VS0VT0X60Yh0Yi0ZF0ZO0ZP0[:0[;0[?0[@0\<0\=0\Z0];0]\0]]0]^0]_0]`0^J0^K0^L0^M0^e0_F0_G0_h0_i0aJ0a_0a`0b>0b_0bd0be0cF0eH0g>0gS0iM0iZ0ja0jb0k?0kJ0kO0kd0ke0m]0oa11e13j14715?15@15J15O16i16j16k17D17E17J17T17U17V18218E18\1:K1:j1<E1=V1>11?L1@]1B91CK1Cf1DA1E@1Eb1F=1FW1GV1H11I01JO1Ki1LD1M_1O01Oo1PJ1Qe1S61SQ1Sn1UG1VV1W11WL1Xg1Z81[71\R1]c1_A1`U1a01ao1cJ1d[1eZ1fW1gH1gb1i=1jN1ki1m:1n91o120<20O20b21521621J22B23:23;23h24U24h24i25a25b26526b27Z28G2922932942:02:g2;T2<A2<U2=M2>:2?22?_2@l2Ao2B02B]2C\2D82DT2EA2F52Fm2Fn2Gf2Gg2Gh2Gi2Gj2HW2ID2J12Ji2Jj2Kd2L\2L]2MJ2M^2O:2PL2PM2PN2PO2PP2PQ2QP2RE2S=2T<2T_2UW2Uk2V?2VS2W@2WA2WT2Wg2Wh2Wi2XV2YN2YO2ZX2[W2\^2]X2]l2^@2^m2_e2`B2`_2aL2b92bM2c:2d22do2e`2f82gP2h^2i:2ig2j_2k32km2lA2m92n12nE2o=2o>2ok30c31[33334A35=35j37;38B38V38lS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2h25Ehtop2HB5Ha_st5Hl_st3a4e3len1qS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2h25Ehtop2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x2HxS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_st3a4e3len1qS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS1R3HIA4PHIx1h1P3END2PXFS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hp23Hq14Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hp23Hq14Hp2aFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1RFS3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp1FS2rg3Hrg2KrS1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp13SP1FS2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOFSS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1RFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2sp2PP3CRT2bs2FB3sp13len1q5Hlen0S2sp2PP3CRT2bs2D12FB3sp13D1u2rg3HrgFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RS2bs3len1q2p22KlFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1RFFFS3CRTFS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBuFS3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RS1P3END2p23Hp2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1RS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOP1FS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3FS2sp2PP3CRT2bs3ALC4CRT02FB3sp13SPR2F04SP1RFS2loFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R1q3Hq1SS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2sp2PP3CRT2bs3ALC4CRT02FB3sp13SPR2F04SP1RFFFS2sp2PP3CRT2bs2D12FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1RS2bs3len1q2p24Hp2a2KlFS2sp2PP3CRT1P3END2bs2B22FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hp23Hq14Hp2aS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hp23Hq14Hp2aS2sp2PP3CRT2bs2FB3sp1S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2PP3CRT1x2HxS1R3HIA4PHIx4FFRx4CNTx1h2LF2sp2PP3CRT1P2bs4LFB33LFB1d2FB3sp12p21H2H02H1FS2sp2PP3CRT3BUF2bs3B472FB3sp1S2rg3Hrg2KrS3CRTS2sp2PP3CRT2bs2FB3sp1FS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hq15Hqlen4Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hq15Hqlen4Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hq15Hqlen4Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R3len1q2p23Hp23Hq14Hp2a2E2S3len1q2p22PLS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R3len1q2p23Hq14Hp2aSS1P3END2B2S3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RFFS1R3HIA4FFRx1h1P3END1d2FXFS3CRTS1R3HIA2h1FFS2sp2PP3CRT2lo2bs2FB3sp13SP1S1P3len1q3Hq15Hlen0S1P3END3len1q2p23Hp22PLS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1RS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRTS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2HB5Ha_st5Hl_st3a4e3CRT3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2HB5Ha_st5Hl_st3CRT4FBLOS2LF2PP3BUF2bs4LFB33LFB3DPBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT3BUF2bs4LFB33LFB4DXBuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st3a4e3CRT3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st3CRTS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_st3CRTS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_st3a4e3CRT1R2FB3len1qS2LF2sp2bs4LFB33LFB2FB3sp13SP12HB5Ha_st5Hl_st3CRTS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FB3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFS2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF2PP2bs4LFB33LFBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP12HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOP12HB5Ha_st5Hl_st3CRTFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2bs4LFB33LFB3sp14SP1R2HBS2LF2bs4LFB33LFB3sp14SP1R2HBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2HB5Ha_st5Hl_st3CRTFFFFFS1R2LF3slo2bs4LFB33LFB4SLOS3sp12HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp12HB5Ha_st5Hl_st3CRTS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2bs4LFB33LFB3sp12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1FS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOP12HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOP12HB5Ha_st5Hl_st3CRTS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB3sp12HB5Ha_stS2LF2bs4LFB33LFB3sp12HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_st3a4e3CRT1R2FB3len1qS2LF2sp2bs4LFB33LFB2FB3sp13SP12HB5Ha_st5Hl_st3CRTS2LF2bs4LFB33LFB2FB1c2HcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRTS2LF2bs4LFB33LFB3sp14SP1R2HBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF3CRT2bs4LFB33LFBS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS2LF2bs4LFB33LFB3sp1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2h14Estk5HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRTS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOP12HB5Ha_st5Hl_st3a4e3CRT2FB3len1qS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOP12HB5Ha_st5Hl_st3CRTS2LF2bs4LFB33LFB3sp1S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH GETEXT BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx0 FFRx0 CNTx0 PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R"] Lemma hdr_walk : forall (h1 : HST asegs R HIA) (m1 : mem) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (w0 w1 w2 : word)
           (jloc ja : list byte) (k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k128 k136 k144 k152 k160 k168 : word),
      HM asegs R HIA h1 LB ((FB, 256) :: LF) m1 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h
      -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h
      -> havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h
      -> rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      -> rw_cells asegs m1 (FB + 32) [CB 216 jloc]
      -> rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHX
      -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL
      -> rw_cells asegs m1 sp1 [C8 k16; C8 k24; C8 k32; C8 k40; C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88; C8 k96; C8 k104; C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 k152; C8 k160; C8 k168; CB 16 ja; C8 (Z_to_bv 64 FB)]
      -> stk asegs m1 (sp1 + 184) (bv_unsigned sp + -104) -> stk asegs m1 lo sp1 -> mem_inv asegs m1
      -> rw_cells asegs m1 PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m1 (CRT + 424) [CB 272 (zeros 272)] -> bytes_at asegs m1 BUF bs
      -> aobj asegs AL CS m1 PP 8 -> aobj asegs AL CS m1 (CRT + 424) 272 -> aobj asegs AL CS m1 BUF n
      -> presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m1
      -> sshad asegs AL m1 slo sp1 -> sshad asegs AL m1 sp1 (bv_unsigned sp) ->
    aevtA asegs (KF asegs R HIA h1 mo0) POST
      (MS (mkR (Z_to_bv 64 0xaa6b8) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL))
                   (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) a4e (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
              F (Z_to_bv 64 0xaa798) fc None m1 (seg_rom asegs)).
  Proof.
    intros until k168. intros HH1 Ehcs Ehtop Estk Eflag Evol Efr FHD FLOC0 FSH SAVE RSL SThi STlo MI1 HPP1 HEXT1 HB1 OPP1 OEXT1 OBUF1 PRES SS1 SS2.
    rewrite <- Ehcs in OPP1, OEXT1, OBUF1.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m1 PRES HCS1 Estk) as PRES1. clear PRES.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    (* [comment removed for export] *)
    assert (FINX : forall (hq : HST asegs R HIA) (mx : mem) (r p' : Z) (X : xst) (ja' : list byte)
                     (c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 : word)
                     (yra y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 t3v t6v t7v t8v t9v t10v y28 y29 y30 y31 : word),
               HM asegs R HIA hq LB LF' mx -> (forall x, CS x -> hcs asegs R HIA hq x) -> htop asegs R HIA hq = htop asegs R HIA h ->
               hstkhi asegs R HIA hq = hstkhi asegs R HIA h -> hflag asegs R HIA hq = hflag asegs R HIA h ->
               havol asegs R HIA hq = havol asegs R HIA h -> hfr asegs R HIA hq = hfr asegs R HIA h ->
               rw_cells asegs mx FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mx (Z.shiftr FB 3 + al_sb AL) FSHX ->
               rw_cells asegs mx (bv_unsigned sp + -104) SAVEL ->
               rw_cells asegs mx sp1 [C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; C8 c104; C8 c112; C8 c120; C8 c128; C8 c136;
                                      C8 c144; C8 c152; C8 c160; C8 c168; CB 16 ja'; C8 (Z_to_bv 64 FB)] ->
               stk asegs mx (sp1 + 184) (bv_unsigned sp + -104) -> stk asegs mx lo sp1 -> mem_inv asegs mx ->
               presW asegs R HIA hq LB LF (bv_unsigned sp) (bv_unsigned sp) W m mx ->
               sshad asegs AL mx slo sp1 -> sshad asegs AL mx sp1 (bv_unsigned sp) ->
               rw_cells asegs mx PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
               xcells asegs CRT mx X -> xown asegs mx LB X -> xblocks X = [] -> -2^31 < r <= 0 ->
               aevtA asegs (KF asegs R HIA hq mo0) POST
                 (MS (mkR yra (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 FB) t3v (Z_to_bv 64 r) (Z_to_bv 64 FB) t6v t7v t8v t9v t10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) y28 y29 y30 y31)
                     F (Z_to_bv 64 0xaad18) fc None mx (seg_rom asegs))).
    { intros until y31. intros HHq HCSq ETq ESq EFq EVq EFRq FHDq FSHq SAVEq RSLq SThiq STloq MIq PRESq SS1q SS2q HPPq Hpq XCq XOq XBq RRq.
      pose proof (xfold asegs CRT _ _ XCq) as XF. pose proof (xown_ok asegs _ _ _ XOq) as XOK.
      eapply A_x509_crt_ext_B.x_fin with (hq := hq) (Lx := @nil blk) (p' := p') (eo := eo_of X) (ej := ej_of X) (STKc := STKc);
        first [ exact HHq | exact PRESq | exact HPPq | exact CFB | exact FRSH | eassumption | reflexivity
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => rewrite EVq; pose proof (PHIx0 (END - P) ltac:(clear - B2; lia)) as PX; clear - PX; lia
                | |- hfr _ _ _ _ <= _ => rewrite EFRq; pose proof (FFRx0 (END - P) d ltac:(clear - B2; lia)) as FX; clear - FX; lia
                | |- Z.of_nat (length _) <= _ => cbn [length Z.of_nat]; exact (CNTx0 (END - P) ltac:(clear - B2; lia))
                | |- Permutation [] _ => change (ext_blocks (eo_of X)) with (xblocks X); rewrite XBq; constructor
                end
              | match goal with |- ?g => idtac "FINX-LEFT:" g end ]. }
    idtac "HDR-FINX".
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hcs_ok asegs R HIA h1) as CSOKc.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    pose proof (hm_top asegs R HIA h1 _ _ _ HH1) as HTOP1. rewrite Ehtop, Estk in HTOP1.
    assert (SCSc : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS1| eapply crange_sub; [exact SCS0| exact LOS| xl HTOP1]]).
    assert (SCS1c : crange (hcs asegs R HIA h1) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| xl]).
    assert (SCS0c : crange (hcs asegs R HIA h1) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS1| exact SCS0]).
    assert (CFBc : crange (hcs asegs R HIA h1) FB 256) by (eapply crange_mono; [exact HCS1| exact CFB]).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES1)))| apply (art_data_lo asegs R HIA)]).
    assert (SUBh : forall b', In b' (LB ++ fdata LF) -> In b' (LB ++ fdata LF')) by (intros b' Hb'; apply fdata_cons_sub; exact Hb').
    assert (CWPn : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h1) PP 8) by (rewrite Ehtop; eapply client_wrange_mono; [exact CWP| exact SUBh]).
    assert (CWXn : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h1) (CRT + 424) 272) by (rewrite Ehtop; eapply client_wrange_mono; [exact CWX| exact SUBh]).
    assert (CWPh : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBh]).
    assert (CWXh : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA h) (CRT + 424) 272) by (eapply client_wrange_mono; [exact CWX| exact SUBh]).
    assert (CRPs : client_range L (LB ++ fdata LF') sp1 PP 8) by (eapply (client_range_wsep L (LB ++ fdata LF) _ lo _ sp1 _ _ CWP); [exact SUBh| left; exact PPLO]).
    assert (CRXs : client_range L (LB ++ fdata LF') sp1 (CRT + 424) 272) by (eapply (client_range_wsep L (LB ++ fdata LF) _ lo _ sp1 _ _ CWX); [exact SUBh| left; xl]).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA h1) h1 LB LF m1 FB 256 lo HH1 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INHc & INDc & AP & _ & _ & _ & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    assert (BINc : In (BUF, n) (LB ++ fdata LF')) by (apply in_app_iff; left; exact BIN).
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (xcells_zero asegs CRT _ HEXT1) as XC0.
    pose proof XC0 as XC0'. unfold xcells, wbuf, CrtExtStmts.akid_cells, seq_cells in XC0'. cbn [app] in XC0'.
    ddestruct XC0' as (XV & XS & XK & XA & XW & XP & XE & XU & XN).
    cbn [xst_zero x_v1 x_v2 x_v3 x_v4 x_sct x_scp x_scl x_sp x_sn x_k1 x_k2 x_k3 x_k4 x_a1 x_a2 x_a3 x_a4 x_act x_acp x_acl x_ap x_an x_r1 x_r2 x_r3 x_r4
         x_w1 x_w2 x_w3 x_w4 x_pct x_pcp x_pcl x_pp x_pn x_et x_ca x_mp x_ku x_ect x_ecp x_ecl x_ep x_en x_ns] in XV, XS, XK, XA, XW, XP, XE, XU, XN.
    clear HEXT1.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kq; zify_cond Kq.
    { idtac "HDR-EMPTY".
      (* [comment removed for export] *)
      do 2 zstep.
      eapply FINX with (hq := h1) (X := xst_zero) (r := 0) (p' := P);
        first [ exact HH1 | exact HCS1 | exact XC0 | exact PRES1 | exact HPP1 | eassumption | reflexivity | apply xown_zero | xl | (clear; lia) | match goal with |- ?g => idtac "HDR-EMPTY-LEFT:" g end ]. }
    clear XC0.
    (* [comment removed for export] *)
    do 7 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof GETEXT as SPG. unfold x509_get_ext_stmtA, A_X509_GET_EXT in SPG.
    idtac "HDR-GETEXT".
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { eapply SPG with (h := h1) (LB := LB) (LF := LF') (PP := PP) (EXT := CRT + 424) (P := P) (END := END) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (tag := 3);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop; unfold X509_GET_EXT_STACK_A;
        first [ exact HH1 | exact XV | exact HPP1 | eassumption | reflexivity | xside
              | match goal with |- ?g => idtac "GETEXT-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_get_ext_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & rg & p2 & tg & len & q & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrg & HPP2 & XV2 & Hp2 & HG).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaa7bc)) with (Z_to_bv 64 0xaa7bc : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "HDR-GETEXT-BACK".
    pres_call HP2.
    clear HH1 HPP1 XV STlo SS1 MI1.
    presA_transport HP2.
    clear HP2 SPG.
    switch_h h1 h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    rewrite Evol in Evol2. rewrite Efr in Efr2.
    unfold buf_cells in XV2.
    assert (HCS2 : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    assert (XCv : forall mx, rw_cells asegs mx (CRT + 424) [C4 tg; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 q)] ->
              rw_cells asegs mx (CRT + 448) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 480) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 504) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                             C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 584) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 608) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 640) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 656) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
              rw_cells asegs mx (CRT + 688) [CB 8 (zeros 8)] ->
              xcells asegs CRT mx (xst_v3 tg (Z_to_bv 64 0) len q)).
    { intros mx X0 X1 X2 X3 X4 X5 X6 X7 X8. exact (conj X0 (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8)))))))). }
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kr; zify_cond Kr.
    { idtac "HDR-GETEXT-ERR".
      eapply FINX with (hq := h2) (X := xst_v3 tg (Z_to_bv 64 0) len q) (r := rg) (p' := p2);
        first [ exact HH2 | exact HCS2 | exact HPP2 | eassumption | reflexivity | apply xown_v3 | (apply XCv; assumption) | xl Hrg | match goal with |- ?g => idtac "HDR-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kr Hrg; try kland Kr; rewrite ?Z.mod_small in Kr by lia; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite ?Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
    subst rg. ddestruct (HG eq_refl) as (Hq1 & Hlen0 & Hqlen & Hp2a). clear HG Kr.
    (* [comment removed for export] *)
    xzto [0xaa838].
    idtac "HDR-A".
    (* [comment removed for export] *)
    zstep. if_cases Kl; zify_cond Kl.
    { idtac "HDR-NOEXT".
      assert (E2 : p2 = q + len) by (clear - Kl Hp2a Hq1 Hlen0 Hqlen B1 B3 B5 B47; try kland Kl; rewrite ?Z.mod_small in Kl by lia; lia).
      (* [comment removed for export] *)
      do 8 zstep.
      rewrite ?(unsigned_lit p2) by (xl Hp2). rewrite ?(unsigned_lit (q + len)) by (xl Hq1 Hlen0 Hqlen).
      rewrite <- E2. rewrite Z.lxor_nilpotent.
      match goal with |- context [Z_to_bv 64 (Z.land ?e ?c)] => let EE := fresh in assert (EE : Z.land e c = 0) by (vm_compute; reflexivity); rewrite EE; clear EE end.
      eapply FINX with (hq := h2) (X := xst_v3 tg (Z_to_bv 64 0) len q) (r := 0) (p' := p2);
        first [ exact HH2 | exact HCS2 | eassumption | reflexivity | apply xown_v3 | (apply XCv; assumption) | (clear; lia) | match goal with |- ?g => idtac "HDR-NOEXT-LEFT:" g end ]. }
    assert (PL : p2 < q + len) by (clear - Kl Hp2a Hq1 Hlen0 Hqlen B1 B3 B5 B47; try kland Kl; rewrite ?Z.mod_small in Kl by lia; lia).
    clear Kl.
    (* [comment removed for export] *)
    xzto [0xaa8c4].
    idtac "HDR-B".
    idtac "HDR-C".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
    match goal with H : rw_cells _ ml (FB + 32) [CB 216 _] |- _ => destruct (floc_of_junk asegs ml (FB + 32) _ H) as (lenw & otg & opd & olen & op & crit & et & j1 & j2 & j3 & j4 & FLOCl); clear H end.
    assert (INV : xinv (q + len) [] ml h2 (xst_v3 tg (Z_to_bv 64 0) len q) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja ja).
    { unfold xinv. cbn [app]. spine;
        first [ eassumption | apply xown_v3 | (apply XCv; assumption) | (cbn; constructor) | match goal with |- ?g => idtac "HDR-INV-LEFT:" g end ]. }
    assert (HBUD : BUD h2 [] p2).
    { unfold BUD. rewrite Evol2, Efr2. cbn [length Z.of_nat].
      pose proof (PHIx0 (p2 - P) ltac:(clear - Hp2; lia)). pose proof (FFRx0 (p2 - P) d ltac:(clear - Hp2; lia)). pose proof (CNTx0 (p2 - P) ltac:(clear - Hp2; lia)). lia. }
    idtac "HDR-LOOP".
    pose proof (tloop (q + len) ltac:(clear - Hq1 Hlen0; lia) ltac:(exact Hqlen) (Z.to_nat (q + len - p2)) p2 ltac:(clear - PL; lia) ltac:(clear - Hp2 PL; lia)) as TL.
    unfold LoopOblig in TL.
    eapply TL; first [ exact INV | exact HBUD | eassumption | match goal with |- ?g => idtac "HDR-LOOP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L56385286098.7L64850595401.000000G00HS1R3BUF2lo2bs3BCE3ALO1HS". (* [comment removed for export] *)
  #[using="IMG UARG SM2 NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH GETEXT BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx0 FFRx0 CNTx0 PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF"] Lemma main_call : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m (CRT + 424) [CB 272 (zeros 272)] -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m (CRT + 424) 272 ->
    aevtS asegs POST
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 CRT) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 A_X509_CRT_EXT) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros until t6. intros HH HK0 HPP HEXT HBUF ST SS MI OPP OEXT.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE.
      pose proof (art_lo asegs R HIA) as ALO. pose proof LOS. clear - BCE ALO H. lia. }
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_crt_ext_A.pro_walk with (STKc := STKc) (P := P) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact HH | exact HPP | exact HEXT | exact HBUF | exact ST | exact SS | exact MI | exact OPP | exact OEXT | exact OBUF | exact LFB | eassumption
              | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    ddestruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & w0 & w1 & w2
                   & jloc & ja & k16 & k24 & k32 & k40 & k48 & k56 & k64 & k72 & k80 & k88 & k96 & k104 & k112 & k120 & k128 & k136 & k144 & k152 & k160 & k168
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & FLOC0 & FSH & SAVE & RSL & SThi & STlo & MI1
                   & HPP1 & HEXT1 & HB1 & OPP1 & OEXT1 & OBUF1 & APP & APC & PRES0 & SS1 & SS2).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & _).
    intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    eapply hdr_walk with (FB := FB) (sp1 := sp1) (h1 := h1);
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact APP | exact APC | exact BUFLO | exact HH1 | exact PRES0 | eassumption
            | match goal with |- ?g => idtac "HDR-PRE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  (* [comment removed for export] *)
  #[using="IMG UARG SM2 NS1 STKc0 AMS NA1 DIMG HMND GT GB OIDH GETEXT BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx0 FFRx0 CNTx0 PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le"] Theorem A_x509_crt_ext_spec : x509_crt_ext_stmtA asegs R HIA PHIx FFRx CNTx (A_x509_crt_ext_A.STKx R STKc) (LFMAX_CRT + 3) A_X509_CRT_EXT.
  Proof.
    unfold x509_crt_ext_stmtA. intros until bs. intros; subst.
    eapply main_call with (bs := bs) (d := d) (slo := slo) (BUF := BUF);
      first [ eassumption | reflexivity | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
  Qed.
End Walk.
