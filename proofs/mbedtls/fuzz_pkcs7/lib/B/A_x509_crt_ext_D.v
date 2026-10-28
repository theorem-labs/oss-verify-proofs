(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse P_x509_crt_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_get_san_A A_x509_crt_ext_stmt A_x509_crt_ext_A A_asn1_get_bool A_oid_x509_ext A_x509_get_ext_A A_x509_basic_A A_x509_key_usage_A A_x509_skid_A A_x509_ns_cert_type_A A_x509_crt_ext_area A_x509_crt_ext_B A_x509_crt_ext_C.
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
Definition zchk_new : list Z := [0xaa9e8; 0xaa9ec; 0xaa9f0; 0xaa9f4; 0xaa9f8].
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6757220598.1000001S".
Lemma zchk_land1 x : Z.land x 1 = x mod 2. Proof. apply (Z.land_ones x 1); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422538246.1000001S".
Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29782099606.1000001S".
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L28392174091.155L34564696816.159L40819769766.1  L49085461534.158L61422585519.103L63887242734.157L66149329409.196L9354819225.167 00001H01o02002S02\03B03j05KS1R2LF2sp2PP3CRT3BUF2lo3slo2bs4LFB33LFB3PP04PPLO4CRT04SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp11HSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11HS2LF4LFB3S2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB3sp11HS2LF2bs4LFB33LFB2FB2r01H1q1r2H02H12q02H5S1R4STKc5STKc12LF2sp2PP3CRT2lo3slo2bs4LFB33LFB3PP04CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4".
Lemma zchk_land15 x : Z.land x 15 = x mod 16. Proof. apply (Z.land_ones x 4); lia. Qed.
Local Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac zlia := zchk_clear; lia.
Local Ltac zchk_dec :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; zlia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; zlia) ]
  | |- context [Z.leb ?a ?b] =>
      first [ replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; zlia)
            | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; zlia) ]
  end.
Local Ltac zchk_base :=
  first [ reflexivity
        | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
        | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Local Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => zchk_base
  end.
Local Ltac zchk_solve :=
  rewrite ?zchk_land1, ?zchk_land3, ?zchk_land7, ?zchk_land15;
  zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with
                 | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
                 | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) by zlia
                 end;
          zchk_rec ].
Local Ltac zchk_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xaacd4 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xaacd4) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) zchk_new) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
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

  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 PP0 CWP PPLO BIN B1 B2 B3 B47 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma errj_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 : list byte) (ja jb : list byte) (r p' bp : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> -2^31 < r <= 0 ->
    BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v (Z_to_bv 64 r) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaacfc) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.errj_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.errj_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.errj_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma tail_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 s4v s5v s6v s9v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 (Z_to_bv 64 (CRT + 640)) x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v s6v (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) s9v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaab0c) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.tail_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.tail_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.tail_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 NA1 DIMG KUSE STKc1 STKc2 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_ku : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaabe0) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_ku with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_ku with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_ku ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 NA1 DIMG NSCT STKc1 STKc2 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_ns : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaac34) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_ns with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_ns with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_ns ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG BASIC STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_basic : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaab58) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_basic with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_basic with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_basic ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG SKID STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_skid : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaabfc) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_skid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_skid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_skid ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIq FFRq CNTq STKq SEQOF STKc1 STKcq PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_eku : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    Z.land (x_seen X) 2048 = 0 ->
    (forall b, b = 1 \/ b = 8 \/ b = 32 \/ b = 2048 -> Z.land (bv_unsigned (x_et X)) b = 0 -> Z.land (Z.lor (x_seen X) 2048) b = 0) ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaac50) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_eku with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_eku with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_eku ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIs FFRs CNTs STKs GSAN STKc1 STKcs PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIs_le FFRs_le CNTs_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_san : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    Z.land (x_seen X) 32 = 0 ->
    (forall b, b = 1 \/ b = 8 \/ b = 32 \/ b = 2048 -> Z.land (bv_unsigned (x_et X)) b = 0 -> Z.land (Z.lor (x_seen X) 32) b = 0) ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaac18) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_san with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_san with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_san ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIp FFRp CNTp STKp GPOL STKc1 STKcp PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIp_le FFRp_le CNTp_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_pol : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    Z.land (x_seen X) 8 = 0 ->
    (forall b, b = 1 \/ b = 8 \/ b = 32 \/ b = 2048 -> Z.land (bv_unsigned (x_et X)) b = 0 -> Z.land (Z.lor (x_seen X) 8) b = 0) ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaab78) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_pol with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_pol with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_pol ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIk FFRk CNTk STKk AKID STKc1 STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIk_le FFRk_le CNTk_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma arm_akid : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    Z.land (x_seen X) 1 = 0 ->
    (forall b, b = 1 \/ b = 8 \/ b = 32 \/ b = 2048 -> Z.land (bv_unsigned (x_et X)) b = 0 -> Z.land (Z.lor (x_seen X) 1) b = 0) ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaad4) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_akid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_akid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_akid ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@D28498761192.284D4451634193.284 D60109196847.284K10093203181.284K17397425005.284K23551032557.284K2431698795.284 K30840574317.284K37953334125.284K44164039966.284K49978975725.284K52576198765.284K60822670701.284K9136277101.284 K9840090748.284 L10091109645.2  L1685717371.0   L17382748301.2  L23182876091.2  L23540543245.2  L2419170461.2   L24882004373.71 L27111942217.1  L29680655011.1  L30851056269.2  L35655538583.72 L37963823245.2  L38235734261.1  L41202929119.272L44168742175.3  L47042279518.81 L49964299789.2  L52565717901.2  L53271535775.272L54261998223.2  L60828966541.2  L63174241565.81 L64850595401.0  L9090702513.71  L9134183821.2   L9835808138.2   P23170010975.284P54268551240.284Q10649498890.281Q10651748618.280Q13733106231.280Q17701933584.281Q28496781288.283Q28498761192.284Q37216054521.281Q39600066516.281Q40916972731.281Q42439443119.284Q4451634193.284 Q4453582353.283 Q45353769141.280Q49746415830.284Q60529412798.284Q61556549392.282Q61847600945.281Q67038978349.284Q68013150533.284Q8699115497.284 00000c01V02R03?03l04Y05E06206_07L08908f09S0:@0:l0:m0:n0:o0;00;10;20;P0;T0;Y0;Z0=L0=M0=Q0>20>30?`0?a0?b0@C0@D0@E0B20B30BO0BP0BQ0CW0De0E80EK0E^0F10FV0G;0GU0GV0GW0HG0Hl0IQ0Id0Jb0Jc0K?0L90MF0N:0O@S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPB2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stFSFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTFS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HQE3HBPFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2e92HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3PP02HBFFS1R2LF2PP3slo2bs4LFB33LFB4SLOS2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2PP2bs4LFB33LFB3TOP3sp12e95HTOPc2HB5Ha_st5Hl_stFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2e92HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs4LFB33LFB3TOP3sp13SP12e95HTOPc2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma skip_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 (Z_to_bv 64 (CRT + 640)) x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaa58) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 4 zstep.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    eapply tail_walk with (q := e9) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | eassumption | xl HP0 HQ0 HQE HE9 HBP | match goal with |- ?g => idtac "SKIP-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L13527335811.83 L24882004373.71 L27111942217.1  L2732059965.83  L29680655011.1  L32361667354.269L35655538583.72 L38235734261.1  L49334198535.83 L64850595401.0  L9090702513.71  Q23833329338.277Q27663295649.277Q31632298672.277Q37641087770.27700002502S02W02l03103R05D05H07M07N07j08W08j09=0:5S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS2sp2PP3CRT2bs2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPSS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma default_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 (Z_to_bv 64 (CRT + 640)) x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaac6c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    pose proof INV as INV0.
    open_xinv INV hc.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    { eapply skip_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV0 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DEF-SKIP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 4 zstep.
    eapply errj_walk with (r := -8320) (p' := q) (bp := bp); first [ exact INV0 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 HBP | match goal with |- ?g => idtac "DEF-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@D28498761192.285D4451634193.285 D60109196847.285K10093203181.285K17397425005.285K23551032557.285K2431698795.285 K30840574317.285K37953334125.285K44164039966.285K49978975725.285K52576198765.285K60822670701.285K9136277101.285 K9840090748.285 L10091109645.2  L13527335811.83 L15902870269.83 L1685717371.0   L17382748301.2  L23182876091.2  L23540543245.2  L2419170461.2   L24882004373.71 L27111942217.1  L29680655011.1  L30851056269.2  L32361667354.273L33947518423.83 L35655538583.72 L37963823245.2  L38235734261.1  L41202929119.273L44168742175.3  L47042279518.81 L49964299789.2  L52565717901.2  L53271535775.273L54261998223.2  L60828966541.2  L63174241565.81 L64850595401.0  L9090702513.71  L9134183821.2   L9835808138.2   P23170010975.285P54268551240.285Q10649498890.282Q10651748618.281Q13733106231.281Q17701933584.282Q23831346178.281Q27652695577.281Q28496781288.284Q28498761192.285Q31633985544.281Q37216054521.282Q37638875554.281Q39600066516.282Q40916972731.282Q42439443119.285Q4451634193.285 Q4453582353.284 Q45353769141.281Q49746415830.285Q60529412798.285Q61556549392.283Q61847600945.282Q67038978349.285Q68013150533.285Q8699115497.285 00000c01V02R03?03l04Y05E06206_07L08908f09S0:@0:l0:m0=20=G0=H0=I0=J0=K0=L0=j0=n0>30>40>U0@Z0BL0BM0BQ0C20C30D`0Da0Db0EC0ED0EE0G20G30GO0GP0GQ0HW0Ie0J80JK0J^0K10K^0L10LV0M;0MN0Mh0N`0Na0Nb0OR0P70P\0Po0Qm0Qn0RJ0SD0TQ0UE0VKS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPB2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT2bs2FB3sp1SFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HQE3HBPFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2e92HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFB3PP02HBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS1R2LF2PP3slo2bs4LFB33LFB4SLOS2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2PP2bs4LFB33LFB3TOP3sp12e95HTOPc2HB5Ha_st5Hl_stFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2e92HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs4LFB33LFB3TOP3sp13SP12e95HTOPc2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma unknown_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaaf0) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 6 zstep.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kc; zify_cond Kc.
    { (* [comment removed for export] *)
      do 2 zstep.
      eapply errj_walk with (r := -9570) (p' := e9) (bp := bp); first [ exact INV2 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 HBP | match goal with |- ?g => idtac "UNK-ERR-LEFT:" g end ]. }
    eapply tail_walk with (q := e9) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | eassumption | xl HP0 HQ0 HQE HE9 HBP | match goal with |- ?g => idtac "UNK-TAIL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac jt_go Hk := rewrite Hk in *; do 7 zstep.
  (* [comment removed for export] *)
  Ltac hz_tac HK :=
    lazymatch goal with SUBo : forall b, _ -> _ -> Z.land (x_seen ?X) b = 0, KD1 : forall b, _ -> Z.land _ b = b -> _ |- Z.land _ _ = 0 =>
      cbn [x_seen setet]; apply SUBo; [clear; lia|]; apply KD1; [clear; lia|]; rewrite ?HK; reflexivity end.
  Ltac hsub_tac HK :=
    lazymatch goal with SUBo : forall b, _ -> _ -> Z.land (x_seen ?X) b = 0, EB : forall b, _ -> _ -> _ /\ _ |- forall b, _ -> _ -> _ =>
      let b := fresh "b" in let Hb := fresh "Hb" in let H0 := fresh "H0" in let E1 := fresh "E1" in let E2 := fresh "E2" in
      intros b Hb H0; cbn [x_et x_seen setet] in H0 |- *; destruct (EB b ltac:(clear - Hb; lia) H0) as [E1 E2];
      rewrite ?HK in E1; rewrite Z.land_lor_distr_l, (SUBo b Hb E2), E1; reflexivity end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "07M0@D16464982057.290D54752915971.290D60109196847.290K12226132804.290K21870859916.290K22945712379.290K44164039966.290L10235320750.295L10669763125.295L11404653746.295L11668478197.295L12219836580.2  L12408374717.1  L12539321134.295L13527335811.83 L13604783214.295L14379947573.295L14447004729.2  L1446287989.295 L14664429230.295L14732077592.0  L15489369424.2  L15613930590.1  L15730431982.295L16794857518.295L1685717371.0   L17099211893.295L18154731893.295L19232585650.295L1930573885.1   L19716667709.1  L20544516914.295L20874651829.295L21866712442.2  L22135340654.295L22941438733.2  L23198718126.295L23603422965.295L23710501914.276L24061693967.278L24882004373.71 L27111942217.1  L27220613693.1  L27319894773.295L27976633717.295L29588410158.295L29680655011.1  L29695142424.0  L30252456425.276L30252456425.278L30652835950.295L30696963253.295L31094682933.295L3137102497.0   L31720936110.295L32786480110.295L33806214005.295L34482876405.295L35082026350.295L35497694602.3  L35655538583.72 L36150175662.295L36526609077.295L37215650030.295L37631907489.0  L37744465018.275L38200921077.295L38235734261.1  L38279555374.295L39356568174.295L40422505646.295L40912402741.295L4163455413.295 L42287381298.295L43620562798.295L43632719733.295L44168742175.3  L44598345021.83 L45572442045.1  L45749943022.295L46360962741.295L47408094133.295L47706788769.0  L48387988182.2  L49154504626.295L49334198535.83 L50136402421.295L51037680434.295L51134580661.295L52067440306.286L52137533806.295L52298219197.1  L52385715068.1  L52855736117.295L53214546862.295L53854451189.295L54280484078.295L55343865134.295L56566375221.295L57627662389.295L58709670382.295L59109295640.0  L59773035054.295L59978813757.1  L60339656309.295L60839037806.295L61639115041.0  L61907727790.295L62971633390.295L63059576245.295L63164974909.1  L64850595401.0  L67445894197.295L68295269422.295L7046229486.295 L7273771125.295 L7369768728.0   L7421422752.2   L7736014575.2   L7949384949.295 L8110134830.295 L9090702513.71  L9636196114.10  P14461423358.290P7750690063.290 Q10235426675.294Q10297205759.294Q1044364068.294 Q10476456817.294Q10498468606.294Q10522489501.294Q10703720243.294Q10963872638.294Q11362932927.294Q11542208561.294Q11564712894.294Q11588741213.294Q11767899379.294Q12027494462.294Q12431310463.294Q12453258387.294Q12538902003.294Q12632570238.294Q12652626205.294Q13087488510.294Q13605153459.294Q13696720446.294Q13718382301.294Q13893612403.294Q14153211582.294Q14664843379.294Q14743773651.294Q14762473470.294Q14764726291.294Q14766758983.294Q14776075027.294Q14795120541.294Q15217390718.294Q15569742931.294Q15574528659.294Q15615935677.284Q15730604339.294Q15842997511.294Q15858775389.294Q1597722111.294 Q16235477843.294Q16456686910.294Q16464982057.290Q16794754803.294Q16888152702.294Q16925026845.294Q17516671742.294Q18101537713.294Q1819811143.294 Q18582399934.294Q18692066259.294Q19160998257.294Q1937982833.294 Q19646546302.294Q19961542099.294Q20225148465.294Q20395152804.294Q21171156935.294Q21182740253.294Q21290909681.294Q21471890276.294Q22134968499.294Q22237146247.294Q22537642020.294Q2275262692.294 Q23136260739.289Q23199151731.294Q23296574023.294Q23424977521.294Q23601797604.294Q24155188159.294Q24360762119.294Q24489157425.294Q24824344228.294Q2516139692.284 Q25220907391.294Q25309204371.294Q25426481351.294Q25565370609.294Q25790799027.294Q25816022950.284Q25901073508.294Q26289284671.294Q2661376703.294 Q26631647665.294Q26857075315.294Q26922866771.294Q26966834468.294Q27355013119.294Q27355748051.294Q27560587079.294Q27695273841.294Q27721742078.294Q27924900659.294Q28030980836.294Q28584371391.294Q28763622449.294Q28785635262.294Q2883990023.294 Q28990882035.294Q29096709028.294Q2946010515.294 Q29588578803.294Q29650098815.294Q29700980167.294Q29851878782.294Q29875907869.294Q3003742769.294 Q30055070131.294Q30086162835.294Q30165082468.294Q30314661374.294Q30602996230.284Q30652729011.294Q30718473023.294Q30767223431.294Q30919735870.294Q30939792093.294Q31114502003.294Q31228708388.294Q31242882857.289Q31326757395.294Q31374654142.294Q31720586355.294Q31784200447.294Q31959543921.294Q31983883262.294Q32180778035.294Q3233365747.294 Q32440373374.294Q32786830643.294Q32848347583.294Q33049610430.294Q33244409331.294Q3339450788.294 Q33504528702.294Q33907812223.294Q33948699352.286Q33948765052.284Q33951215832.285Q33951215832.287Q34083131121.294Q34109599358.294Q34312749747.294Q34570284798.294Q34610423571.294Q34973801535.294Q35081917363.294Q35175319358.294Q35212193757.294Q35378509939.294Q35638626238.294Q36149741939.294Q36239506686.294Q36280009885.294Q36442657075.294Q36633006364.295Q36702289278.294Q37216022067.294Q3727628415.294 Q37307323838.294Q37344197213.294Q37768532542.294Q38279645171.294Q38373575550.294Q38394139591.294Q38409917213.294Q38831235260.295Q38999473150.294Q39356415155.294Q39469877469.294Q39621797959.286Q39621863907.284Q40067813566.294Q40422134387.294Q40646415985.294Q4072084465.294 Q41131472510.294Q41712144177.294Q41872219667.294Q42197724990.294Q42439443119.290Q42776323313.294Q42954715236.294Q4297512883.294 Q43620391347.294Q43649341830.284Q43713648007.294Q43733882333.294Q43852537265.294Q4407271268.294 Q44781996871.294Q44949364774.284Q45086691044.294Q45198182227.294Q45750293555.294Q45847748615.294Q45950762259.294Q46152968100.294Q46454566351.286Q46454631531.284Q46911904199.294Q47050785265.294Q47278048691.294Q47383874916.294Q47765794623.294Q47988145799.294Q4803866943.294 Q48116541105.294Q48452248100.294Q48831775999.294Q49180433521.294Q49401663539.294Q49515879396.294Q49698585326.288Q49746415830.290Q49895964095.294Q4992554195.294 Q5009408135.294 Q50246710577.294Q50271048894.294Q50467916275.294Q50582155428.294Q51007548115.294Q51135513471.294Q51186393799.294Q51306146545.294Q5137811633.294 Q51531574963.294Q5162182718.294 Q51641587300.294Q51838693011.294Q51976164243.294Q52137627571.294Q52194981951.294Q52252121991.294Q52396761918.294Q52433079261.294Q52599915635.294Q52707577636.294Q53214389619.294Q53260964351.294Q53316301127.294Q53462489342.294Q53499355293.294Q5363240307.294 Q53665676595.294Q53771756772.294Q53971975064.294Q54280116787.294Q54325147327.294Q54382286343.294Q54526669246.294Q54567175773.294Q54729822963.294Q5473547300.294 Q54752915971.290Q54989454910.294Q55344296947.294Q55390874751.294Q55556372755.294Q55594489726.294Q55795551155.294Q56055699454.294Q5607464915.294 Q56459216191.294Q56604870803.294Q56634305713.294Q56660741182.294Q56697083101.294Q56872313203.294Q57132174526.294Q57522879231.294Q57724397054.294Q57757044125.294Q57935939123.294Q58197926526.294Q58430374099.294Q58709301043.294Q58801134270.294Q58822796125.294Q59002224627.294Q59011533944.285Q59011533944.287Q59262081854.294Q59773455603.294Q59826642515.294Q59866886270.294Q59886950429.294Q6026905343.294 Q60329931006.294Q6073591367.294 Q60839208371.294Q60930779454.294Q60935090567.294Q60954800605.294Q61561362878.294Q61907557235.294Q62021047965.294Q6228427262.294 Q62397455379.294Q62627118974.294Q6264777117.294 Q62971211827.294Q63069162503.294Q63084940381.294Q63691265086.294Q64269610481.294Q6440002099.294 Q65044406867.294Q65337950897.294Q6537178596.294 Q66275307591.294Q66291086237.294Q66563749860.294Q67038978349.290Q67341560071.294Q67357337949.294Q67467596081.294Q67629739172.294Q6769594904.287 Q68013150533.290Q68294914803.294Q68405186247.294Q68425158173.294Q68697555556.294Q6999000954.285 Q6999000954.287 Q7046054707.294 Q7090569151.294 Q7093452115.294 Q7139319559.294 Q7292085950.294 Q7324733277.294 Q7503633395.294 Q754083719.294  Q7553888595.294 Q7613907620.294 Q8109717747.294 Q8156812671.294 Q8207692999.294 Q8368823422.294 Q8390485021.294 Q8569909427.294 Q8699115497.290 Q873836465.294  Q8829771006.294 Q9233025599.294 Q9434576190.294 Q9637729907.294 Q9743814948.294 Q9897620926.294 00000e01Z02X03G04604e05V06706X07907Z07[07`08A0:F0:g0;H0;I0;j0<K0<L0<R0<W0=80=Y0=Z0>;0>\0?=0?B0?G0?h0@I0@J0@k0@l0AM0An0BO0C00CN0CR0CW0D80DY0E:0E?0E@0Ea0FB0Fc0GD0Ge0Gf0HG0Hh0II0Ij0JK0JL0L>0L_0M@0Ma0Mb0O<0O]0Oa0PB0Pc0QD0Qe0RF0Rg0SH0Si0Sj0T?0TD0Te0UF0Ug0Uh0Uo0VP0XU0Y60YW0Z80Z90ZZ0Z_0Zd0[E0[f0\G0\h0]I0]j0^K0^l0^m0_N0_S0`40`U0`V0a70aX0b90b>0b?0b`0cA0cb0dC0dD0dK0dL0dm0eN0ej0f=0gP0h[0hk0hl0hm0hn0ho0i00i10i20i30i40i50i60i70i80i90iP0i`0ia0ib0ic0j30j40j50j60j70jG0j^0j_0k60kM0kd0ke0kf0l=0lT0lg0m70mN0mO0mP0mg0mh0nP0n`0na0nb0nc0nd0o;0o<0oS0oT0oU0oV0om0on0oo10F10G10H10I10Y11011111211Z11j12A12B12C12D12[12\12]13013113H13_13`13a14N14O14P14Q14R14S14j14k14l15C15Z15[15\15]15^15_15`15a16816916:16Q16a16b17917:17;17<17=17T17U17V18N18^18_19619719819919:19b1:91::1:J1:K1:L1:M1:N1:O1:P1:`1:a1:b1:c1:d1:e1:f1;:1;N1;b1<61<71<81<91<:1<Q1<R1<b1<c1<d1<e1<f1=61=71=81=91>11>21>B1>C1>D1>E1>F1>V1>W1>n1>o1?\1?]1?m1?n1@B1@V1@W1@g1@h1@i1@j1@k1AB1AC1B61B71B81B91BI1CA1CX1CY1CZ1C[1D21D_1D`1E71EG1E^1F51F61FJ1F^1G51G61G71G81G91GP1GQ1GR1GS1GT1GU1GV1GW1H41I51I61IM1Id1Ie1If1Ig1Ih1J?1J@1JW1JX1JY1JZ1J[1J\1K31KJ1KZ1K[1L21L31L41L51L61LF1LG1L^1L_1L`1La1Lb1Lc1M;1MK1ML1Mc1Md1Me1Mf1Mg1NO1NP1N`1Na1O81O91O:1O;1OR1OS1Oj1Ok1Ol1Om1On1Oo1P01P11P21P31P41PK1P[1P\1P]1P^1QX1RR1RS1Rc1S:1S;1S<1S=1S>1SU1Se1Sf1T=1T>1T?1TO1TP1TQ1Th1Ti1Tj1U:1UQ1UR1US1UT1UU1Ul1Um1Un1VE1VF1VG1WW1Wn1Wo1X01X11XM1YC1YS1Yj1Yk1Yl1Z@1ZT1Zd1Ze1[<1[S1[T1[U1[V1[m1\D1\E1\U1\V1\m1\n1\o1]01^91^:1^;1^<1^=1^>1^?1^@S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11X2et2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11X2et2HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp11X2et2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u1X2et2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC1X2et2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC1X2et2HB5Ha_st5Hl_stS2LF3CRT3BUF2bs4LFB33LFB4DXBu1X2et2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS1b2HbS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT2bs2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2et2HUS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2b02HbFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2lo2bs2FB3sp13SP1S2et2UR1r2KT1q1H2H0S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu1X2et2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBFFFFFFFFFFFFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFS2LF2bs4LFB33LFBFFFFS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBFFFFS1R2LF2bs4LFB33LFB4IMG'FS1R2LF2bs4LFB33LFB4IMG'FFFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFFS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFS1R2LF2bs4LFB33LFB4IMG'FFS2LF2bs4LFB33LFB2FBFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFFFFFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFFFFFFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'FFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFFS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB4IMG'FS2LF2bs4LFB33LFBFFFFFFS2LF2bs4LFB33LFBFFFFFFS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBFFFFS1R2LF2bs4LFB33LFB4IMG'FS2LF2bs4LFB33LFBFFFFS2LF2bs4LFB33LFBFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS2LF2bs4LFB33LFBFFFFS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS2LF2bs4LFB33LFBFS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBFS2LF2bs4LFB33LFBFFFFS1R2LF2bs4LFB33LFB4IMG'FS1R2LF3CRT3slo2bs4LFB33LFB4SLOS1X2et2HB5Ha_st5Hl_stFFFS2LF2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R2LF2bs4LFB33LFB4IMG'FFFS1R2LF2bs4LFB33LFB4IMG'S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'FFFFFFFS2LF3CRT2bs4LFB33LFB2HB5Ha_stS1R3HIA1h2LF2sp3CRT2bs4LFB33LFB3TOP3sp11X2et5HTOPc2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'FS1R2LF2bs4LFB33LFB4IMG'FFFFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFFS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFFFS1R2LF2bs4LFB33LFB5ALWF'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFFS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFS1R2LF2bs4LFB33LFB4IMG'FS1R2LF2bs4LFB33LFB4IMG'FFFFFFFFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RFS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFS2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'FFS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu1X2et2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB4IMG'FFFS2LF3CRT2bs4LFB33LFB4CRT02HBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFFS1R3HIA1h2LF2sp3CRT3slo2bs4LFB33LFB3TOP3sp13SP11X2et5HTOPc2HB5Ha_st5Hl_stFFFFFFF". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma dispatch_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaa68) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    pose proof INV as INV0.
    open_xinv_mu INV hc.
    pose proof (bv_unsigned_in_range 64 (sx32 et)) as UR. unfold bv_modulus in UR. cbn [Z.pow Z.of_N Pos.pow] in UR.
    pose proof (bv_unsigned_in_range 64 (sx32 (x_et X))) as ER. unfold bv_modulus in ER. cbn [Z.pow Z.of_N Pos.pow] in ER.
    assert (OET : aobj asegs AL (hcs asegs R HIA hc) mm (CRT + 640) 8) by (eapply aobj_sub; [exact OEXT| clear; lia| clear; lia]).
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "DISP-A".
    (* [comment removed for export] *)
    zstep. if_cases KD; zify_cond KD.
    { (* [comment removed for export] *)
      do 3 zstep.
      eapply errj_walk with (r := -9472) (p' := q) (bp := bp); first [ exact INV0 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 HBP | match goal with |- ?g => idtac "DISP-DUP-LEFT:" g end ]. }
    pose proof (Z.land_nonneg (bv_unsigned (sx32 et)) (bv_unsigned (sx32 (x_et X)))) as LN.
    assert (KD0 : Z.land (bv_unsigned (sx32 et)) (bv_unsigned (sx32 (x_et X))) = 0).
    { first [ exact KD | apply land64_zero in KD; [exact KD|] | apply mod64_zero in KD; [exact KD|] ].
      all: pose proof (PropExec.Z_land_range (bv_unsigned (sx32 et)) (bv_unsigned (sx32 (x_et X))) ltac:(clear - UR; lia) ltac:(clear - ER; lia)); clear - H UR ER; lia. }
    clear KD.
    (* [comment removed for export] *)
    do 4 zstep.
    idtac "DISP-B".
    match type of XE with rw_cells _ _ _ [C4 ?w; _; _; _] => set (etn := w) in XE end.
    assert (XO1 : xown asegs mm (Lx ++ LB) (setet X etn)).
    { apply xown_setet; [exact XO|]. intros b Hb H0. subst etn. exact (proj2 (etn_bits et (x_et X) b ltac:(clear - Hb; lia) H0)). }
    pose proof XO as XOo. ddestruct XOo as (_ & _ & _ & _ & _ & _ & _ & _ & SUBo).
    clear XO.
    assert (PERM1 : Permutation Lx (xblocks (setet X etn))) by exact PERM.
    clear PERM.
    fold_xinv INV1 hc Lx (setet X etn) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    assert (KD1 : forall b, 0 <= b < 2^32 -> Z.land (bv_unsigned (sx32 et)) b = b -> Z.land (bv_unsigned (x_et X)) b = 0).
    { intros b Hb Hub. rewrite <- (land_sx32_low (x_et X) b Hb). rewrite <- Hub.
      rewrite Z.land_assoc, (Z.land_comm (bv_unsigned (sx32 (x_et X))) (bv_unsigned (sx32 et))), KD0. apply Z.land_0_l. }
    assert (EB : forall b, 0 <= b < 2^32 -> Z.land (bv_unsigned etn) b = 0 -> Z.land (bv_unsigned (sx32 et)) b = 0 /\ Z.land (bv_unsigned (x_et X)) b = 0).
    { intros b Hb H0. subst etn. exact (etn_bits et (x_et X) b Hb H0). }
    clearbody etn.
    idtac "DISP-C".
    (* [comment removed for export] *)
    zstep. zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. if_cases KN; zify_cond KN.
      { eapply arm_ns with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-NS-LEFT:" g end ]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases KE; zify_cond KE.
      { eapply arm_eku with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | hz_tac KE | hsub_tac KE | match goal with |- ?g => idtac "DISP-EKU-LEFT:" g end ]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases KC; zify_cond KC.
      { eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-DEF1-LEFT:" g end ]. }
      eapply arm_basic with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-BASIC-LEFT:" g end ]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KT; zify_cond KT.
    { eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-DEF2-LEFT:" g end ]. }
    assert (HU : 1 <= bv_unsigned (sx32 et) <= 32) by (clear - KT UR; change 18446744073709551615 with (Z.ones 64) in KT; rewrite Z.land_ones in KT by lia; Z.div_mod_to_equations; lia).
    clear KB KT.
    assert (CASES : bv_unsigned (sx32 et) = 1 \/ bv_unsigned (sx32 et) = 2 \/ bv_unsigned (sx32 et) = 3 \/ bv_unsigned (sx32 et) = 4 \/ bv_unsigned (sx32 et) = 5 \/ bv_unsigned (sx32 et) = 6 \/ bv_unsigned (sx32 et) = 7 \/ bv_unsigned (sx32 et) = 8 \/ bv_unsigned (sx32 et) = 9 \/ bv_unsigned (sx32 et) = 10 \/ bv_unsigned (sx32 et) = 11 \/ bv_unsigned (sx32 et) = 12 \/ bv_unsigned (sx32 et) = 13 \/ bv_unsigned (sx32 et) = 14 \/ bv_unsigned (sx32 et) = 15 \/ bv_unsigned (sx32 et) = 16 \/ bv_unsigned (sx32 et) = 17 \/ bv_unsigned (sx32 et) = 18 \/ bv_unsigned (sx32 et) = 19 \/ bv_unsigned (sx32 et) = 20 \/ bv_unsigned (sx32 et) = 21 \/ bv_unsigned (sx32 et) = 22 \/ bv_unsigned (sx32 et) = 23 \/ bv_unsigned (sx32 et) = 24 \/ bv_unsigned (sx32 et) = 25 \/ bv_unsigned (sx32 et) = 26 \/ bv_unsigned (sx32 et) = 27 \/ bv_unsigned (sx32 et) = 28 \/ bv_unsigned (sx32 et) = 29 \/ bv_unsigned (sx32 et) = 30 \/ bv_unsigned (sx32 et) = 31 \/ bv_unsigned (sx32 et) = 32) by (clear - HU; lia).
    clear HU.
    destruct CASES as [Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|[Hk|Hk]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
    - (* [comment removed for export] *) jt_go Hk. eapply arm_akid with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | hz_tac Hk | hsub_tac Hk | match goal with |- ?g => idtac "DISP-T1-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply arm_skid with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T2-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T3-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply arm_ku with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T4-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T5-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T6-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T7-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply arm_pol with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | hz_tac Hk | hsub_tac Hk | match goal with |- ?g => idtac "DISP-T8-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T9-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T10-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T11-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T12-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T13-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T14-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T15-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T16-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T17-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T18-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T19-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T20-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T21-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T22-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T23-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T24-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T25-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T26-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T27-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T28-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T29-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T30-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply default_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | match goal with |- ?g => idtac "DISP-T31-LEFT:" g end ].
    - (* [comment removed for export] *) jt_go Hk. eapply arm_san with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV1 | exact KLOOP | eassumption | hz_tac Hk | hsub_tac Hk | match goal with |- ?g => idtac "DISP-T32-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L16526487874.175L19616048289.178L2192452093.174 L22676661558.175L24188363034.175L32883993289.178L38339916114.17800002804@06A08B0:G0<R0=LS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz3HB12H22H32HLS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz2H12HL1i2Hi1HS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz2H12H3S2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz2H22HLS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz3HB02H12HLS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21B3bsx2P02Lz2H12H32HL1i2Hi1HS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  #[using="R HIA NS1 STKc STKc0 STKc1 LB LF sp PP CRT P END BUF lo slo bs LFB3 LFB PP0 BIN B1 B2 B3 DPB CRT0 DXB D1 SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APP APC SPR ALO ACV F0 APB D1u DXBu SP1R ENDX EX1 EX2"] Lemma bytes_at_slice : forall mX B bsx P0 Lz, bytes_at asegs mX B bsx -> B <= P0 -> 0 <= Lz -> P0 + Lz <= B + Z.of_nat (length bsx) ->
    bytes_at asegs mX P0 (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))
    /\ Z.of_nat (length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))) = Lz.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L14406737544.210L19246787633.2  L20509319872.160L31939843611.160L40228640085.0  L51907746211.2  L62369502168.160L64412859763.2  00000100200M00e00f00m01H01OFSS2sp2PP3CRT2bs2FB3sp12rg2RRS2sp2PP3CRT2bs2FB3sp12rgSS2rg2RRS2sp2PP3CRT2bs2FB3sp12rg2RRS2rg2RR". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 PP0 CWP PPLO BIN B1 B2 B3 B47 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma err_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (rg p' bp : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    -0x7f < rg < 0 -> BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaacc4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP Hp' RR HBUD HBP.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    (* [comment removed for export] *)
    do 3 zstep.
    first [ rewrite A_x509_get_san_A.swrap32_errsum'' by (clear - RR; lia)
          | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - RR; lia))
          | match goal with |- ?g => idtac "ERRSUM-LEFT" end ].
    zstep.
    eapply errj_walk with (p' := p') (bp := bp); first [ exact INV | eassumption | clear - RR; lia | match goal with |- ?g => idtac "ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03:0@C17025492443.313C65802607699.314D27847976046.314D47770555849.314D47776798540.292D54661255290.292D55639571502.292D55641685675.314D60109446735.314D60128441358.314D61543520757.292D61549796208.314K14848440079.313K25709469327.313K30222305807.313K33779218703.313K40145229071.313K45693719410.314K5284942906.314 K54542738319.313K55499728911.313K63014653711.313K8693187983.313 L11845198509.3  L12252132089.3  L13176305223.2  L13947844548.3  L14313191351.1  L14861253785.2  L15340755406.78 L15618147883.1  L16772787627.1  L17605243636.86 L19103996075.1  L19566614582.86 L19964894411.86 L21218866939.2  L21619350327.1  L22212138180.3  L23710709032.1  L24139200548.300L24796913220.3  L24882004373.71 L25713366297.2  L26393260740.86 L27111942217.1  L27789073007.1  L28931833527.1  L29407717531.1  L29680655011.1  L30226661785.2  L30747922934.5  L32497050292.86 L32866598340.3  L33308163853.86 L33740837294.0  L33783050905.2  L3480350366.86  L35655538583.72 L36463206329.4  L37605408727.73 L38235734261.1  L39478371757.86 L40132288153.2  L41122741931.1  L41409160545.3  L41832806413.86 L42419476660.1  L4370579368.1   L43927446468.3  L45689297124.2  L46059794920.1  L47289743172.3  L47348680317.2  L4872004339.2   L48843152936.1  L49207136770.3  L49339385823.86 L52941874306.3  L5297692588.3   L53266624065.86 L54410352043.1  L54555682841.2  L55085943702.3  L55512605593.2  L56157302580.86 L56560440097.0  L57394714052.3  L57757144503.1  L57850745591.1  L58511626801.3  L58678780634.6  L59003401692.86 L59308586248.2  L59967748674.3  L60056205954.3  L63001773209.2  L64686745924.3  L64850595401.0  L65642230468.3  L66925110933.285L7244092893.3   L8705412633.2   L881835912.0    L9090702513.71  L9476387309.86  L9644563342.71  N13257356329.314N20884620581.314N22787815853.314N35806358206.314N49089372318.314N64789588100.314O12233548996.313O1358745554.314 O13649862898.314O14175554244.313O1478916974.314 O16961596029.313O17025492443.313O20169458429.313O20458779460.313O22479346685.313O23601537266.314O24352547140.313O26475597711.314O27265912465.314O33870522200.314O34052634180.313O39013788797.313O41306367357.313O42395367124.313O43849271089.314O44531015165.313O44879841026.314O45696702077.313O45947445700.313O47737000900.313O47972003709.313O50689527441.314O50702732434.313O51150049554.313O53449798340.313O56414299794.313O57957320900.313O59625529265.313O65672115325.313O8067387102.312 P11860422666.313P12257878110.314P13953656163.313P21212095580.313P22197995107.313P24812063971.313P30744236914.314P32881815395.313P36465839390.314P41419110342.313P43934249315.313P47284020707.313P47359677658.314P4875970917.314 P49191944357.313P52940256805.313P55088519473.314P57379456867.313P58510033046.312P58674176094.314P59973560549.314P60050384933.313P64680999907.313P65640603747.313Q11148838878.314Q15605927357.314Q15766564435.314Q16670484879.314Q19561449455.285Q23890870216.310Q26318654066.314Q31124869336.314Q31615214184.310Q32681607669.314Q34363165844.314Q34671225381.285Q34964382778.314Q42439168719.314Q43649455646.285Q44949385150.285Q47061991091.314Q48118064779.314Q48360113622.314Q49746198710.314Q51518068631.314Q543084191.314  Q58496806552.314Q62380812747.314Q67038703949.314Q7757734246.285 Q8699324297.314 Q9356559679.292 Q9633967632.285 Q9644583048.314 00000100501O01P01Q02<02=02>03203]04H05305X06=06b07G07l08P09109V0:;0:`0;E0;F0;G0;O0;P0;T0;U0=E0=I0=M0?K0?O0BF0DT0DU0DY0DZ0D^0D_0D`0E>0E?0FG0FK0FO0FP0FT0FY0FZ0F[0I60I70IO0IP0IQ0KQ0MC0MD0Ml0N00NM0NN0NR0NS0Nk0No0O30O40O50O90O:0O;0O<0O@0OA0QG0QH0QI0Q^0Qb0Qc0Qd0Qe0Sc0Sd0Se0Si0Sm0Sn0So0V:0V@0VA0VB0VC0VD0VE0VF0W10W<0W=0W>0WZ0X70XO0Y20Y`0ZG0[@0[A0[d0[e0[f0[g0[h0[i0[j0[k0[l0[m0[n0[o0\00\10\20\30\40\50\60\70\80\90\:0\;0\<0\=0\>0\?0\@0\A0\B0\C0\D0\E0\F0\G0]00]Y0^E0^F0_20_^0aQ0b=0bd0cM0d90de0ek0fi0gR0h;0hc0iO0jU0k\0lE0ln0mZ0nF0nG0nd0oK0oL10A11811`11a12c12d12e13B14@14e15g16^16_17]18E19819919V1:31:X1;Z1<71=21=U1>51>UFS2FBS1R3HIA1h2LF2sp2PP3CRT3BUF2lo2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc2OL2OP3HTcFFS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPFFS1R2LF2sp2PP3CRT3BUF2lo2bs4LFB33LFB3LOS2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF2PP3BUF2bs4LFB33LFB2FB3APP2OL2OPS2LF3BUF2bs4LFB33LFB2FB3APB2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPFFS2lo3sp1FS2FBFS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22OL2OP2e93HE94HOP2S2FBS2FBS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2FBS1R2sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13APP3APC5BUFLO3SPR3ALO2F02F14FBLO3APB6CRTLOu3D1u4DXBu4SP1R4ENDX3EX22OL2OP1q2p02e93HP03HQ03HQE3HE94HOP2S1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2FBFS2FBFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2sp2PP3CRT3BUF2bs3PP02B54CRT02D12FB3sp13APP3APC3SPR2F03D1u4SP1R2OP4HOP1S2PPS2FBFS2FBS3CRTFFS1R3NS14STKc5STKc32sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT2bs2FB3sp12F0SFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2sp2PP3CRT3BUF2bs2D12FB3sp13D1u2OP4HOP1S2loS2sp2PP3CRT2lo2bs2FB3sp14FBLOFS2FBFS2sp2PP3CRT2bs2FB3sp12F0S2FBS2FBFFS2FBFFFS2FBFS1R3NS14STKc5STKc12sp2PP3CRT3END3BUF2lo2bs3PP04PPLO2B34CRT02D13SPH2FB3sp15BUFLO3SPR3ACV2F02F14SLOu3D1u4SP1R4ENDX3EX22OL2OP2e93HE94HOP2FFS2sp2PP3CRT2bs2FB3sp1S2FBFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9SFS2FBS2FBFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22OL2OP1q2p02e93HP03HQ03HQE3HE94HOP14HOP2S1i2HiFFFFSFS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2sp2lo3sp1FSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2sp2PP3CRT2lo2bs2FB3sp14FBLOS2sp2PP3CRT2bs2FB3sp12F0S2LF3BUF2bs4LFB33LFB2FB2OL2OP3x331CS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OP3x331CS2LF3BUF2lo2bs4LFB33LFB3sp12OL2OP3x331CS1R2LF3BUF2lo2bs4LFB33LFB3LOS2FB3sp13ALO2OL2OP4SBND3x331CFS2LF3BUF2bs4LFB33LFB2FB2OL2OP3x331CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF2PP3BUF2lo2bs4LFB33LFB4PPLO3sp12OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPFS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF2PP3CRT1P3END3BUF2bs4LFB33LFB2B12B22B33DPB2FB3APP3APC3APB4DXBu4ENDX3EX22OL2OP1q2bp2e93HQE3HE93HBP4HOP14HOP23HXLS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3BUF2lo2bs4LFB33LFB3sp15BUFLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB4FBLO4SLOu2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2OL2OPS2LF3END3BUF2lo2bs4LFB33LFB2B33sp15BUFLO4ENDX3EX22OL2OP2e93HE94HOP23HXLS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPFS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R2LF3BUF2lo2bs4LFB33LFB3LOS3ALO2OL2OPFS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp13SPR2F02F82OL2OPS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcS2LF3CRT3BUF2lo2bs4LFB33LFB6CRTLOu2OL2OPFS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPFFS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP14SLOu2OL2OPS1R2LF3BUF3slo2bs4LFB33LFB4SLOS2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcFS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3ALO4SLOu2OL2OPS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OPS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp12OL2OP5HTOPcFS2LF3BUF2bs4LFB33LFB2FB2OL2OPS2LF3BUF2bs4LFB33LFB2FB2OL2OPS2LF2PP3BUF2lo2bs4LFB33LFB4PPLO2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R3HIA1h2LF2sp3BUF3slo2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcS2LF3BUF2bs4LFB33LFB3sp14SP1R2OL2OPS2LF3BUF2bs4LFB33LFB2FB2F02OL2OPS2LF3BUF2bs4LFB33LFB2FB2F02OL2OP". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma oidl_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (OL OP q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    BUF <= OP -> 0 <= OL -> OP + OL <= e9 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaa00) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HOP1 HOL HOP2 KLOOP.
    open_xinv_mu INV hc.
    destruct (bytes_at_slice _ BUF bs OP OL HBUF HOP1 HOL ltac:(xl HOP2 HE9 EX2)) as [HXS HXL].
    (* [comment removed for export] *)
    do 3 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 64) 3%nat as OOID.
    assert (OETY : aobj asegs AL (hcs asegs R HIA hc) mg (FB + 144) 4).
    { eapply (aobj_of_part_shadow_sh asegs AL (hcs asegs R HIA hc) mg FB _ (FB + 144) 18%nat 4 CSOKc FSH);
        [eapply crange_sub; [exact CFBc| clear; lia| clear; lia]| exact F8| xl| clear; lia| clear; lia| reflexivity]. }
    chunk_split FLOCc 2%nat FL0 FL1. chunk_split FL1 4%nat FOID FL2. chunk_split FL2 3%nat FL3 FL4. chunk_split FL4 1%nat FET FL5.
    replace (FB + 32 + 32) with (FB + 64) in * by (clear; lia). replace (FB + 64 + 24) with (FB + 88) in * by (clear; lia).
    replace (FB + 88 + 56) with (FB + 144) in * by (clear; lia). replace (FB + 144 + 4) with (FB + 148) in * by (clear; lia).
    pose proof (A_oid_get_x509_ext_type_spec R HIA OIDH) as SPO. unfold oid_lookup1_stmtA, A_OID_GET_X509_EXT_TYPE in SPO.
    idtac "OIDL-CALL".
    lazymatch goal with HHx : HM _ _ _ hc ?lbx _ mg |- _ =>
      acallxA_sp sp1
        (eapply SPO with (h := hc) (LB := lbx) (LF := LF') (OID := FB + 64) (EXT := FB + 144) (P := OP) (LEN := OL) (lo := lo) (tg := otg) (pd := opd) (v0 := et)
                         (xs := firstn (Z.to_nat OL) (skipn (Z.to_nat (OP - BUF)) bs));
         rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold buf_cells;
         first [ exact HHx | exact FOID | exact FET | exact HXS | exact HXL | exact OOID | exact OETY | eassumption | reflexivity
               | (eapply aobj_sub; [exact OBUF| xl HOP1 | xl HOP2 HE9 EX2])
               | xside HOP1 HOL HOP2 HE9 EX1 EX2 HP0 HQ0 HQE
               | match goal with |- ?g => idtac "OIDL-LEFT:" g end ]) end.
    idtac "OIDL-BACK".
    match goal with H : rw_cells _ _ (FB + 144) [C4 ?v] |- _ => rename v into etv; rename H into FET end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into ro end.
    match goal with H : ro = 0 \/ _ |- _ => rename H into Hro end.
    joinc FL0 FOID. joinc FL0 FL3. joinc FL0 FET. joinc FL0 FL5.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 etv j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "OIDL-KNOWN".
      eapply dispatch_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV2 | exact KLOOP | eassumption | match goal with |- ?g => idtac "OIDL-DISP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 2 zstep.
    idtac "OIDL-UNKNOWN".
    eapply unknown_walk with (q := q) (p0 := p0) (bp := bp) (e9 := e9); first [ exact INV2 | exact KLOOP | eassumption | match goal with |- ?g => idtac "OIDL-UNK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@C40858145355.309C60410007123.308D10636937134.309D16071854214.309D16901939902.309D2457516971.309 D32458870384.309D39243574473.309D46794843979.309D60109446735.309D66237350158.309K1093189274.307 K12719279130.307K16483843482.307K17012660943.307K20040736922.307K20981739667.307K24527616463.307K26389978266.307K27873714767.307K28081892559.307K29378133114.309K30993319891.309K33674735898.307K41744454554.307K42309482703.307K45300827802.307K49805008847.307K53361377999.307K54996069696.308K56707495759.307K62527904282.307K65858155712.308K67776174415.307L10039789130.189L10039789130.298L10044042153.299L10079012065.2  L10323762809.81 L1103920410.2   L12729978778.2  L12865196093.88 L12867456647.85 L13527341863.85 L13529531805.88 L13636442081.2  L13946884974.189L13946884974.298L14402536676.3  L14402536676.300L15940222605.299L16482024986.2  L17025536345.2  L17698511111.81 L18501743953.81 L19700477810.81 L20038394650.2  L20407675145.189L20977711877.2  L21122558689.2  L21230010724.3  L21654730866.2  L24514671193.2  L24697106893.189L24882004373.71 L2621559066.1   L26375085850.2  L27111942217.1  L27832549545.283L27877616089.2  L27940752049.81 L28068947801.2  L29391009772.3  L29680655011.1  L30507144274.2  L30997223346.3  L31320619992.2  L32749673313.2  L33685467802.2  L3482445080.81  L35248710037.81 L35655538583.72 L35916062914.81 L36307103329.2  L38235734261.1  L40058613985.2  L40228640085.0  L4086203097.189 L41114250170.81 L41202929119.299L41251426164.1  L41755152410.2  L42296603481.2  L42383166414.189L42488948659.2  L43317526968.81 L45193043736.24 L45311526170.2  L45382656977.84 L47870616696.2  L48937103345.300L49233373885.2  L49800647769.2  L5021251703.1   L50678314462.3  L53357021529.2  L53506586542.298L53530411688.1  L53704106081.2  L55008356054.2  L55182816650.81 L55504905889.0  L5659140096.84  L56719719641.2  L5685787249.3   L57083180513.2  L57389346443.81 L576250137.299  L58972694988.81 L59308586248.2  L6008604205.3   L60558678699.1  L61774255627.2  L62275882349.3  L62417043471.88 L62513011098.2  L62873986039.1  L64179129035.1  L64850595401.0  L65331221217.2  L656832749.85   L65862516566.2  L66298372189.2  L66812728480.3  L67070089790.2  L67763426009.2  L866928845.84   L881835912.0    L9090702513.71  N15340698282.308N18792612241.308N26872553873.308N48204456022.308N60733400192.308N66590330291.308O12232075104.307O14559438816.307O14912726833.308O151759997.307  O15540865262.307O16086026184.308O16723931389.307O18988691132.308O20866770946.309O21058125422.307O22525005962.308O2463212925.307 O24727989486.307O25722042592.307O25895279840.307O30010457231.308O34618340093.307O3493317847.307 O37559489567.309O37860830077.307O3821773283.309 O41222319070.306O424351700.307  O43490832480.307O44938202843.307O45423855982.307O46148948448.307O4719021806.307 O49076961262.307O49701823576.308O50011839873.307O52019636960.307O55209884805.307O55738917358.307O59000851965.307O59916692861.307O61256669038.307O64251960330.308O64474006218.308O66521921705.306O66725143264.307O6754613856.307 O6815798909.307 O8878376686.307 O9125703549.307 P10069038662.307P13625410886.307P21137750086.307P21231604675.306P21647862485.307P30511339222.308P32763840966.307P36322327750.307P40051745350.307P42484919333.308P47876372191.307P49230739482.308P50671478649.307P53719298758.307P5671676118.306 P57084798790.307P61788423340.308P62260666314.307P65345388614.307P66292560634.308P66818508295.309P67064334489.308Q10592389669.307Q10592533181.309Q10598691865.283Q10636937134.309Q10637080374.307Q10649498890.308Q11133374175.309Q11657053839.309Q13731015691.307Q15673955380.307Q16071854214.309Q16178735000.309Q17027695041.309Q17681074618.309Q17701933584.308Q18824847950.308Q19561451475.283Q21767670690.309Q27573751300.309Q2803826605.309 Q29775981542.309Q3166354565.308 Q32681607669.309Q36985122307.309Q39600066516.308Q40904410655.309Q40916972731.308Q42439168719.309Q45360064137.307Q46794843979.309Q48118064779.309Q49746198710.309Q5638148954.283 Q56530976407.309Q57828105177.309Q60314416515.309Q6132825310.309 Q61847600945.308Q67026529334.308Q67038703949.309Q8699324297.309 Q9356559674.286 Q9633965612.283 Q9644583048.309 00000400800Y02003=03>03_03`04A04k05L05g06B06]07807S07m08H08c09>09Y0:40:O0:j0;E0;`0<;0<V0=10=K0=f0>A0>[0?60AH0Cf0FD0FE0Gj0Gk0Gl0J80LD0NF0PH0PI0RU0Tm0U80U90W[0W\0W]0Y[0\Z0^[0^\0^]0^^0^_0^`0^a0^b0`80`V0`[0`\0``0aA0aB0c]0c^0c_0cd0ce0cf0cn0co0d00f30h90ik0jH0jI0jM0jN0jO0jo0kL0km0l10l20l30m>0m?0mX0mn0mo0nW0nX0o90o:0o;0o<0o=0o>0o_0oc0od0oe12`12a14V14W14X14Y15115R15o16516@16D16E16F16l16m17117217317417I17J17K17L17M17N19<19=19Y1:21:31:L1:m1;g1=11=21=31=41=51=61=71=81=91=:1=;1=<1==1=>1=?1=@1=A1=B1=C1=D1=E1=F1=G1=H1=I1=J1=K1=L1=M1=N1=O1=P1=Q1=R1=S1=T1=U1=V1=W1=X1=Y1=Z1=[1=\1=]1=^1>]1?\1@[1AW1AX1BL1CK1DJ1EI1F=1G91H51HT1IS1JU1KT1LP1Lo1Mn1NI1OG1PC1PV1Pi1Q<1QO1Qb1R51RH1RI1R\1Ro1Sg1T:1TM1UI1U\1VI1W41X01X11XE1X`1Xa1Xb1Xc1Xd1Xe1Xf1YA1YT1Yg1Z[1[D1[W1[X1\E1]D1]E1^?1_71_o1``1a91aO1aeS2PPS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTcFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3BUF2bs4LFB33LFB2FB3APBS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LFS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e43HE4FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02bp2e43HQ03HE43HBP2q43Hq44Hq4aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02bp2e43HQ03HE43HBP2q43Hq44Hq4aS2rg3RRg2KzFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43Hq43LR44Hq4a4Hq4LFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFFFFFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R1q2p02bp3HQ03HBP2q43Lw43LR44Hq4aS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S3sp1FS2PPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFS3CRTFFS2sp3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs2FB3sp13APBFS2loFSS2sp2PP3CRT2bs2FB3sp12q43Lw43LR4S2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2FBFFS2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02FB3sp13SPR2F04SP1R1q2p03HP03HQ02q44Hq4aFS2sp2PP3CRT2bs2FB3sp13APPS2bs2e42q43Lw44Hq4L2KmFS2sp2PP3CRT2bs2D12FB3sp13D1u1q2e42q43Hq4FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2FBFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4SS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02bp3HQ03HBP2q44Hq4aFFFS2sp2PP3CRT2bs2FB3sp12F0S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT3BUF2bs3B472FB3sp1S1i2HiS2rg3RRg2KzS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNFS2FBFSFS2sp2PP3CRT2bs2FB3sp1FFFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p03HQ02q44Hq4aSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2LF2bs4LFB33LFB2FB3x341CFS2LF2bs4LFB33LFB2FB3x341CS2LF2sp2bs4LFB33LFB3sp13SP13x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu3x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2lo2bs4LFB33LFB2FB3sp14FBLOS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP1S1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBFS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOuFS2LF2bs4LFB33LFB3sp1S2LF2sp2bs4LFB33LFB3sp13SP1FFFFFFS1R2LF3slo2bs4LFB33LFB4SLOSS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPcS2LF2bs4LFB33LFB2FBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB3sp14SP1RS2LF2bs4LFB33LFB2FB2F0S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma octet_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE4 HBUD HBP HOP1 HOL HOP2 KLOOP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 5 zstep.
    frame_aobj FSH (FB + 32) 1%nat as OLEN.
    chunk_split FLOCc 1%nat FLEN FLr. replace (FB + 32 + 8) with (FB + 40) in FLr by (clear; lia).
    idtac "OCT-GT".
    gt_call OLEN FLEN q e4 (FB + 32) 4 ltac:(xl HP0 HQ0 HQE HE4 EX1 EX2).
    idtac "OCT-GT-BACK".
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw4; rename H into FLEN end.
    match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q4 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HLg end.
    match goal with H : _ < rg <= 0 |- _ => rename H into RRg end.
    match goal with H : _ <= q4 <= e4 |- _ => rename H into Hq4 end.
    pose proof (bv_unsigned_in_range 64 Lw4) as LR4. unfold bv_modulus in LR4. cbn [Z.pow Z.of_N Pos.pow] in LR4.
    joinc FLEN FLr.
    fold_xinv INV2 hc Lx X (FLOC Lw4 j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "OCT-GT-ERR".
      assert (RN : rg <> 0) by (clear - Kz RRg; intros ->; apply Kz; reflexivity).
      eapply err_walk with (rg := rg) (p' := q4) (bp := bp);
        first [ exact INV2 | eassumption | xl HP0 HQ0 HQE HE4 EX1 EX2 Hq4 RRg RN HBP | match goal with |- ?g => idtac "OCT-ERR-LEFT:" g end ]. }
    assert (Rg0 : rg = 0) by (clear - Kz RRg; try kland Kz; rewrite ?unsigned_lit in Kz by lia; rewrite ?Z_to_bv_unsigned in Kz; unfold bv_wrap, bv_modulus in Kz; cbn [Z.pow Z.of_N Pos.pow] in Kz; Z.div_mod_to_equations; lia).
    subst rg. destruct (HLg eq_refl) as [Hq4a Hq4L]. clear HLg Kz RRg.
    (* [comment removed for export] *)
    do 5 zstep.
    (* [comment removed for export] *)
    zstep. if_cases Km; zify_cond Km.
    { idtac "OCT-MISMATCH".
      (* [comment removed for export] *)
      do 2 zstep.
      rewrite (zbv_wrap 18446744073709542042).
      eapply errj_walk with (p' := q4) (bp := bp);
        first [ exact INV2 | eassumption | xl HP0 HQ0 HQE HE4 EX1 EX2 Hq4 HBP | (clear; lia) | match goal with |- ?g => idtac "OCT-MIS-LEFT:" g end ]. }
    assert (E9 : q4 + bv_unsigned Lw4 = e4) by (clear - Km HP0 HQ0 HQE HE4 EX1 EX2 Hq4 Hq4L LR4 B1 B3 B5 B47; try kland Km; rewrite ?Z.mod_small in Km by lia; lia).
    rewrite E9.
    idtac "OCT-OIDL".
    eapply oidl_walk with (q := q4) (p0 := p0) (bp := bp) (e9 := e4) (OL := OL) (OP := OP);
      first [ exact INV2 | exact KLOOP | eassumption | xl HP0 HQ0 HQE HE4 Hq4 Hq4a HBP | match goal with |- ?g => idtac "OCT-OIDL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Loop.
  End Body.
  End Call.
End Walk.
