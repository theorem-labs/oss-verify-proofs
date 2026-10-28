(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_parse_san_A A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E.
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
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
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
Local Ltac zchk_brute :=
  unfold_cond; fold_lit_ux;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
         end;
  repeat match goal with
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         end;
  first [ reflexivity | vm_compute; reflexivity | exfalso; zlia ].
Local Ltac zchk_solve :=
  rewrite ?zchk_land7;
  zchk_dec;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with
                 | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
                 | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit64 x) by zlia
                 end;
          zchk_rec
        | zchk_brute ].
Local Ltac zchk_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xae8d0 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xae8d0) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zstep ::= step; zsimp; repeat zchk_if.
Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43150339301.25000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).
  Local Notation sfr := (A_x509_san_ext_C.sfr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs).
  Local Notation svA := (A_x509_san_ext_C.svA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs).
  Local Notation Wc := (A_x509_san_ext_C.Wc PP).
  Local Notation nLB := (A_x509_san_ext_C.nLB LB).
  Local Notation nfreshA := (A_x509_san_ext_C.nfreshA R LB LF PP CUR).
  Local Notation curFA := (A_x509_san_ext_C.curFA CUR).
  Local Notation headrep := (A_x509_san_ext_C.headrep CUR END BUF).
  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).
  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).
  (* [comment removed for export] *)
  Ltac fin_sfr t :=
    unfold A_x509_san_ext_C.sfr;
    spine; first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (unfold A_x509_san_ext_A.rsl; eassumption)
                 | (repeat split; eassumption) | reflexivity | solve [t] | match goal with |- ?g => idtac "SFR-LEFT:" g end ].
  Local Notation ERRQ := (A_x509_san_ext_D.ERRQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation CALLQ1 := (A_x509_san_ext_D.CALLQ1 R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation EXITP := (A_x509_san_ext_E.EXITP R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L27111942217.1  L35177111487.1  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L43300649301.0  L45569475286.216L50797055232.13 L56380991837.10 L56475376854.218L59176156076.3  L60098763854.6  L64850595401.0  L9080220944.4   L9102618472.3   L9356559676.18  Q30263103398.228Q3067468761.228 Q3069256409.227 Q35042537576.229Q41569180220.227Q43414146086.230Q53545822440.227Q60795410781.228Q62457807837.230Q66309980860.229Q9077729369.230 Q9080100697.229 00000400900Q00U00V00W00X02;02d03=04`04l05605705F05R06O07M07\07k08:08I09G09V09e0:40:C0:R0:aS2PPS3curS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp13cur4CPOS3CLO4NRTa3SPR4SP1R2F0S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS1R3BUF2lo2bs3LOS3ALO3BCES1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPH2FB3sp13cur4CPOS3CLO4NRTa3SPR4SP1R2F0S3cpp3CPR2K0S1R2lo3LOSSS2sp2lo3sp13SP1S3cpp3CPR2K0S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13cur3CAL4CPOS3SPR4SP1R2F0S2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13cur3CAL4CPOS3SPR4SP1R2F0S2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP BIN CUR0 CWC SLOS SLOL SLO TOP SPH LOS"] Lemma seg3 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp : Z) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp 0 mm ->
    0 <= cpp < 2^64 ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms =>
         (cpp = 0 /\ exists (a0' a1' s10' : word), ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0' a1' a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                                  (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10' (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                             F (Z_to_bv 64 0xae7e8) fc None mm (seg_rom asegs))
         \/ (cpp <> 0 /\ ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 1) (Z_to_bv 64 32) a2 a3 a4 a5 a6 a7
                                  (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP)
                                  (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64))
                                  (Z_to_bv 64 (Z.shiftr (cur + 24) 3 + al_sb AL)) (Z_to_bv 64 (cur + 24)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                             F (Z_to_bv 64 0xae7d0) fc None mm (seg_rom asegs)))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae784) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D CPR. sfr_open D.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    pose proof (hm_abase asegs R HIA hc _ _ mm HHc) as AB0.
    (* [comment removed for export] *)
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    { assert (C0 : cpp = 0) by (clear - K0 CPR; kland K0; rewrite ?Z.mod_small in K0 by lia; lia).
      apply evtA_done. left. split; [exact C0|]. deexists 3. reflexivity. }
    assert (CN0 : cpp <> 0) by (clear - K0 CPR; kland K0; rewrite ?Z.mod_small in K0 by lia; lia).
    (* [comment removed for export] *)
    do 6 zstep.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    apply evtA_done. right. split; [exact CN0| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@D11532395422.225D29401369980.225D60109196847.225K14662993782.225K44164039966.225K48593550302.225K52599012741.225K59713869701.225L13059311132.0  L14647789168.2  L1685717371.0   L27111942217.1  L33766366300.2  L35177111487.1  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L43300649301.0  L44166661144.3  L48596171480.2  L50797055232.13 L52610022531.2  L56380991837.10 L57130527895.2  L59723830915.2  L60098763854.6  L62586168108.2  L64850595401.0  L9080220944.4   L9356559676.18  P33760599386.225P57140489617.225P62587740714.225Q1101800120.222 Q11530185118.224Q11532395422.225Q29399418748.224Q29401369980.225Q35042506344.221Q42439443119.225Q43414146086.222Q43622973458.223Q57329886304.225Q62457807837.222Q64683667846.225Q66310014140.221Q66733290487.222Q67866883671.222Q9077729369.222 Q9080131929.221 00000_01N02F02l03R04704]05C05D05E05F05J05K05P05h05l05m05n05o06006106Z06[07407507607@07A07B07Q08N09\0:b0<00<G0<e0=C0=a0>?0>N0?70@50@M0@N0@]0AS0Ab0B]0CD0CS0CbS2LF2sp2PP3CUR2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp13cur2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp13cur2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB3cur3CBF2HB5Ha_st5Hl_stS2LF2PP2bs3LFB3cur3CPP2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur4CFBa2HB5Ha_st5Hl_stSFSS2PPFS3curS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSFFS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaFS1R3BUF2lo2bs3LOS3ALO3BCEFFS1R2lo3LOSFSS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp13cur3SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3cur3CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp13cur3SP13CLO4NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB3cur4CPOS2HBS2LF2bs3LFB3cur2HB5Ha_st5Hl_stS2LF2bs3LFB3cur2HB5Ha_st5Hl_stS2LF2bs3LFB3cur2HB5Ha_st5Hl_stS2LF2bs3LFB3cur2HB5Ha_st5Hl_stS2LF2bs3LFB3curS1R2LF3slo2bs3LFB4SLOS3cur2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13cur3CAL4CPOS3SPR4SP1R2F0S2LF2bs3LFB3cur2HB5Ha_stFS2LF2bs3LFB3curS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3cur4HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB3curS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS2LF2bs3LFB3curS2LF2bs3LFB3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP BIN CUR0 CWC SLOS SLOL SLO TOP SPH LOS"] Lemma seg4_null : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp : Z) (mm : mem)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 0) k0 (Z_to_bv 64 (-9578)) k16 k24 k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp 0 mm ->
    evtA asegs AL (hcs asegs R HIA hc) (ERRQ hc Lh FB sp1 k0 (Z_to_bv 64 (-9578)) k16 k24 k48 cur ctc cpc clc cpp 0 mm)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP)
               (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64))
               (Z_to_bv 64 (Z.shiftr (cur + 24) 3 + al_sb AL)) (Z_to_bv 64 (cur + 24)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae7d4) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D. sfr_open D.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    pose proof (hm_abase asegs R HIA hc _ _ mm HHc) as AB0.
    (* [comment removed for export] *)
    do 4 zstep.
    (* [comment removed for export] *)
    zstep.
    do 4 zstep.
    apply evtA_done. unfold ERRQ.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    exists (-9578). repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [clear; lia|].
    split; [fin_sfr ltac:(idtac) | eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00d0@D11532395422.233D29401369980.233D60109196847.233K14662993782.233K44164039966.233K48593550302.233K52599012741.233K59713869701.233K64521742742.233L14647789168.2  L1685717371.0   L27111942217.1  L29765672786.217L33766366300.2  L35177111487.1  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L43300649301.0  L44166661144.3  L48596171480.2  L50797055232.13 L52610022531.2  L56380991837.10 L57130527895.2  L59308628179.6  L59723830915.2  L60098763854.6  L62586168108.2  L64515273836.2  L64850595401.0  L9080220944.4   L9356559676.18  P33760599386.233P57140489617.233P62587740714.233Q1101800120.230 Q11530185118.232Q11532395422.233Q29399418748.232Q29401369980.233Q35042506344.229Q42439443119.233Q43414146086.230Q43622973458.231Q57329886304.233Q62457807837.230Q64683667846.233Q66310014140.229Q9077729369.230 Q9080131929.229 00000a01R02L03403\04C04k05S06906:06;06?07G07H07M07e07i07j07k07l07m07n08W08X09109209;09<09F09G09H09I09X0:U0;e0<m0>=0>T0?40?T0@40@T0@c0AN0BL0Bd0Be0C40Cl0D;0DJ0DYS2LF2sp2PP3CUR2bs3LFB2FB3sp13cur1N2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp13cur1N2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp13cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS2LF3BUF2bs3LFB3cur1N3CBF2HB5Ha_st5Hl_stS2LF2PP2bs3LFB3cur1N3CPP2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3cur1N4CFBa2HB5Ha_st5Hl_stS2LF2bs3LFB3cur1N5APcur2HB5Ha_st5Hl_stFSS2PPS1R2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13cur1N4CPOS2N02NC3ACV3SPR4SP1R2F0FS3curS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSFFS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaFS1R3BUF2lo2bs3LOS3ALO3BCEFS1N2N02K0FS1R2lo3LOSFFSS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp13cur1N3SP13CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3cur1N3CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp13cur1N3SP13CLO4NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB3cur4CPOS2HBS2LF2bs3LFB3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB3cur1N2HB5Ha_st5Hl_stS2LF2bs3LFB3curS1R2LF3slo2bs3LFB4SLOS3cur1N2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13cur3CAL4CPOS3SPR4SP1R2F0S2LF2bs3LFB3cur2HB5Ha_stFS2LF2bs3LFB3curS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3cur1N4HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB3curS2LF2bs3LFB3curS2LF2bs3LFB3cur". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP BIN CUR0 CWC SLOS SLOL SLO TOP SPH LOS"] Lemma seg4_node : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur N : Z) (ctc cpc : word) (clc cpp : Z) (mm : mem)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp 0 mm ->
    rw_cells asegs mm N [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
    0 < N -> N + 32 <= alloc_ceiling -> (N + 32 <= cur \/ cur + 32 <= N) -> (PP + 8 <= N \/ N + 32 <= PP) -> (FB + 256 <= N \/ N + 32 <= FB) ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms => exists (mm' : mem) (w0' w1' w2' tl' : word) (j64' jn' : list byte) (a0' a1' s10' : word),
         ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0' a1' a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                      (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 N) s10' (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xae7e8) fc None mm' (seg_rom asegs)
         /\ sfr hc Lh FB sp1 w0' w1' w2' tl' (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64' tg pd ln pv jn' p cur ctc cpc clc cpp N mm'
         /\ rw_cells asegs mm' N [CB 32 (repeat (Z_to_bv 8 0) 32)]
         /\ presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc cur) mm mm')
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP)
               (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64))
               (Z_to_bv 64 (Z.shiftr (cur + 24) 3 + al_sb AL)) (Z_to_bv 64 (cur + 24)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae7d4) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D NZ N0 NC APcur NPP NFB. sfr_open D.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    pose proof (hm_abase asegs R HIA hc _ _ mm HHc) as AB0.
    (* [comment removed for export] *)
    do 4 zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0 N0 NC ACV; kland K0; rewrite ?Z.mod_small in K0 by lia; lia|].
    apply evtA_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [fin_sfr ltac:(idtac) |]. split; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma rw_cells_blob' : forall mq A0 cs, rw_cells asegs mq A0 cs -> rw_cells asegs mq A0 [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    clear. intros mq A0 cs H. pose proof H as H'. destruct H' as [[Hwf _] _].
    eapply rw_cells_reshape; [exact H| cbn; split; [apply cells_bytes_length; exact Hwf| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0400@C17025492443.252C58610189443.253D27847976046.253D28498761192.251D4451634193.251 D60109196847.251D60109446735.253D7166328948.253 D7711982088.253 K2431698795.251 K27828321123.253K39533642975.253K40357714920.251K44164039966.251K46571346844.253K50026579861.253K51995598935.253K53681487260.253K64038415723.251K9840090748.251 L10607040861.2  L12252132089.3  L13176305223.2  L13429559224.3  L13634871270.13 L14004562497.1  L15934535645.1  L16720091990.13 L16772002776.251L1685717371.0   L19980016842.7  L21218866939.2  L21472756189.3  L23182876091.2  L23513658539.2  L24023900370.0  L2419170461.2   L26341001237.13 L27111942217.1  L27600769099.13 L27818631954.2  L30251340380.4  L35249142376.3  L35653441506.13 L36125313021.12 L36463206329.4  L36495035983.2  L38235734261.1  L38692635477.0  L39263166881.0  L39332637397.0  L39540710574.2  L40351945721.2  L40390944894.3  L41202929119.237L41409160545.3  L42411609006.0  L42987094779.2  L43300649301.0  L43370515344.1  L44168742175.3  L45550567929.1  L45561584168.247L46039367185.3  L46564279277.2  L49015591532.3  L49444411156.2  L50016819191.2  L50797055232.13 L52001060902.3  L52568202056.1  L52941874306.3  L53271535775.237L53670749677.2  L54261998223.2  L55085943702.3  L56380991837.10 L57781587882.251L58800853620.11 L59308586248.2  L60056205954.3  L60098763854.6  L6180070147.4   L6305950207.14  L64009471222.1  L64010811431.0  L64025917085.2  L64041324646.11 L64179039535.1  L64850595401.0  L65221962844.1  L66151427842.16 L7701224057.1   L7809393150.2   L881835912.0    L8827747003.7   L9080220944.4   L9356559676.18  L9817103278.244 L9819744892.237 L9835808138.2   O1478916974.253 O17025492443.252O18035660929.253O19792103183.253O21791150237.251O2739346461.253 O28514787611.252O36307779889.253O36846146150.253O37177802714.253O43849271089.253O44766544199.253O50689527441.253O50702732434.253O54061950545.253O54197161434.253O56414299794.253O58610189443.253O59625529265.253P12257878110.253P17794074698.260P21212095580.252P23170010975.251P23511823980.251P36465839390.253P36501589128.251P38605639612.260P40396402703.251P41419110342.253P42993179274.253P46045341280.253P49008495133.252P49454059365.253P50026579861.253P52940256805.253P53346601986.260P54268551240.251P55088519473.253P60050384933.253P61642083433.260P7740881908.260 P7815379343.253 Q10592318621.256Q10639171022.250Q10649498890.248Q10651864077.247Q10821824020.260Q12658605510.260Q12658605510.262Q13002548137.254Q13732992816.247Q14986738841.254Q15010535802.254Q15766564435.253Q17425018425.254Q17701933584.248Q17716263636.250Q18089490443.254Q18099926581.254Q18850126409.254Q20459834793.254Q20851854948.254Q22444220057.254Q23869344553.254Q2388889303.254 Q26307634249.254Q26314584654.260Q26316671538.247Q28496781288.250Q28498761192.251Q29732373684.254Q30441621867.254Q31124869336.253Q31326836009.254Q31526414380.260Q33283861378.260Q34363165844.253Q34390149656.248Q34669208220.255Q34877581972.254Q34964382778.253Q35239537471.253Q35323800637.248Q37216054521.248Q37442814213.253Q37777260077.253Q3865442997.255 Q38802716825.256Q39600066516.248Q40324761936.251Q40599399476.254Q42376373047.253Q42439168719.253Q42439443119.251Q42441548847.260Q43138029699.260Q43922358489.254Q43964130321.252Q44172294453.255Q44298944140.247Q44298944140.255Q44301027056.260Q4451634193.251 Q4453582353.250 Q45353655730.247Q45482765142.262Q46563038180.253Q48119910507.260Q48360113622.253Q49785721508.254Q50059752051.254Q504873378.252  Q51107054235.255Q51379872473.254Q51959565844.254Q53798965253.247Q54789931780.254Q5525646475.254 Q5532017333.254 Q55435349233.253Q5596578838.260 Q58650752521.254Q58668001817.246Q58972088531.257Q59617553652.254Q59619599050.254Q61381344394.253Q61556549392.249Q61847600945.248Q62380812747.253Q62715864643.251Q63211362725.247Q63435846322.255Q63667759319.254Q63811190484.254Q64228675114.259Q64681563910.260Q64683667846.251Q64683942374.253Q65123540362.254Q65654860420.254Q6575031993.254 Q66108231689.254Q66279660824.255Q66901779611.255Q67038986090.253Q67125756313.246Q67837027513.254Q6912043757.257 Q7166328948.253 Q7705936277.251 Q7711982088.253 Q9356559659.233 Q9644583048.253 Q9967504441.254 00000100201H02?03604604a05C05e06S06k07D08108`09909:09S09l0:Z0;H0;P0;Q0;Y0;c0<Y0<^0<a0=M0=N0=O0=g0=h0>30>40>50>60>70>H0>L0??0?@0?P0?\0@40@c0@d0@e0@i0@j0@k0@l0@m0@n0@o0AQ0AR0AS0AT0AU0AX0AY0A\0B>0B?0B@0BA0BB0BC0Bl0Bm0C20C30CU0CV0CW0CX0D10E60E_0Ee0Ef0F00F?0FT0FU0FV0FW0GD0GG0GH0GK0Gg0Gj0Gk0Gl0HD0HS0IP0KP0L20L30L40L50L60L70L80L90L:0L;0L<0L=0L>0L?0L@0LA0LB0LC0LD0LE0LF0Ld0MU0MV0Nf0P>0P^0R60Rg0Sh0TF0U?0U[0V70W80W90WW0XS0Yk0ZH0Zf0[V0\F0]G0]j0^P0^b0_40_a0`N0aR0ad0b60bH0bZ0c60cH0cZ0d@0dA0dB0dT0df0e80eJ0e\0en0f@0fi0g@0gg0hN0h`0ii0ij0j<0j=0j>0j?0j@0jc0k50l00lA0lB0l[0l\0l]0m40mW0mX0mY0mk0ml0nF0o80oj0ok10=11:11;11R11i12R13913`14215615N16a17>17P17c19419K19]1:R1;=1;O1;a1<31=01=11=C1=U1>81>91>:1>;1>V1?Q1?k1@P1AO1AP1Ab1B41CJ1DI1EH1Eo1FB1FT1Ff1G81G[1H21IC1IU1Ig1JJ1J[1K@1KQ1Ki1L>1LPFFS1R3HIA1h2LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03TOP2hc2FB3sp11c3HTc3SP13dsv4CPOS3SPR4SP1R2F0S2LF2sp2PP3CUR2bs3LFB2FB3sp12Lw2p11c3dsv2HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp12Lw2p11c3dsv2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp12Lw2p11c3dsv2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp11c3dsvS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvS2LF2PP2bs3LFB2FB2Lw2p13dsv3APP2HB5Ha_st5Hl_stS2LF2PP2bs3LFB1c3dsv3CPPS2LF2bs3LFB2FB1c3dsv4CFBaS2LF2PP2bs3LFB2Lw2p11c3dsv3CPP2HB5Ha_st5Hl_stS2LF2PP3BUF2bs3LFB3DPB2Lw2p13dsv2HB5Ha_st5Hl_stS2LF2bs3LFB2FB1c3dsv4CFBaFS2LF3BUF2bs3LFB1c3dsv3CBFS2LF2bs3LFB2FB1c3dsv4CFBaS2LF2PP2bs3LFB2FB2Lw2p13dsv3APP2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2FB2Lw2p13dsv3APP2HB5Ha_st5Hl_stS2lo3sp1FS2lo3sp1S2lo1c3CLOS1R3NS13NA14STKp5STKp02sp2lo3slo4SLOL3SLO3sp13SP14NRTaS3sp1S1lS1P3END3BUF2bs2B12B33B472B52Lw2p13Hpc3HLE2LRFSS1R3HIA1h2sp3TOP3sp13SP1FS2sp2lo3sp1FFSFS3END2bs2Lw2p12KLS2PPS1R3NS13NA14STKp5STKp02sp2lo3SLO3sp11c3SP13CLO4NRTaFS2sp3SPH3sp13SP1S2sp3sp13SP1S1R3HIA1h2sp2lo3TOP4HTOPS1R3NS13NA14STKp5STKp02sp2lo3SLO3SPH1c3CLO4NRTaFFS2loSSSFFFS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvFSFSS1cFS1cS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvFFFFFS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaFS3sp1FS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvFFFS1R3BUF2lo2bs3LOS3ALO3BCES1R2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsv2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS1R3NS14STKp5STKp02sp2lo3SLO3sp13SP14NRTaS1i2HiFS1R2lo3LOSS2sp2lo3sp13SP1S3END2bs2Lw2p13HLE2KLFSFS1R3NS13NA14STKp5STKp02sp2lo3SLO3sp13SP14NRTaS1cSS1cS3sp12r04SP1M1q1r1H2H02q02H4S1cFSS1P3END2Lw2p13Hpc3HLE2LRS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR3END3BUF2lo2bs3LFB3PP02B34CUR03SLO3SPH2FB3sp12Lw2p11c3dsv4CPOS3HLE4NRTa3SPR4SP1R2F05BUFLO3P2RS2LF2sp2PP3CUR2bs3LFB2FB3sp11c3dsvFFFFFFFFFFFFFFFFFFFFS2LF2PP2lo2bs3LFB4PPLO3sp13dsvS1R2LF3CUR2bs3LFB2FB3dsv3APC2HB5Ha_st5Hl_st5SAEstFS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO2Lw2p13dsv4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12Lw2p13SP13dsv4NRTa2HB5Ha_st5Hl_stS2LF3BUF2lo2bs3LFB3sp13dsv5BUFLOS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12Lw2p13SP13dsv4NRTa2HB5Ha_st5Hl_stS1R2LF3BUF2bs3LFB2FB3dsv3APB2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp11c3SP13dsv3CLO4NRTaS2LF2lo2bs3LFB2FB3sp13dsv4FBLOS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO1c3dsv3CLO4NRTaS2LF2lo2bs3LFB3sp11c3dsv3CLOS2LF2lo2bs3LFB3sp11c3dsv3CLOS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp11c3SP13dsv3CLO4NRTaFS2LF2lo2bs3LFB2FB3sp13dsv4FBLOS1R2LF2sp3slo2bs3LFB4SLOS2FB3dsv3ALO2F12HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12Lw2p13SP13dsv4NRTa2HB5Ha_st5Hl_stS2LF2sp2lo2bs3LFB3sp13SP13dsvS2LF2lo2bs3LFB2FB3sp13dsv4FBLOS1R2LF2bs3LFB2FB1c3dsv4CFBa2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs3LFB2FB3dsv3APP2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp11c3SP13dsv3CLO4NRTaS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB3dsv2HB5Ha_st5Hl_stS2LF2PP2bs3LFB3dsvS2LF2PP2bs3LFB3dsvS1R2LF3BUF2bs3LFB2FB3dsv2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB3dsv2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo3LFB1l2B33B473B302FB3dsv5BUFLO2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FB3dsvS2LF2PP2bs3LFB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2lo2bs3LFB3LOS3dsv3ALOS2LF2bs3LFB2FB3dsvS2LF2PP2bs3LFB3dsvS1R2LF2PP2bs3LFB2FB3dsv2HB5Ha_st5Hl_stFFS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB3dsv2HBS2LF2PP2bs3LFB2Lw2p13dsv2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2Lw2p13dsv2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3dsvS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3dsv4NRTa2HB5Ha_st5Hl_stFS2LF2bs3LFB2FB3dsvFFFFS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3dsvS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp13SP13dsv4NRTaS2LF2bs3LFB1c3dsvFS2LF2PP2bs3LFB3PP03dsv2HBFFS1R2LF2bs3LFB2FB3dsv2HBS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stFFS2LF2bs3LFB2FB3dsvFS1R2LF3slo2bs3LFB4SLOS3dsvS1R2LF2PP3slo2bs3LFB4SLOS2Lw2p13dsv2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS2FB3dsv2HB5Ha_st5Hl_st5SAEstFS2LF2bs3LFB2FB3dsvS1R3HIA1h2LF2sp2bs3LFB3TOP2FB3sp13SP13dsv4HTOP2HB5Ha_st5Hl_stFS1R2LF2bs3LFB2FB3dsv2HBS1R2LF2bs3LFB2FB3dsv2HBS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_st5SAEstS2LF2PP2bs3LFB2Lw2p13dsv2HB5Ha_st5Hl_stS2LF2PP2bs3LFB2Lw2p13dsv2HB5Ha_st5Hl_stS2LF2PP2bs3LFB3dsvS1R2LF3END3BUF2lo3LFB1l2B33B473B302FB3dsv5BUFLO2HB5Ha_st5Hl_st5SAEstS2LF2lo2bs3LFB1c3dsv3CLOS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3dsv3ALO4NRTa2HB5Ha_st5Hl_st5SAEstS2LF2sp2lo2bs3LFB3sp13SP13dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB3sp13dsvS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13dsv4NRTa2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB3dsv2HBS2LF2bs3LFB2FB3dsvS1R3HIA1h2LF2sp2bs3LFB3TOP2FB3dsv4HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP13dsv4HTOPS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R3HIA1h2LF2sp2bs3LFB3TOP2FB3sp13SP13dsv4HTOP2HB5Ha_st5Hl_stFS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stFFFS2LF2PP2bs3LFB3dsv2HB5Ha_stS2LF2sp2PP3CUR2bs3LFB3ALP3PP02FB3sp11c3dsv4CPOS3SPR4SP1R2F0S2LF2PP2lo2bs3LFB4PPLO3dsvS1R2LF2bs3LFB2FB1c3dsv2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13dsv4NRTaFS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp11c3dsv4CPOS3SPR4SP1R2F02F82HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2FB3dsv4HTOP2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2PP3slo2bs3LFB3TOP2Lw2p13dsv4HTOP2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3dsv4HTOPS2LF2bs3LFB3sp13dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB3dsv2HBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13dsv4NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB2FB3dsvS2LF2bs3LFB2FB3dsvS1R2LF2bs3LFB2FB3dsv2HB5Ha_st5Hl_stS2LF2bs3LFB1c3dsvS1R2LF2bs3LFB2FB1c3dsv2HB5Ha_st5Hl_stS2LF2bs3LFB1c3dsvS2LF2bs3LFB3sp13dsv4SP1RS2LF2bs3LFB2FB3dsv2F0S2LF2bs3LFB2FB3dsv". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 AMC STKp STKp0 NRT LFB ALP PP0 CWP PPLO HBY BIN B1 B3 B47 B5 B30 DPB CUR0 CWC CURLO DCB SLOS SLOL SLO TOP SPH LOS"] Lemma seg5 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd Lw : word) (jn : list byte)
      (p1 c : Z) (ctc cpc : word) (clc cpp cnx : Z) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd Lw (Z_to_bv 64 p1) jn p1 c ctc cpc clc cpp cnx mm ->
    p1 + bv_unsigned Lw <= END ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms => exists (mm' : mem) (w0' w1' w2' tl' : word) (j64' jn' : list byte) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (pc' : Z),
         ms = MS (mkR xra' (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                      (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 c) (Z_to_bv 64 (p1 + bv_unsigned Lw)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3' t4' t5' t6')
                 F (Z_to_bv 64 pc') fc None mm' (seg_rom asegs)
         /\ ((pc' = 0xae6b0 /\ p1 + bv_unsigned Lw < END) \/ (pc' = 0xae878 /\ p1 + bv_unsigned Lw = END))
         /\ sfr hc Lh FB sp1 w0' w1' w2' tl' (Z_to_bv 8 248) k0 k8 k16 k24 k48 j64' tg pd Lw (Z_to_bv 64 p1) jn' (p1 + bv_unsigned Lw) c tg pd (bv_unsigned Lw) p1 cnx mm'
         /\ presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc c) mm mm')
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 c) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae7e8) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D HLE. sfr_open D.
    rt_facts;
    pose proof (hcs_ok asegs R HIA hc) as CSOKc;
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP; rewrite HTc, HSc in HTOP;
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia);
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia]);
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]);
    assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]);
    assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]);
    assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]);
    lazymatch type of HHc with HM _ _ _ _ ?Lh _ ?mm =>
      pose proof (fresh_apart_relist R HIA LF hc LB Lh mm FB 256 FRSH HHc) as FRSHc;
      ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
      assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN);
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh);
      assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh);
      assert (BUFLO : BUF + n <= lo) by
        (destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]; cbn [fst snd] in BCE; clear - BCE ALO LOS; lia);
      assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))) by
        (intros b' Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]);
      assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]);
      pose proof CWP1 as CWP1c; rewrite <- HTc in CWP1c;
      lazymatch type of CURc with rw_cells _ _ ?cur _ =>
        pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
                      ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRESw;
        assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia);
        assert (WCCw : wcover R Lh LF (bv_unsigned sp) (Wc cur) cur 32) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; right; left; clear; lia)
      end;
      assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)])
    end;
    pose proof (art_stk_high asegs R HIA) as STKH;
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP;
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC;
    ddestruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0);
    pose proof CWcur as CWcurc; rewrite <- HTc in CWcurc;
    assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    unfold A_x509_san_ext_A.FSHb in FSH; unfold A_x509_san_ext_A.rsl in RSL.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    assert (P2R : 0 <= p1 + bv_unsigned Lw < 2^64) by (clear - HLE LR Hpc B1 B5 B3 B47; lia).
    (* [comment removed for export] *)
    do 6 zstep.
    idtac "S5-CPY-CALL".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : rw_cells _ m2 c _ |- _ => rename H into CUR2 end.
    match goal with H : rw_cells _ m2 (sp1 + 96) _ |- _ => rename H into TSB2 end.
    match goal with H : sshad _ _ m2 slo _ |- _ => rename H into SS2 end.
    chunk_split CUR2 4%nat CURa CURn. replace (c + 24) with (c + 24) in CURn by (clear; lia).
    apply rw_cells_blob' in CURa. cbn [cells_size csize Nat.add cells_bytes cbytes app] in CURa.
    lazymatch type of CURa with rw_cells _ _ _ [CB _ ?dsq] => set (dsv := dsq) in CURa;
      assert (LDS : Z.of_nat (length dsv) = 24) by (subst dsv; rewrite !length_app, !length_le4, !length_le8; reflexivity) end.
    clearbody dsv.
    apply (u8arr_of_rw_cells asegs) in CURa.
    pose proof (proj2 (proj1 TSB2)) as BSB. cbn [cells_bytes cbytes app] in BSB.
    assert (OSRC : aobj asegs AL (hcs asegs R HIA hc) m2 (sp1 + 96) 24).
    { change 24 with (8 * Z.of_nat 3).
      eapply (aobj_of_zero_shadow asegs AL (hcs asegs R HIA hc) m2 (sp1 + 96) (zcells 3) (sp1 + 96) 0 3 CSOKc);
        [ eapply crange_sub; [exact SCSc| clear - SP1 SLO NS1 NA1 NRTa STKp0; lia| clear - SP1; lia]
        | clear - SP1M; Z.div_mod_to_equations; lia | clear; lia
        | apply (sshad_chunk asegs AL m2 slo (bv_unsigned sp) 2 (sp1 + 96) SS2); [clear - SP1 SLO SLOL NS1 NA1 NRTa STKp0; lia| clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia]
        | intros i Hi; do 3 (destruct i as [|i]; [reflexivity| try (exfalso; clear - Hi; lia)]); exfalso; clear - Hi; lia ]. }
    pose proof (artA_amemcpy asegs R HIA (arl_amemcpy R)) as SPC. specialize SPC with (h := hc).
    replace (Z_to_bv 64 425404 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_amemcpy R)) by (rewrite AMC; reflexivity).
    lazymatch type of BSB with bytes_at _ _ _ ?ssq =>
    callxA_sp sp1
      (eapply SPC with (LB := Lh) (LF := LF' FB) (DST := c) (SRC := sp1 + 96) (n := 24) (lo := lo) (ds := dsv) (ss := ssq);
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       first [ exact CURa | exact BSB | exact LOS | exact OSRC | exact LDS | eassumption | reflexivity
             | lazymatch goal with
               | |- _ = arl_amemcpy R \/ _ => left; reflexivity
               | |- Z.of_nat (length _) = 24 => rewrite !length_app, !length_le4, !length_le8; reflexivity
               | |- aobj _ _ _ _ c 24 => lazymatch goal with O : aobj _ _ _ _ c 32 |- _ => eapply aobj_sub; [exact O| clear; lia| clear; lia] end
               | |- lo <= sp1 - _ => clear - SLO SP1 NS1 NA1 NRTa STKp0; lia
               | |- crange _ lo _ => exact SCS1
               | |- c + 24 <= lo \/ _ => left; clear - CLO; lia
               | |- sp1 + 96 + 24 <= lo \/ _ => right; clear; lia
               | |- 24 = 0 \/ c + 24 + 8 <= _ => right; clear - CLO SLO SPH NS1 NA1 NRTa STKp0; lia
               | |- 24 = 0 \/ sp1 + 96 + 24 + 8 <= _ => right; clear - SP1 SPH; lia
               | |- 24 = 0 \/ _ => right; left; clear - CLO SLO SP1 NS1 NA1 NRTa STKp0; lia
               | |- 24 < _ => clear; lia
               | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_sp_mono; [exact LOS|]; eapply client_wrange_inside; [exact CWcurc| intros b' Hb; exact Hb| clear; lia| clear; lia]
               | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
               end
             | match goal with |- ?g => idtac "S5-CPY-PRE-LEFT:" g end ])
    end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "S5-CPY-LEFT:" g end.
    clear SPC OSRC.
    idtac "S5-CPY-DONE".
    match goal with H : u8arr _ _ c _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rename H into CUR3 end.
    match goal with H : ?x = Z_to_bv 64 c |- _ => subst x end.
    lazymatch type of CUR3 with rw_cells _ ?mx _ ?cs =>
      pose proof (rw_cells_reshape asegs mx c cs [C4 tg; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)] CUR3
                    ltac:(cbn; repeat split; first [apply length_le4 | apply length_le8 | reflexivity]) ltac:(cbn [cells_bytes cbytes app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity)) as CUR4 end.
    clear CUR3.
    lazymatch goal with A1 : rw_cells _ ?mx c _, A2 : rw_cells _ ?mx (c + 24) _ |- _ => chunk_join A1 A2 CUR5 end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB5 end end.
    do 13 zstep.
    clear AB5.
    (* [comment removed for export] *)
    do 10 zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    try rewrite (Z.add_comm (bv_unsigned Lw) p1) in *.
    idtac "S5-LOOPTEST".
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - idtac "S5-LOOP".
      assert (PLT : p1 + bv_unsigned Lw < END) by (clear - KL P2R Hpc B1 B5 B3 B47; kland KL; rewrite ?Z.mod_small in KL by lia; lia).
      apply evtA_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [left; split; [reflexivity| exact PLT]|].
      split; [unfold A_x509_san_ext_C.sfr; rewrite (Z_to_bv_bv_unsigned Lw); fin_sfr ltac:(clear - Hpc HLE LR; lia) | eassumption].
    - idtac "S5-EXIT".
      assert (PGE : p1 + bv_unsigned Lw = END) by (clear - KL P2R HLE Hpc B1 B5 B3 B47; kland KL; rewrite ?Z.mod_small in KL by lia; lia).
      (* [comment removed for export] *)
      zstep.
      apply evtA_done.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [right; split; [reflexivity| exact PGE]|].
      split; [unfold A_x509_san_ext_C.sfr; rewrite (Z_to_bv_bv_unsigned Lw); fin_sfr ltac:(clear - Hpc HLE LR; lia) | eassumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
