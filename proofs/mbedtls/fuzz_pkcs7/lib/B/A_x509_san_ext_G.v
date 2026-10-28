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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F.
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
Local Ltac zchk_solve :=
  rewrite ?zchk_land7;
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40997712292.3000009S1t2T02T7". (* [comment removed for export] *)
  #[using="Type"] Lemma sx32_small : forall t, 0 <= t <= 7 -> bv_unsigned (sx32 (Z_to_bv 64 t)) = t.
  Proof.
    clear. intros t [T0 T7]. assert (C : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L27111942217.1  L35177111487.1  L35653441506.13 L36099440282.227L38235734261.1  L38692635477.0  L39332637397.0  L41663468825.221L43300649301.0  L50797055232.13 L56380991837.10 L60098763854.6  L64850595401.0  L9080220944.4   L9356559676.18  Q34669538841.231Q44927690124.237Q52737562013.237Q535283720.231  00000400900Q01101501601701W01X02A02Z02d02e03404104?04M04[04iS2PPS3curS1R3HIA1h2sp2lo3TOP4HTOPS2LF2sp2PP3CUR2bs3LFB2FB3sp13curS2loSSS2LF2sp2PP3CUR2bs3LFB2FB3sp13curSS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS1R3BUF2lo2bs3LOS3ALO3BCES1R2lo3LOSSS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FB". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB CWP BIN CWC SLOS SLOL SLO TOP LOS"] Lemma seg2b : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (r t dn : Z) (rest : list cell) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl b k0 k8 k16 k24 (Z_to_bv 64 (-8320)) j64 tg pd ln pv jn p cur ctc cpc clc cpp cnx mm ->
    rw_cells asegs mm (FB + 64) (C4 (Z_to_bv 64 t) :: rest) -> 0 <= t <= 7 ->
    (t = 4 -> exists p4 j48 mg pad7 j8, rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms =>
         (t = 4 /\ exists (a1' : word),
           ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 dn) a1' a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae780) fc None mm (seg_rom asegs))
         \/ (t <> 4 /\ exists (a0' a1' : word),
           ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0' a1' a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae784) fc None mm (seg_rom asegs)))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae770) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D SANc TR T4. sfr_open D. clear TSN.
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
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases K4; zify_cond K4; rewrite (sx32_small t TR) in K4.
    { idtac "S2-APP". apply evtA_done. right. split; [exact K4| deexists 2; reflexivity]. }
    idtac "S2-T4".
    pose proof K4 as E4.
    ddestruct (T4 E4) as (p4 & j48 & mg & pad7 & j8 & ->). unfold name_blob in SANc. cbn [app] in SANc.
    (* [comment removed for export] *)
    zstep.
    apply evtA_done. left. split; [exact E4|]. eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L27111942217.1  L29010565920.223L29010565920.3  L29010566049.222L29010566049.3  L35177111487.1  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L40228640085.0  L43300649301.0  L47104866713.10 L50797055232.13 L56380991837.10 L60098763854.6  L64850595401.0  L66151410184.3  L9080220944.4   L9356559676.18  Q26483517826.232Q60713763874.23200000400500>00?00@00E00]00a00b00c00d00e01501^02702A02B02K02Z03W04>059S2PPFS1r2Hr2K2FFS3curS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSSS1r2Hr2r02K11q1HS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS1R3BUF2lo2bs3LOS3ALO3BCES1R2lo3LOSSS1r2Hr2K2S2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTa". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB CWP BIN CWC SLOS SLOL SLO TOP SPH LOS"] Lemma seg2 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (r t dn : Z) (rest : list cell) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl b k0 k8 k16 k24 (Z_to_bv 64 (-8320)) j64 tg pd ln pv jn p cur ctc cpc clc cpp cnx mm ->
    rw_cells asegs mm (FB + 64) (C4 (Z_to_bv 64 t) :: rest) -> 0 <= t <= 7 ->
    (t = 4 -> exists p4 j48 mg pad7 j8, rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
    -0x3000 < r <= 0 -> a0 = Z_to_bv 64 r ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms =>
         (r <> 0 /\ r <> -8320 /\ exists (a1' : word),
           ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae8f4) fc None mm (seg_rom asegs))
         \/ ((r = 0 \/ r = -8320) /\ ((t = 4 /\ exists (a1' : word),
           ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 dn) a1' a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae780) fc None mm (seg_rom asegs))
             \/ (t <> 4 /\ exists (a0' a1' : word),
           ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0' a1' a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae784) fc None mm (seg_rom asegs)))))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                    F (Z_to_bv 64 0xae764) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D SANc TR T4 Hr ->. pose proof D as D0. sfr_open D. clear TSN.
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
    (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1.
    { assert (RC : r = -8320).
      { clear - K1 Hr. kland K1. rewrite ?Z_to_bv_unsigned in K1. unfold bv_wrap, bv_modulus in K1. cbn [Z.pow Z.of_N Pos.pow] in K1. Z.div_mod_to_equations. lia. }
      eapply evtA_mono; [eapply seg2b with (r := r) (dn := dn); first [exact D0| exact SANc| exact TR| exact T4]|].
      intros ms' HP. right. split; [right; exact RC| exact HP]. }
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    { idtac "S2-FATAL". apply evtA_done. left.
      split; [intros ->; apply K2; vm_compute; reflexivity|].
      split; [intros ->; apply K1; vm_compute; reflexivity|].
      eexists. reflexivity. }
    assert (RC : r = 0).
    { clear - K2 Hr. kland K2. rewrite ?Z_to_bv_unsigned in K2. unfold bv_wrap, bv_modulus in K2. cbn [Z.pow Z.of_N Pos.pow] in K2. Z.div_mod_to_equations. lia. }
    eapply evtA_mono; [eapply seg2b with (r := r) (dn := dn); first [exact D0| exact SANc| exact TR| exact T4]|].
    intros ms' HP. right. split; [left; exact RC| exact HP].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L27111942217.1  L35177111487.1  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L43300649301.0  L48937103345.222L50797055232.13 L53643291478.221L56380991837.10 L60098763854.6  L64850595401.0  L9080220944.4   L9356559676.18  Q13482632424.232Q18827113617.232Q2107035961.233 Q2867079804.232 Q36138949977.232Q36140770393.233Q40386526429.233Q58194532358.233Q67028466409.23200000400900Q00U00V00W00X01801a03F03_03i03j04905605E05l05m06<06K06Z06i07g08bS2PPS3curS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSS2LF2sp2PP3CUR2bs3LFB2FB3sp13curS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR05CURLO3SLO3SPH2FB3sp13cur4CPOS4NRTa3SPR4SP1R2F0S1R3BUF2lo2bs3LOS3ALO3BCES1R2lo3LOSSS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS2LF3CUR2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPFS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS2LF2sp2PP3CUR2bs3LFB3PP03ALC4CUR02FB3sp13cur4CPOS3SPR4SP1R2F0S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTa". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP BIN ALC CUR0 CWC CURLO SLOS SLOL SLO TOP SPH LOS"] Lemma fatal1 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (r : Z) (ht hpd : word) (hl hp hnx : Z) (mm : mem)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp cnx mm ->
    rw_cells asegs mm CUR [C4 ht; C4 hpd; C8 (Z_to_bv 64 hl); C8 (Z_to_bv 64 hp); C8 (Z_to_bv 64 hnx)] ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms => exists (a1' : word),
         ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 hnx) a1' a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 r) (Z_to_bv 64 (CUR + 24)) (Z_to_bv 64 (Z.shiftr (CUR + 24) 3 + al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP)
                      (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xae928) fc None mm (seg_rom asegs))
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae8f4) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D HEADc. sfr_open D.
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
    do 13 zstep.
    apply evtA_done. eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@D48795193980.236D59892785054.236D60109196847.236K20177394750.236K20957767126.236K25746690853.236K32859452709.236K44164039966.236L15934535645.1  L1685717371.0   L20171099480.2  L20970438176.2  L24023900370.0  L25742411987.2  L27111942217.1  L27817441514.237L2824734717.2   L32855174867.2  L35653441506.13 L38235734261.1  L38692635477.0  L39332637397.0  L42411609006.0  L42506209623.2  L43300649301.0  L44168742175.3  L45354782925.2  L50797055232.13 L51578300575.1  L56380991837.10 L60098763854.6  L64009471222.1  L64850595401.0  L8171953640.237 L9080220944.4   L9356559676.18  P17794074698.246P2830239034.236 P38605639612.246P42504116273.236P45360812554.236P53346601986.246P7740881908.246 Q10592318621.242Q10651829299.237Q10821824020.246Q12658605510.246Q12658605510.248Q13002548137.240Q13193519490.232Q13482632424.232Q14986738841.240Q15010535802.240Q17425018425.240Q17703789353.237Q18089490443.240Q18099926581.240Q18850126409.240Q20459834793.240Q20851854948.240Q22444220057.240Q23869344553.240Q2388889303.240 Q26307634249.240Q26314584654.246Q26316671538.233Q2867079804.232 Q29732373684.240Q30441621867.240Q31326836009.240Q31526414380.246Q32465409102.236Q33283861378.246Q33854725207.233Q34669208220.241Q34877581972.240Q36138949977.232Q36140770393.233Q3865442997.241 Q38802716825.242Q40386526429.233Q40599399476.240Q42439443119.236Q42441548847.246Q42637512183.233Q43138029699.246Q43922358489.240Q43964130321.238Q44172294453.241Q44298944140.233Q44298944140.241Q44301027056.246Q45482765142.248Q46184984384.236Q48119910507.246Q48667226146.232Q48792950908.235Q48795193980.236Q49785721508.240Q504873378.238  Q51107054235.241Q51379872473.240Q51959565844.240Q54789931780.240Q5525646475.240 Q5532017333.240 Q55435349233.239Q5596578838.246 Q56420723160.233Q58194532358.233Q58650752521.240Q58653567769.232Q58972088531.243Q59617553652.240Q59619599050.240Q59890570654.235Q59892785054.236Q61381344394.239Q63025202418.234Q63435846322.241Q63627873392.236Q63667759319.240Q63811190484.240Q64228675114.245Q64681563910.246Q64683667846.236Q65654860420.240Q6575031993.240 Q66108231689.240Q66279660824.241Q66901779611.241Q67038986090.239Q67140649113.232Q67837027513.240Q6912043757.243 Q9967504441.240 00000[01F02:02_03I04304]05C05F05G05H05I05J05K05O06M06N06O06g06k06l06m06n06o07007107207[07`08908C08D08E08F08U09R0:J0;X0<J0=P0>^0?V0@R0A10AS0B<0Be0Ce0D30DZ0Di0E70EE0ES0F50F60F70FE0FS0Fa0Fo0G=0GK0GY0H>0HQ0H`0Hn0J30JA0JB0Je0Jf0KM0Kl0L:0LI0LX0Lk0MJ0MY0Mg0NP0O>0P90P:0PH0QA0QB0QU0Qh0RM0SM0SN0T]0UX0V60VT0Vb0Wo0XB0XP0YA0YO0Y]0Yk0Zd0Ze0[<0\10\?0\M0\l0\m0\n0]L0]j0]k0^C0^D0^g0_50_C0`N0aI0b?0bM0b[0bi0cH0c[0dh0e60eD0ec0f1S2LF2sp2PP3CUR2bs3LFB2FB3sp12HB5Ha_st5Hl_stS2LF2sp2PP3CUR2bs3LFB2FB3sp12HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS2FB3sp12HB5Ha_st5Hl_stS2LF2PP3CUR2bs3LFB3CPP2HB5Ha_st5Hl_stS2LF3CUR2bs3LFB2FB1r2Hr3APC2HB5Ha_st5Hl_stS2LF3CUR2bs3LFB2FB1r2Hr3APC2HB5Ha_st5Hl_stS2LF3CUR2bs3LFB2FB1r2Hr3APC2HB5Ha_st5Hl_stS2LF3CUR3BUF2bs3LFB3CBF2HB5Ha_st5Hl_stS1lSFFSFS2PPS1R2LF2sp2PP3CUR2bs3LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxFFS1R3HIA1h2sp2lo3TOP4HTOPS2loSSSFSFFS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS3CURS1R3BUF2lo2bs3LOS3ALO3BCES1R2lo3LOSFSFS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS1R2LF2PP3CUR2bs3LFB2D12FB3CPP4CFBa2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R2LF3BUF2bs3LFB2FB1r2Hr3APB2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3CLO4NRTa2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB3SLO3sp13SP13CLO4NRTa2HB5Ha_st5Hl_stS1R2LF2sp3slo2bs3LFB4SLOS2FB3ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF2PP3CUR2bs3LFB2D12FB1r3CPP2Hr3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2PP2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo3LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS2LF3CUR2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2PP2bs3LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB2FB2HBS2LF3CUR2bs3LFBS2LF2bs3LFB2FBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB4NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB2FBFS1R2LF3CUR2bs3LFB2FB2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp13SP14HTOPS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF3CUR2bs3LFBS2LF2bs3LFB2FBS1R2LF3CUR3slo2bs3LFB4SLOS2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaFS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP2FB3sp13SP14HTOP2HB5Ha_st5Hl_stFS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo3LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3ALO4NRTa2HB5Ha_st5Hl_st5SAEstS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14NRTaS2LF3CUR2bs3LFB2HB5Ha_st5Hl_stS2LF3CUR2bs3LFB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP14NRTa2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP2FB4HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3LFB3TOP2FB3sp13SP14HTOP2HB5Ha_st5Hl_stFS2LF3CUR2bs3LFB4CUR02HBS2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13CAL3SPR4SP1R2F0S2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stFFS2LF3CUR2bs3LFB2HB5Ha_st5Hl_stS2LF3CUR2bs3LFB2HB5Ha_st5Hl_stFS2LF3CUR2bs3LFB2HB5Ha_stFS1R2LF3CUR2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2sp2PP3CUR2bs3LFB3PP04CUR02FB3sp13SPR4SP1R2F02F82HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2FB4HTOP2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3CUR3slo2bs3LFB3TOP4HTOP2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs3LFB2FB2HBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP14NRTa2HB5Ha_st5Hl_stS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R2LF2bs3LFB2FB2HB5Ha_st5Hl_stS2LF2bs3LFB2FB". (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB PP0 CWP PPLO HBY BIN B3 B47 B30 DPB CUR0 CWC DCB D1 SLOS SLOL SLO TOP SPH LOS"] Lemma fatal2 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k8 k16 k24 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p : Z) (ht hpd : word) (hl hp hnx : Z) (r : Z) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5v s6v s7v s8v s9v s10v t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd ln pv jn p CUR ht hpd hl hp hnx mm ->
    -0x3000 < r <= 0 -> (r = 0 -> p = END) ->
    evtA asegs AL (hcs asegs R HIA hc) (EXITP hc Lh FB sp1 k0 k8 k16 k24 k48 CUR ht hpd hl hp 0 mm)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 r) (Z_to_bv 64 (CUR + 24)) (Z_to_bv 64 (Z.shiftr (CUR + 24) 3 + al_sb AL)) s5v s6v s7v
               s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae92c) fc None mm (seg_rom asegs)).
  Proof.
    intros until t6. intros D Hr HENDx. sfr_open D.
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
    do 5 zstep.
    clear AB0.
    (* [comment removed for export] *)
    do 11 zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    apply evtA_done. unfold A_x509_san_ext_E.EXITP.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    exists r. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact Hr|].
    split; [fin_sfr ltac:(idtac) | split; [eassumption| exact HENDx]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
