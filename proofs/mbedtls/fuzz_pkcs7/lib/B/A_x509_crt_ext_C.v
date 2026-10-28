(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse P_x509_crt_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_get_san_A A_x509_crt_ext_stmt A_x509_crt_ext_A A_asn1_get_bool A_oid_x509_ext A_x509_get_ext_A A_x509_basic_A A_x509_key_usage_A A_x509_skid_A A_x509_ns_cert_type_A A_x509_crt_ext_area A_x509_crt_ext_B.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L48438527537.172L48440628059.171L48440637961.173L51279041139.17400000`01P02@04\S2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx2bp3bp'2HbS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx2bp3bp'2HbS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx2bp3bp'2HbS1R3HIA4PHIx4FFRx4CNTx1h2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT01d2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R2hc2Lx2bp3bp'3B1'3B2'3B3'1H2H02H1". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 STKc1 PHIx_mono FFRx_mono CNTx_mono LB LF sp PP CRT END BUF lo slo bs LFB3 LFB PP0 BIN B1 B2 B3 DPB CRT0 DXB D1 SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APP APC SPR ALO ACV F0 APB D1u DXBu SP1R"] Lemma BUD_mono : forall hc Lx bp bp', BUD hc Lx bp -> P <= bp <= bp' -> BUD hc Lx bp'.
  Proof.
    (intros hc Lx bp bp' dd_H; ddestruct dd_H as (B1' & B2' & B3'); intros Hb). unfold BUD.
    pose proof (PHIx_mono (bp - P) (bp' - P) ltac:(lia)). pose proof (FFRx_mono (bp - P) (bp' - P) d ltac:(lia)). pose proof (CNTx_mono (bp - P) (bp' - P) ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L13527335811.4  L24882004373.71 L27111942217.1  L29680655011.1  L35655538583.72 L38235734261.1  L64850595401.0  L9090702513.71  Q53792970682.275Q63205301786.27500000>00\00`00e02W02[02\03803h04cS1P3END2bp3HBPS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loSS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12Lx5HTOPcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2Lx". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB PP0 CWP PPLO BIN B1 B2 B3 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC SPR ALO ACV F0 APB SLOu D1u DXBu SP1R"] Lemma exit_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (floc : list cell) (w0 w1 w2 k16 : word) (ja jb : list byte) (r p' bp : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X floc FSHX w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> -2^31 < r <= 0 ->
    BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v (Z_to_bv 64 r) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaad14) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP Hp' RR HBUD HBP.
    destruct (BUD_mono _ _ _ END HBUD ltac:(clear - HBP; lia)) as (BV & BF & BC).
    dpose INV as (_ & _ & _ & _ & _ & XO0 & _ & XC0 & _).
    pose proof (xfold asegs CRT _ _ XC0) as XF. pose proof (xown_ok asegs _ _ _ XO0) as XOK.
    open_xinv INV hc.
    (* [comment removed for export] *)
    zstep.
    eapply A_x509_crt_ext_B.x_fin with (hq := hc) (Lx := Lx) (p' := p') (eo := eo_of X) (ej := ej_of X) (STKc := STKc);
      first [ exact HHc | exact HCSc | exact HTc | exact HSc | exact HFc | exact BV | exact BF | exact BC | exact PRES | exact HPP | exact Hp' | exact RR | exact CFB | exact FRSH
            | exact PERM | eassumption | reflexivity
            | match goal with |- ?g => idtac "EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02>0@L15934535645.1  L1685717371.0   L24023900370.0  L24882004373.71 L27111942217.1  L27817441514.295L27817441514.296L29680655011.1  L35655538583.72 L38235734261.1  L42411609006.0  L64009471222.1  L64850595401.0  L8171953640.295 L8171953640.296 L9090702513.71  P324046647.302  P324046647.303  P38605639612.302P38605639612.303P49211061452.302P49211061452.303P7740881908.302 P7740881908.303 P7903954312.302 P7903954312.303 Q10195749203.297Q10592318618.289Q10639171022.286Q10821824020.302Q10821824020.303Q11796756721.297Q11988014288.296Q12658605510.302Q12658605510.303Q12658605510.304Q12658605510.305Q13241170297.299Q14705649756.292Q14751535315.297Q15944836594.296Q16355141072.296Q16909570643.297Q17420902403.297Q17558758360.298Q17716263636.286Q20517146075.299Q22374337363.297Q22516600531.297Q23232684382.294Q2363337691.299 Q24257074651.299Q25166423590.302Q25166423590.303Q26314584654.302Q26314584654.303Q26316671538.283Q26729481055.293Q26892573131.287Q2863532638.294 Q29745040014.297Q30441621865.288Q31326836009.297Q32959886801.295Q3339752862.289 Q34268448600.298Q3444200401.295 Q34877581972.297Q34952600272.296Q35895740379.299Q36759522011.299Q37065061723.299Q38555981400.298Q39328755025.295Q39408379774.292Q40332524508.292Q40599399476.297Q40974010456.298Q41635797459.297Q4174339024.296 Q42295909976.298Q42441548847.302Q42441548847.303Q44298944140.283Q44298944140.298Q44301027056.302Q44301027056.303Q4473570896.296 Q45445507793.295Q45482765142.304Q45482765142.305Q45742062764.282Q46591526104.298Q48119910507.302Q48119910507.303Q4845047677.293 Q49748522582.302Q49748522582.303Q51379872473.297Q51959565846.288Q52387815135.293Q52690940469.298Q53328907473.295Q53774309119.291Q54196455217.297Q54200699147.297Q54789931780.297Q5596578838.302 Q5596578838.303 Q56186208347.299Q56900949851.299Q58972088534.290Q59391892184.298Q59617553652.297Q59621696206.297Q59991740767.293Q61500136060.294Q6191098356.302 Q6191098356.303 Q62603800435.295Q62635101267.297Q63435846322.298Q63488537438.294Q64228675114.301Q64228675114.302Q64411644381.291Q65430079568.296Q6575031993.297 Q66901779611.298Q66922076282.298Q66995821912.298Q67028497104.287Q67041068973.302Q67041068973.303Q67126152652.282Q68011063237.302Q68011063237.303Q6912043752.290 Q705497310.294  Q7830203611.299 Q8701202793.302 Q8701202793.303 00000300400500S00W01Z02]02b04T04X04Y04Z04[04\04]05906707507g08Y09K0:=0:n0;_0=00>A0>B0>f0?M0@;0@i0AQ0AR0B@0Bn0D30E80E`0Ea0FI0G10G20G30GF0GG0Gn0Go0H00H10H20H30H40H50H60H`0IJ0Ib0Ic0Jb0Jc0K60L80LK0LL0M00M10M20ME0MF0MG0MH0MI0MJ0N20NZ0OB0OU0OV0OW0OX0OY0PL0Q?0QW0Qo0RY0SC0SD0SE0TJ0UO0Ub0Uc0Vo0X;0Xc0Yd0Ze0[80[o0\W0\o0]00]X0]k0^>0^Q0^R0^S0^T0_<0_`0`H0`I0`J0`K0a30aa0bO0c70c80c90c:0dJ0eZ0fB0fj0g=0gU0h=0h>0iH0jX0kh0l;0m20mi0nM0o50o610?11HS1lSSS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loSFSFFS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FBFS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFFFFFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB4SLOu2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FBFFFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFFFFS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstFFS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HBFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEst". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB PP0 CWP PPLO BIN B1 B2 B3 B47 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma errj_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 : list byte) (ja jb : list byte) (r p' bp : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> -2^31 < r <= 0 ->
    BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v (Z_to_bv 64 r) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaacfc) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP Hp' RR HBUD HBP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 6 zstep.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb.
    eapply exit_walk with (p' := p') (bp := bp); first [ exact INV2 | eassumption | match goal with |- ?g => idtac "ERRJ-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L11238556328.0  L14992968852.207L2397676628.0   L26467768376.4  L30285960423.76 L39018493418.76 L42604909192.207L52071635888.20700000101j01k02<03J04Z06M06NSS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX13EX2SS4ENDX2p'3LX03NE0S2sp2PP3CRT1P3BUF2bs3PP02B12B54CRT02D12FB3sp13APP3APC3SPR2F03D1u4SP1R4ENDX3EX1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B54CRT02D12FB3sp13APP3APC3SPR2F03D1u4SP1R2p'3Hp'S1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R2p'3Hp'F". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB PP0 CWP PPLO BIN B1 B2 B3 B5 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 APB SLOu D1u DXBu SP1R EX1 EX2"] Lemma fin_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 : list byte)
      (ja jb : list byte) (p' bp : Z)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s5v s6v s7v s8v s9v s10v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 p') x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v (Z_to_bv 64 ENDX) s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xaaca8) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP Hp' HBUD HBP.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    (* [comment removed for export] *)
    do 7 zstep.
    rewrite ?(unsigned_lit p') by (xl Hp'). rewrite ?(unsigned_lit ENDX) by (xl EX1 EX2).
    destruct (Z.eq_dec p' ENDX) as [EQ|NE].
    - subst p'. rewrite Z.lxor_nilpotent.
      match goal with |- context [Z_to_bv 64 (Z.land ?e ?c)] => let EE := fresh in assert (EE : Z.land e c = 0) by (vm_compute; reflexivity); rewrite EE; clear EE end.
      eapply exit_walk with (p' := ENDX) (bp := bp); first [ exact INV | eassumption | clear; lia | match goal with |- ?g => idtac "FIN-LEFT:" g end ].
    - replace (Z.lxor p' ENDX <? 1) with false.
      2:{ symmetry. apply Z.ltb_ge.
          assert (LX0 : 0 <= Z.lxor p' ENDX) by (apply Z.lxor_nonneg; split; intros _; xl Hp' EX1 EX2).
          destruct (Z.eq_dec (Z.lxor p' ENDX) 0) as [E0|NE0]; [| clear - LX0 NE0; lia]. exfalso. apply NE. apply Z.lxor_eq. exact E0. }
      match goal with |- context [Z_to_bv 64 (Z.land ?e ?c)] => let EE := fresh in assert (EE : Z.land e c = 18446744073709542042) by (vm_compute; reflexivity); rewrite EE; clear EE end.
      rewrite (zbv_wrap 18446744073709542042).
      eapply exit_walk with (p' := p') (bp := bp); first [ exact INV | eassumption | clear; lia | match goal with |- ?g => idtac "FIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02N0@L13527335811.81 L14988778990.289L15934535645.1  L1685717371.0   L24023900370.0  L24882004373.71 L27111942217.1  L27817441514.293L27817441514.294L29680655011.1  L35655538583.72 L38235734261.1  L39762146710.4  L41202929119.287L42411609006.0  L45931800355.17 L49334198535.81 L56775171906.289L64009471222.1  L64850595401.0  L8171953640.293 L8171953640.294 L9090702513.71  P324046647.300  P324046647.301  P38605639612.300P38605639612.301P49211061452.300P49211061452.301P7740881908.300 P7740881908.301 P7903954312.300 P7903954312.301 Q10195749203.295Q10592318618.287Q10639171022.284Q10649498890.296Q10651912114.295Q10821824020.300Q10821824020.301Q11796756721.295Q11988014288.294Q12658605510.300Q12658605510.301Q12658605510.302Q12658605510.303Q13241170297.297Q13733010575.295Q14705649756.290Q14751535315.295Q15944836594.294Q16355141072.294Q16909570643.295Q17420902403.295Q17558758360.296Q17701933584.296Q17716263636.284Q20517146075.297Q22374337363.295Q22516600531.295Q23232684382.292Q2363337691.297 Q24257074651.297Q25166423590.300Q25166423590.301Q25274940938.295Q26314584654.300Q26314584654.301Q26316671538.281Q26729481055.291Q26892573131.285Q2863532638.292 Q29745040014.295Q30441621865.286Q31326836009.295Q32959886801.293Q3339752862.287 Q34268448600.296Q3444200401.293 Q34877581972.295Q34952600272.294Q35895740379.297Q36759522011.297Q37065061723.297Q38555981400.296Q39328755025.293Q39408379774.290Q39600066516.296Q40332524508.290Q40599399476.295Q40916972731.296Q40974010456.296Q41524360563.295Q41635797459.295Q4174339024.294 Q42295909976.296Q42441548847.300Q42441548847.301Q44298944140.281Q44298944140.296Q44301027056.300Q44301027056.301Q4473570896.294 Q45445507793.293Q45482765142.302Q45482765142.303Q45742062764.280Q46591526104.296Q48119910507.300Q48119910507.301Q4845047677.291 Q49748522582.300Q49748522582.301Q51379872473.295Q51959565846.286Q52387815135.291Q52690940469.296Q53328907473.293Q53774309119.289Q54196455217.295Q54200699147.295Q54789931780.295Q5596578838.300 Q5596578838.301 Q56186208347.297Q56900949851.297Q58972088534.288Q59391892184.296Q59617553652.295Q59621696206.295Q59991740767.291Q61500136060.292Q61847600945.296Q6191098356.300 Q6191098356.301 Q62603800435.293Q62635101267.295Q63435846322.296Q63488537438.292Q64228675114.299Q64228675114.300Q64411644381.289Q65430079568.294Q6575031993.295 Q66901779611.296Q66922076282.296Q66995821912.296Q67028497104.285Q67041068973.300Q67041068973.301Q67126152652.280Q68011063237.300Q68011063237.301Q6912043752.288 Q705497310.292  Q7830203611.297 Q8701202793.300 Q8701202793.301 00001n04804;04<04=04[04_05b06e06j08\08`08l09M09N09\0;Z0=`0=a0=b0=c0=d0>@0?>0@<0@n0A`0BR0CD0D50Df0F70GH0GI0Gm0HT0Hg0I:0Ih0JV0K>0K?0Km0L[0M`0Ne0OM0O`0Oa0PI0Q10Q20Q30QF0QG0QZ0RA0RB0RC0RD0RE0RF0RG0RH0RI0R]0SG0T10TI0TJ0UI0UJ0U]0V_0W20W30WW0WX0WY0Wl0Wm0Wn0Wo0X00X10XY0YA0YB0Yj0Z=0Z>0Z?0ZS0ZT0ZU0ZV0[I0\<0\T0\l0]V0^@0^A0^B0_G0`L0`_0``0al0c80c`0da0eb0f50fl0gT0gl0gm0hU0hh0i;0iN0iO0iP0iQ0j90j]0kE0kF0kG0kH0l00lj0mX0nF0nn0no0o00o110A11Q12912a13413L14414515?16O17_18218i19`1:D1:l1:m1<61=?S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp3HP03HQ03HQE3HBPS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p03HP03HQ03HQE3EX1S1lSSS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loS1P1q2bp3HBPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2bs4ENDX1q2KlS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp3HP03HQ03HQE3HBPS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p03HP03HQ03HQEFSFFS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FBFS2LF2PP2bs4LFB33LFBS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFFFFFFS2LF2bs4LFB33LFB3sp1S1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB4SLOu2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FBFFFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFFS2LF2bs4LFB33LFB3sp1FFFS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstFFS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HBFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEst". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma tail_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HBUD HBP KLOOP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 11 zstep.
    fold_xinv INV2 hc Lx X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    zstep. if_cases Kl; zify_cond Kl.
    { idtac "TAIL-LOOP".
      assert (QL : q < ENDX) by (clear - Kl HP0 HQ0 HQE B1 B3 B5 B47 EX1 EX2; try kland Kl; rewrite ?Z.mod_small in Kl by lia; lia).
      eapply (KLOOP q HQ0 QL); first [ exact INV2 | eassumption | eapply BUD_mono; [exact HBUD| clear - HBP; lia] | match goal with |- ?g => idtac "TAIL-LOOP-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep.
    idtac "TAIL-FIN".
    eapply fin_walk with (p' := q) (bp := bp); first [ exact INV2 | eassumption | xl HP0 HQ0 HQE EX1 EX2 HBP | match goal with |- ?g => idtac "TAIL-FIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac xown_pres HP hc XOn :=
    lazymatch type of HP with presA _ _ _ _ _ _ _ _ ?mA ?mB =>
    lazymatch goal with XOx : xown _ mA (?Lxx ++ LB) ?Xx, PMx : Permutation ?Lxx _, HHx : HM _ _ _ hc _ _ mA, HCz : (forall x, CS x -> hcs asegs R HIA hc x) |- _ =>
      assert (XOn : xown asegs mB (Lxx ++ LB) Xx)
        by (eapply xown_tr; [exact XOx| intros b Hb; exact Hb|];
            let x := fresh "x" in let cs := fresh "cs" in let Hx := fresh "Hx" in let HR := fresh "HR" in let Hsz := fresh "Hsz" in
            intros x cs Hx HR Hsz;
            let XL := fresh "XL" in let APX := fresh "APX" in
            assert (XL : In (x, SEQ_SIZE) Lxx) by (eapply Permutation_in; [apply Permutation_sym; exact PMx| exact Hx]);
            pose proof (lx_apart hc Lxx mA x SEQ_SIZE HHx HCz XL ltac:(unfold SEQ_SIZE; lia)) as APX;
            eapply (presA_rw_cells asegs R); [exact HP| exact HR| rewrite Hsz; eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; left; exact XL| clear; lia| clear; lia]|];
            rewrite Hsz; cbn [disjoint_from]; unfold SEQ_SIZE in *; clear - APX; lia)
    end end.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@D10651567415.278D10833959634.307D12654479616.307D17704051245.278D24125724923.307D32452447318.307D3269699907.307 D35884995692.307D3886322623.307 D390737735.278  D39258386159.307D52045774220.307D54248487652.307D59473897855.309D6203530546.307 D68409308397.307D6897247976.307 D8984215077.278 D904953340.307  L1041497707.81  L10837002389.2  L1103920410.2   L12654381620.1  L12729978778.2  L12986590262.81 L13527341729.87 L14096410875.83 L1487348749.1   L1530387784.71  L15844907397.81 L15910629773.1  L16482024986.2  L17698511112.81 L18144980569.81 L19273442573.1  L19979573058.81 L20038394650.2  L20100555981.1  L20977711877.2  L21230010724.3  L23615739305.3  L24334533294.1  L24882004373.71 L26375085850.2  L27111942217.1  L2826782963.81  L29680655011.1  L29944679437.1  L30507144274.2  L3075075738.83  L30997223346.3  L31862681339.81 L33685467802.2  L3482445079.81  L34837878146.83 L35655538583.72 L35916062925.81 L36035727278.2  L37208353821.2  L38235734261.1  L390915313.81   L39360202971.81 L39568824258.2  L40988234253.1  L41114250165.81 L41755152410.2  L44015431570.319L44994508990.81 L45311526170.2  L46887489953.87 L48581558115.81 L48932718241.0  L49037321277.81 L52222525021.3  L52674297804.1  L55217942029.1  L57628700040.4  L58774595815.7  L58972694979.81 L61453499215.3  L62240161195.2  L62513011098.2  L62719656717.1  L63199674356.298L64584198451.87 L64850595401.0  L64980445247.2  L65862516566.2  L66082616973.1  L67070089790.2  L7541372002.81  L8984655251.81  L9090702513.71  L921615245.1    L9976516746.1   P1041757538.307 P1103805628.307 P12729896508.307P16481615804.307P18389176255.307P19976377707.307P20038771388.307P20979511989.307P23097620927.307P26375167676.307P26654780607.307P30999741941.307P32812358207.307P33685091132.307P37210678701.307P39566696050.307P3982783807.307 P41755070908.307P43679441343.307P45311182012.307P48368720831.307P51925880511.307P52220849178.307P62513354812.307P65860122342.307P8674438975.307 Q1103805628.307 Q12729896508.307Q15985628819.309Q16481615804.307Q19561186129.307Q20038771388.307Q20979511989.307Q21229638117.307Q26375167676.307Q30509110512.307Q30999741941.307Q33685091132.307Q33854460858.276Q37210678701.307Q39566696050.307Q41755070908.307Q42637247002.276Q45311182012.307Q52220849178.307Q59578101107.309Q61453052878.307Q6203530546.307 Q62239780138.307Q62513354812.307Q64980527513.307Q65860122342.307Q67070757567.307Q68266871398.307Q8931203145.307 Q9634228910.307 00000Q01601[02<02]03>03?03@03A03b03c04H04i05O06006106R07307407Q07Y07Z07_07`0:70<<0=l0>10>J0>l0?10?20A00AH0AM0C[0C\0Ca0Cb0Cc0Cm0D20DP0DQ0DU0FW0F\0Fa0Fb0HR0HS0JT0JU0LX0NJ0P<0PY0Pb0Pc0Pg0Q<0Ra0Rb0Rg0SD0SE0Si0VD0VE0XM0Zc0Zd0]E0]F0]J0]O0]\0^30^P0^Q0^R0^S0^X0^Y0_<0_=0_>0_?0_D0_E0_c0`80`T0`Y0`]0a<0aW0b20bM0cL0cn0dI0dc0eb0f=0g<0gW0hV0i10iL0ig0jf0kA0l@0l[0mZ0nY0o60oQ0ok10j10k10l10m10n11Y11Z11[12W12X13L13M13N14;14<14=14>15615715815P16O16c17b17c18Z18[19W1:C1:W1:mS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsFS3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HBP2p23Hp2S3CRTS2sp2PP3CRT2bs2FB3sp13SP1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOS3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2bs2D12FB3sp1S3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS3CRTFFS1R3HIA2hcS3CRTS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2PPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ02p23Hp2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX1q2e93HE92p23Hp2S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3FS2loS2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9FS3CRTS2sp2PP3CRT3BUF2bs3DPB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12csS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HE93HBP2p23Hp2S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9SS1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE93NS15STKc2FS2x0S3CRTS2PP3CRT1x2HxS1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT3BUF2bs3B472FB3sp1FFFS3CRTFS2sp2PP3CRT2bs2D12FB3sp13D1u2rk3HrkSFFS3CRTFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT2lo2bs2FB3sp13SP1S3CRTS2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3BUF2bs4LFB33LFB3DPBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT3BUF2bs4LFB33LFB4DXBuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS2LF2bs4LFB33LFB2FB1c2HcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2bs4LFB33LFB3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPcS2LF2bs4LFB33LFB3sp1S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG KUSE STKc1 STKc2 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_ku : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv INV hc.
    (* [comment removed for export] *)
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    chunk_split XE 3%nat XE0 XKU.
    replace (CRT + 640 + 12) with (CRT + 652) in XKU by (clear; lia).
    pose proof KUSE as SPK. unfold x509_ku_stmtA, A_X509_KEY_USAGE in SPK.
    idtac "KU-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPK with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (KU := CRT + 652) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_KU_STACK_A;
        first [ exact HHc | exact XKU | exact HPP | eassumption | reflexivity | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "KU-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_ku_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & rk & p2 & kv
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & XKU2 & Hp2).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaabf0)) with (Z_to_bv 64 0xaabf0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "KU-BACK".
    xown_pres HP2 hc XO2.
    pres_call HP2.
    clear XO HHc HPP XKU STlo SS1 MI.
    presA_transport HP2.
    clear HP2 SPK.
    switch_h hc h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (HBUD2 : BUD h2 Lx bp) by (unfold BUD in *; rewrite Evol2, Efr2; exact HBUD).
    idtac "KU-SWITCHED".
    assert (XE2 : rw_cells asegs m2 (CRT + 640) [C4 (x_et X); C4 (x_ca X); C4 (x_mp X); C4 kv]).
    { apply (proj2 (rw_cells_app asegs m2 (CRT + 640) [C4 (x_et X); C4 (x_ca X); C4 (x_mp X)] [C4 kv])). split; [exact XE0|].
      cbn [cells_size csize Nat.add]. replace (CRT + 640 + Z.of_nat 12) with (CRT + 652) by (clear; lia). exact XKU2. }
    clear XE0 XKU2.
    fold_xinv_at INV2 m2 h2 Lx (setku X kv) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "KU-OK".
      eapply tail_walk with (q := p2) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP | match goal with |- ?g => idtac "KU-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "KU-ERR".
    eapply errj_walk with (p' := p2) (bp := bp); first [ exact INV2 | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP EX1 EX2 Hrk | match goal with |- ?g => idtac "KU-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@D10651567415.282D10833959634.311D12654479616.311D17704051245.282D24125724923.311D32452447318.311D3269699907.311 D35884995692.311D3886322623.311 D39258386159.311D52045774220.311D54248487652.311D57208429143.282D59473897855.313D6203530546.311 D64422395237.282D68409308397.311D6897247976.311 D904953340.311  L1041497707.81  L10837002389.2  L1103920410.2   L11767186173.1  L12654381620.1  L12729978778.2  L12986590262.81 L13527341729.87 L13769393830.278L14096410875.83 L1530387784.71  L15844907397.81 L17698511112.81 L19060926077.1  L19979573058.81 L20038394650.2  L20977711877.2  L21230010724.3  L2181270497.1   L23615739305.3  L24882004373.71 L26375085850.2  L27111942217.1  L29680655011.1  L29740695027.81 L30507144274.2  L3075075738.83  L30997223346.3  L31862681339.81 L31902079384.2  L33685467802.2  L3482445079.81  L34837878146.83 L35655538583.72 L35916062925.81 L36035727278.2  L37088764141.3  L38235734261.1  L39360202971.81 L40985924861.1  L41114250165.81 L41755152410.2  L44015431570.323L44994508990.81 L45311526170.2  L4654558461.1   L46887489953.87 L48279521405.1  L49037321277.81 L50824534578.81 L51983188781.310L52674297804.1  L54851931528.280L54923363759.2  L55695560127.3  L57208574433.81 L57628700040.4  L58219377819.2  L58755241469.1  L58774595815.7  L58972694979.81 L62513011098.2  L63199674356.302L64421983955.81 L64474356429.2  L64584198451.87 L64850595401.0  L65414423329.0  L65834177225.81 L65862516566.2  L66259187453.1  L67070089790.2  L8404377469.1   L9090702513.71  L9538550066.2   L9976516746.1   P1041757538.311 P1103805628.311 P12729896508.311P18389176255.311P19976377707.311P20038771388.311P20979511989.311P21110254667.311P23097620927.311P26375167676.311P26654780607.311P30999741941.311P31902259262.311P32812358207.311P33685091132.311P37086507690.311P3982783807.311 P41755070908.311P43679441343.311P45311182012.311P48368720831.311P62513354812.311P64472683389.311P65860122342.311P8674438975.311 P9540808834.311 Q1103805628.311 Q12729896508.311Q13195388474.276Q15985628819.313Q19561186129.311Q20038771388.311Q20979511989.311Q21229638117.311Q26375167676.311Q30509110512.311Q30999741941.311Q31902259262.311Q33685091132.311Q37086507690.311Q41755070908.311Q45311182012.311Q48656971674.276Q54923805705.311Q55695908158.311Q58220078106.311Q59578101107.313Q6203530546.311 Q62513354812.311Q64472683389.311Q65860122342.311Q67070757567.311Q68266871398.311Q8931203145.311 Q9540808834.311 Q9634228910.311 00000[01J02902d03O04:04;04<04=04>04m05X06C07307^08I08J09509609S09[09\09a09f09g0<>0>C0AE0C50CN0D00En0F30HA0HB0HC0HD0HI0HS0I10I20I60I;0KQ0KR0MB0MC0OD0OE0OF0QI0S;0Tm0UJ0US0UT0UX0W=0WB0W_0W`0XN0Zi0Zj0Zo0]70]<0_]0`;0ag0ak0cW0cX0cY0cn0d;0d<0dA0dX0e50e60e70eL0eM0f00f10f20fJ0fK0fP0fQ0fV0g20g30g70g`0hE0hj0j30j_0kD0kh0m10n:0n_0oh10M11212;12`13G14P15516>16c17l18Q19619Z1:c1;H1;I1;J1<71<81<m1<n1<o1>51>61?41?51?61?71?81?91?:1@21A31B<1CE1Cg1DE1DF1DG1DH1EN1FD1Fb1Fc1GCS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNS1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNSFS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsFS3CRTS3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS1R3HIA4PHIx4FFRx4CNTx1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2PP3CRT1P3END2lo3slo2bs4LFB33LFB3mo01d2FB3sp12hc2mg2e92x52x62x73x133x143x153x163x173s5v3x283x293x303x313LNSS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HBP2p23Hp2S2sp2PP3CRT2bs2FB3sp13SP1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFFS3CRTS1R3HIA2hcS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2PPS3CRTS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ02p23Hp2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX1q2e93HE92p23Hp2S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3FS2loS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9S3CRTS2sp2PP3CRT3BUF2bs3DPB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nrest3LNS2csS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HE93HBP2p23Hp2S3CRTS1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE93NS15STKc2S2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5nrest3LNSS2x0S2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5nrest3LNSFFS2sp2PP3CRT2bs2FB3sp1S2PP3CRT1x2HxFS3CRTS1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT3BUF2bs3B472FB3sp1FFS2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT2bs2D12FB3sp13D1u2rk3HrkSSS2sp2PP3CRT2bs2D12FB3sp1FS3CRTFS3CRTS2sp2PP3CRT2lo2bs2FB3sp13SP1FS2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp15nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS2LF2PP2bs4LFB33LFB2FB3APP5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3BUF2bs4LFB33LFB3DPB5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS2LF3CRT3BUF2bs4LFB33LFB4DXBu5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2PP3CRT2bs4LFB33LFB3D1u5nrest3LNSS2LF3CRT2bs4LFB33LFB2FB3APC5nrest3LNSS2LF2PP2bs4LFB33LFB2FB3APP5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF3CRT2bs4LFB33LFB2FB3APC5nrest3LNSFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F85nrest3LNSFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nrest3LNSFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu5nrest3LNSFFFFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nrest3LNSS2LF2bs4LFB33LFB2FB5nrest3LNS1c2HcS2LF2bs4LFB33LFB3sp15nrest3LNSFFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nrest3LNSS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5nrest5HTOPc3LNSS2LF2bs4LFB33LFB3sp15nrest3LNSFS2LF2bs4LFB33LFB2FB2F05nrest3LNS". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG NSCT STKc1 STKc2 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_ns : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv INV hc.
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof XN as [[WF8 _] _]. cbn in WF8. destruct WF8 as [LNS _].
    destruct (x_ns X) as [|nb nrest] eqn:ENS; [cbn in LNS; lia|]. cbn in LNS.
    apply (rw_cells_reshape asegs mg (CRT + 688) _ [C1 nb; CB 7 nrest]) in XN; [| cbn; lia| reflexivity].
    chunk_split XN 1%nat XN0 XNR.
    pose proof NSCT as SPK. unfold x509_ns_stmtA, A_X509_NS_CERT_TYPE in SPK.
    idtac "ARM_NS-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPK with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (NS := CRT + 688) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_KU_STACK_A, X509_NS_STACK_A, X509_BASIC_STACK_A, X509_SKID_STACK_A;
        first [ exact HHc | exact XN0 | exact HPP | eassumption | reflexivity | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "ARM_NS-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_ku_postA, x509_ns_postA, x509_basic_postA, x509_skid_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & rk & p2 & nv
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & XN2 & Hp2).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaac44)) with (Z_to_bv 64 0xaac44 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "ARM_NS-BACK".
    xown_pres HP2 hc XO2.
    pres_call HP2.
    clear XO HHc HPP XN0 STlo SS1 MI.
    presA_transport HP2.
    clear HP2 SPK.
    switch_h hc h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (HBUD2 : BUD h2 Lx bp) by (unfold BUD in *; rewrite Evol2, Efr2; exact HBUD).
    idtac "ARM_NS-SWITCHED".
    assert (XNj : rw_cells asegs m2 (CRT + 688) [CB 8 (nv :: nrest)]).
    { eapply (rw_cells_reshape asegs m2 (CRT + 688) [C1 nv; CB 7 nrest]); [| cbn; lia| reflexivity].
      apply (proj2 (rw_cells_app asegs m2 (CRT + 688) [C1 nv] [CB 7 nrest])). split; [exact XN2| exact XNR]. }
    clear XN2 XNR.
    fold_xinv_at INV2 m2 h2 Lx (setns X (nv :: nrest)) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "ARM_NS-OK".
      eapply tail_walk with (q := p2) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP | match goal with |- ?g => idtac "ARM_NS-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "ARM_NS-ERR".
    eapply errj_walk with (p' := p2) (bp := bp); first [ exact INV2 | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP EX1 EX2 Hrk | match goal with |- ?g => idtac "ARM_NS-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0340@D10651567415.280D10833959634.310D12654479616.310D15012441253.280D17313850567.280D17704051245.280D24125724923.310D31594273287.280D32452447318.310D3269699907.310 D35884995692.310D3886322623.310 D39258386159.310D46358390245.280D52045774220.310D54248487652.310D59473897855.312D6203530546.310 D68409308397.310D6897247976.310 D904953340.310  L1041497707.81  L10837002389.2  L1103920410.2   L11825866275.81 L12654381620.1  L12729978778.2  L12986590262.81 L13527341729.87 L14096410875.83 L14648354365.81 L15012030227.81 L1530387784.71  L15844907397.81 L16482024986.2  L17313738609.81 L17698511112.81 L19501003775.2  L19979573058.81 L20038394650.2  L20079065293.1  L20977711877.2  L21109205227.2  L21230010724.3  L21947771341.1  L23615739305.3  L23635439053.1  L24882004373.71 L26375085850.2  L27111942217.1  L27387485261.1  L27792019661.1  L28573892092.4  L29541092109.1  L2961743075.81  L29680655011.1  L30507144274.2  L3075075738.83  L30997223346.3  L31122607821.1  L31594418609.81 L31859350018.2  L31862681339.81 L32024703019.2  L3206560911.3   L32708391181.1  L33428533528.7  L33685467802.2  L3482445079.81  L34837878146.83 L35655538583.72 L35916062925.81 L36035727278.2  L36460422029.1  L36477126818.81 L36651900019.81 L36849512077.1  L38148089741.1  L38235734261.1  L38431023693.1  L39360202971.81 L40018777229.1  L41114250165.81 L41755152410.2  L42465301314.2  L44015431570.323L45311526170.2  L45557011165.3  L46358212179.81 L46411501870.1  L46887489953.87 L48495763134.81 L48820956452.81 L50817913293.1  L51352513313.0  L52517307421.3  L52674297804.1  L52999747263.2  L56731337262.1  L5849476301.1   L58972694979.81 L5930101465.81  L59824185306.2  L61733553549.1  L62122639501.1  L62513011098.2  L63199674356.299L63525406413.1  L63767516462.1  L64584198451.87 L64850595401.0  L65289942669.1  L65412898018.81 L65514909405.2  L65862516566.2  L6667856541.2   L66851658419.81 L67070089790.2  L67081784269.1  L67260533069.1  L711582733.1    L7508641999.3   L9090702513.71  L9424968909.1   L9823343769.81  L9976516746.1   P1041757538.310 P1103805628.310 P12729896508.310P16481615804.310P18389176255.310P19450525567.310P19976377707.310P20038771388.310P20979511989.310P23097620927.310P26375167676.310P26654780607.310P30999741941.310P31856825266.310P32812358207.310P33685091132.310P3982783807.310 P41755070908.310P42463566578.310P43679441343.310P45311182012.310P45554745498.310P48368720831.310P51925880511.310P52519507546.310P59824037500.310P62513354812.310P65512515437.310P65860122342.310P6665331501.310 P8674438975.310 Q1103805628.310 Q12729896508.310Q15985628819.312Q16071902362.276Q16481615804.310Q19501380185.310Q19561186129.310Q20038771388.310Q20979511989.310Q21109815402.310Q21229638117.310Q26375167676.310Q30509110512.310Q30999741941.310Q31856825266.310Q32025141418.310Q3207261198.310 Q33685091132.310Q41755070908.310Q42463566578.310Q45311182012.310Q45554745498.310Q52519507546.310Q52999304985.310Q53913079098.276Q59578101107.312Q59824037500.310Q6203530546.310 Q62513354812.310Q65512515437.310Q65860122342.310Q6665331501.310 Q66733030426.276Q67070757567.310Q67866622394.276Q68266871398.310Q7508203598.310 Q8931203145.310 Q9634228910.310 00000Q01601[02<02]03>03_04@04a04b04c04d04e05F05k06L07207S07T08508608S08[08\0;20;70;80=O0?T0AD0C[0D00DI0Dk0Dl0EA0G?0G@0IN0IO0IT0IU0IV0IW0I\0If0Ik0JI0JJ0JN0JS0JX0Je0Jj0M@0ME0MF0O60O70O<0OQ0OR0QS0QT0QU0QZ0R10R20T50Ug0WY0X60X?0XD0Xb0Zd0Zi0Zn0[20[70\\0\a0]>0]?0]@0]d0]e0]f0^;0^@0`H0bc0c80c=0c>0c?0cC0cD0cI0cN0ck0dC0dD0dI0dN0dO0dP0dU0dZ0e=0e>0eC0ea0eb0ec0ed0gf0gg0gl0h10h60h70hS0hX0i00i40iS0in0jI0jd0kc0lb0mD0m_0n90o80oS10R10m11H12G12b13a14<14W15V16116N17M18L18i19D19_1::1:T1:o1;n1;o1<01<11<i1<j1=a1>L1>M1>N1?M1@I1@J1A>1A?1A@1B?1C>1C?1C@1CA1CB1CC1CD1D;1Dh1E@1EA1EU1EV1EW1EX1EY1FQ1GM1H:1Hf1Ie1J91JOS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HBP2p23Hp2S1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT2bs2FB3sp13SP1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOFS2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS3CRTFFFS3CRTS1R3HIA2hcS3CRTS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2PPS3CRTS3CRTS2PP3CRT1x2HxS3CRTS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ02p23Hp2FS3CRTS2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFS3CRTS1R2PP3CRT2lo2FB2x03APXFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX1q2e93HE92p23Hp2S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3S3CRTS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS3CRTS2loS3CRTS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9S3CRTS2sp2PP3CRT3BUF2bs3DPB2FB3sp1FFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12csFFS2sp2PP3CRT2bs2FB3sp1S3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HE93HBP2p23Hp2S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2bs2FB3sp1S3CRTSFS2x0FS3CRTS3CRTS2sp2PP3CRT3BUF2bs3B472FB3sp1S2sp2PP3CRT2bs2D12FB3sp1FS3CRTS3CRTFFS3CRTS3CRTS2sp2PP3CRT2bs2D12FB3sp13D1u2rk3HrkSS3CRTS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS3CRTS3CRTS3CRTFS2sp2PP3CRT2lo2bs2FB3sp13SP1S3CRTS2sp2PP3CRT2bs2D12FB3sp1S2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT3BUF2bs4LFB33LFB4DXBuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT3BUF2bs4LFB33LFB4DXBuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8FFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB2FB1c2HcFS2LF2bs4LFB33LFB3sp1FFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2bs4LFB33LFB3sp1S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG BASIC STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_basic : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv INV hc.
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    chunk_split XE 1%nat XE0 XE1. chunk_split XE1 1%nat XCA XE2'. chunk_split XE2' 1%nat XMP XKUr.
    replace (CRT + 640 + 4) with (CRT + 644) in * by (clear; lia). replace (CRT + 644 + 4) with (CRT + 648) in * by (clear; lia). replace (CRT + 648 + 4) with (CRT + 652) in * by (clear; lia).
    pose proof BASIC as SPK. unfold x509_basic_stmtA, A_X509_BASIC in SPK.
    idtac "ARM_BASIC-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPK with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (CA := CRT + 644) (MP := CRT + 648) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_KU_STACK_A, X509_NS_STACK_A, X509_BASIC_STACK_A, X509_SKID_STACK_A;
        first [ exact HHc | exact XCA | exact XMP | exact HPP | eassumption | reflexivity | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "ARM_BASIC-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_ku_postA, x509_ns_postA, x509_basic_postA, x509_skid_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & rk & p2 & cav & mpv
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & XCA2 & XMP2 & Hp2).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaab6c)) with (Z_to_bv 64 0xaab6c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "ARM_BASIC-BACK".
    xown_pres HP2 hc XO2.
    pres_call HP2.
    clear XO HHc HPP XCA XMP STlo SS1 MI.
    presA_transport HP2.
    clear HP2 SPK.
    switch_h hc h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (HBUD2 : BUD h2 Lx bp) by (unfold BUD in *; rewrite Evol2, Efr2; exact HBUD).
    idtac "ARM_BASIC-SWITCHED".
    assert (XE2 : rw_cells asegs m2 (CRT + 640) [C4 (x_et X); C4 cav; C4 mpv; C4 (x_ku X)]).
    { apply (proj2 (rw_cells_app asegs m2 (CRT + 640) [C4 (x_et X)] [C4 cav; C4 mpv; C4 (x_ku X)])). split; [exact XE0|]. cbn [cells_size csize Nat.add].
      replace (CRT + 640 + Z.of_nat 4) with (CRT + 644) by (clear; lia).
      apply (proj2 (rw_cells_app asegs m2 (CRT + 644) [C4 cav] [C4 mpv; C4 (x_ku X)])). split; [exact XCA2|]. cbn [cells_size csize Nat.add].
      replace (CRT + 644 + Z.of_nat 4) with (CRT + 648) by (clear; lia).
      apply (proj2 (rw_cells_app asegs m2 (CRT + 648) [C4 mpv] [C4 (x_ku X)])). split; [exact XMP2|]. cbn [cells_size csize Nat.add].
      replace (CRT + 648 + Z.of_nat 4) with (CRT + 652) by (clear; lia). exact XKUr. }
    clear XE0 XCA2 XMP2 XKUr.
    fold_xinv_at INV2 m2 h2 Lx (setbc X cav mpv) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "ARM_BASIC-OK".
      eapply tail_walk with (q := p2) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP | match goal with |- ?g => idtac "ARM_BASIC-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "ARM_BASIC-ERR".
    eapply errj_walk with (p' := p2) (bp := bp); first [ exact INV2 | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP EX1 EX2 Hrk | match goal with |- ?g => idtac "ARM_BASIC-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02@0@D10651567415.277D10833959634.308D11806979143.277D12654479616.308D14758091877.277D17704051245.277D24125724923.308D32452447318.308D3269699907.308 D35884995692.308D3886322623.308 D39258386159.308D52045774220.308D54248487652.308D59473897855.310D6203530546.308 D68409308397.308D6897247976.308 D904953340.308  L1041497707.81  L10837002389.2  L11807424497.81 L12386308030.81 L12654381620.1  L12729978778.2  L12986590262.81 L13527341729.87 L13792348351.2  L14096410875.83 L14757681107.81 L14895519901.2  L1530387784.71  L15491099229.3  L15844907397.81 L16482024986.2  L17698511112.81 L19053264781.1  L19979573058.81 L20038394650.2  L20977711877.2  L21230010724.3  L22416073485.1  L23615739305.3  L24882004373.71 L26375085850.2  L27111942217.1  L29680655011.1  L30507144274.2  L3075075738.83  L30997223346.3  L31862681339.81 L33685467802.2  L34165132787.81 L3482445079.81  L34837878146.83 L35144635169.0  L35655538583.72 L35916062925.81 L36035727278.2  L36839357581.1  L37090131545.81 L38235734261.1  L39360202971.81 L41114250165.81 L41755152410.2  L44015431570.320L44326392205.1  L45298129165.1  L45311526170.2  L46887489953.87 L48854501901.1  L49037321277.81 L49212034091.2  L49774294755.81 L50569572450.81 L52674297804.1  L57628700040.4  L58774595815.7  L58972694979.81 L59704496781.1  L62513011098.2  L63199674356.300L63560818383.3  L64584198451.87 L64850595401.0  L65862516566.2  L66057948813.1  L67070089790.2  L67939372226.2  L9090702513.71  L9976516746.1   P1041757538.308 P12729896508.308P14897123629.308P15493363738.308P16481615804.308P18389176255.308P19976377707.308P20038771388.308P20979511989.308P23097620927.308P26375167676.308P26654780607.308P30999741941.308P32812358207.308P33685091132.308P3982783807.308 P41755070908.308P45311182012.308P48368720831.308P51925880511.308P62513354812.308P65860122342.308P67941893490.308P8674438975.308 Q12729896508.308Q13791938841.308Q14897123629.308Q15493363738.308Q15985628819.310Q16481615804.308Q19561186129.308Q20038771388.308Q20979511989.308Q21229638117.308Q26375167676.308Q26483582778.276Q30509110512.308Q30999741941.308Q33685091132.308Q41755070908.308Q45311182012.308Q49212742826.308Q59578101107.310Q60713831066.276Q6203530546.308 Q62513354812.308Q63561518670.308Q65860122342.308Q67070757567.308Q67941893490.308Q68266871398.308Q8931203145.308 Q9634228910.308 00000Q01601W02<02]03>03_04@04A04B04C04D04i05J06006Q06R07307407Q07Y07n0:I0:N0:O0<f0>k0>l0@\0A10A20AK0AL0An0Ao0Cm0D20F@0FA0FB0FC0FH0FR0G00G10G50G:0G;0Hk0Hl0Jm0Jn0M00O30Pe0Pf0RX0S50S>0SC0S[0S_0UD0Ua0Ub0VF0VK0VP0VQ0XY0X^0[50[60]L0]j0]n0^;0^R0^o0_40_50_60_70_Z0_[0_\0_a0_b0_c0`?0`C0`b0a=0aX0b50bP0cO0d10dL0df0ee0f@0g?0gZ0hY0i40j30jN0ji0kh0lg0mB0m\0n70o60o70on0oo10010110210]10^10_11[11\12I13=13>13?13@13A14@14X15P15d15e16d16e17a17b18N18b198S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsS2sp2PP3CRT2bs2FB3sp1S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HBP2p23Hp2S2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT2bs2FB3sp13SP1FS2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFFS3CRTS1R3HIA2hcS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2PPS3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ02p23Hp2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX1q2e93HE92p23Hp2SS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3S3CRTS2sp2PP3CRT2bs2D12FB3sp1S2loS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9S2sp2PP3CRT3BUF2bs3DPB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12csS3CRTS3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HE93HBP2p23Hp2S3CRTS1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2x0S2PP3CRT1x2HxS1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT3BUF2bs3B472FB3sp1S3CRTFFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rk3HrkSFS3CRTFFS2sp2PP3CRT2lo2bs2FB3sp13SP1S2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT3BUF2bs4LFB33LFB4DXBuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3BUF2bs4LFB33LFB3DPBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2bs4LFB33LFB2FB1c2HcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB3sp1FS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPcS2LF2bs4LFB33LFB3sp1S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG SKID STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH TPV LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_skid : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv INV hc.
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof SKID as SPK. unfold x509_skid_stmtA, A_X509_SKID in SPK.
    idtac "ARM_SKID-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPK with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (SK := CRT + 480) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_KU_STACK_A, X509_NS_STACK_A, X509_BASIC_STACK_A, X509_SKID_STACK_A;
        first [ exact HHc | exact XK | exact HPP | eassumption | reflexivity | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "ARM_SKID-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_ku_postA, x509_ns_postA, x509_basic_postA, x509_skid_postA in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & rk & p2 & tgv & lnv & qv
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & XK2 & Hp2).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xaac0c)) with (Z_to_bv 64 0xaac0c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "ARM_SKID-BACK".
    xown_pres HP2 hc XO2.
    pres_call HP2.
    clear XO HHc HPP XK STlo SS1 MI.
    presA_transport HP2.
    clear HP2 SPK.
    switch_h hc h2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (HBUD2 : BUD h2 Lx bp) by (unfold BUD in *; rewrite Evol2, Efr2; exact HBUD).
    idtac "ARM_SKID-SWITCHED".
    fold_xinv_at INV2 m2 h2 Lx (setsk X tgv (x_k2 X) lnv qv) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "ARM_SKID-OK".
      eapply tail_walk with (q := p2) (p0 := p0) (bp := bp); first [ exact INV2 | exact KLOOP | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP | match goal with |- ?g => idtac "ARM_SKID-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "ARM_SKID-ERR".
    eapply errj_walk with (p' := p2) (bp := bp); first [ exact INV2 | exact HBUD2 | eassumption | xl HP0 HQ0 HQE HE9 Hp2 HBP EX1 EX2 Hrk | match goal with |- ?g => idtac "ARM_SKID-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L24720758687.185L24837285092.181L24837285731.182L29436641091.178L29440768123.177L29442917112.180L29442917243.179L51234907738.180L51234908121.17900002Z04Z06Z07C07l08U09>09i0:TS1R3HIA4PHIx4FFRx1h2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT01d2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R2hc2bp1q2e94PHIc4FFRc3B1'3B2'1H2H02H12H22H32H42H52H6S2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX22bp1q2e92Hb2Hq2HeS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX22bp1q2e92Hb2Hq2HeS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11q2e92HqS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12bp1q2HbS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12bp1q2Hb". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 STKc1 PHIx_mono FFRx_mono PHIx_sadd FFRx_sadd LB LF sp PP CRT BUF lo slo bs LFB3 LFB PP0 BIN B1 B2 B3 DPB CRT0 DXB D1 SLOS SLOL SLO SPH LOS BUDV BUDF FB sp1 SP1 FRSH APP APC SPR ALO ACV F0 APB D1u DXBu SP1R ENDX EX1 EX2"] Lemma BUD_pre : forall (hc : HST asegs R HIA) Lx bp q e9 (PHIc : Z -> Z) (FFRc : Z -> Z -> Z),
    BUD hc Lx bp -> P <= bp <= q -> q <= e9 -> e9 <= END ->
    (forall a, 0 <= a -> PHIc a <= PHIx a) -> (forall a e, 0 <= a -> FFRc a (e + 1) <= FFRx a e) ->
    havol asegs R HIA hc + PHIc (e9 - q) <= AVOL_MAX /\ hfr asegs R HIA hc + FFRc (e9 - q) (d + 1) <= FR_MAX.
  Proof.
    (intros hc Lx bp q e9 PHIc FFRc dd_H; ddestruct dd_H as (B1' & B2' & _); intros Hb Hq He LP LF0).
    pose proof (LP (e9 - q) ltac:(lia)). pose proof (LF0 (e9 - q) d ltac:(lia)).
    pose proof (PHIx_sadd (bp - P) (e9 - q) ltac:(lia) ltac:(lia)). pose proof (FFRx_sadd (bp - P) (e9 - q) d ltac:(lia) ltac:(lia)).
    pose proof (PHIx_mono (bp - P + (e9 - q)) (END - P) ltac:(lia)). pose proof (FFRx_mono (bp - P + (e9 - q)) (END - P) d ltac:(lia)).
    pose proof BUDV. pose proof BUDF. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L23586022611.191L23586022736.192L23586022865.193L29436641091.186L29442916862.190L29442916985.189L29442917112.188L29442917243.187L29442931781.185L30734092901.194L51234907484.190L51234907738.188L51234907867.18900002604<06B07407f08X09J0:<0:n0>>0?20?f0@ZS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX22Lx5nodes2bp1q2e92Hb2HqS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX22Lx5nodes2bp1q2e92Hb2HqS2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX22Lx5nodes2bp1q2e92Hb2HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12Lx5nodes1q2e92HqS1R3HIA4PHIx4FFRx4CNTx1h2LF2sp2PP3CRT1P3END3BUF2bs4LFB33LFB3PP02B12B22B33DPB4CRT01d2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R2hc2h'2Lx5nodes2bp1q2e94PHIc4FFRc4CNTc3B1'3B2'3B3'2HV2HF2HN1H2H02H12H22H32H42H52H62H7S2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx5nodes2bp1q2HbS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx5nodes2bp1q2HbS2LF2sp2PP3CRT1P2bs4LFB33LFB2FB3sp12Lx5nodes2bp1q2Hb". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 STKc1 PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd LB LF sp PP CRT BUF lo slo bs LFB3 LFB PP0 BIN B1 B2 B3 DPB CRT0 DXB D1 SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APP APC SPR ALO ACV F0 APB D1u DXBu SP1R ENDX EX1 EX2"] Lemma BUD_post : forall (hc h' : HST asegs R HIA) Lx (nodes : list Z) bp q e9 (PHIc : Z -> Z) (FFRc : Z -> Z -> Z) (CNTc : Z -> Z),
    BUD hc Lx bp -> P <= bp <= q -> q <= e9 -> e9 <= END ->
    (forall a, 0 <= a -> PHIc a <= PHIx a) -> (forall a e, 0 <= a -> FFRc a (e + 1) <= FFRx a e) -> (forall a, 0 <= a -> CNTc a <= CNTx a) ->
    havol asegs R HIA h' <= havol asegs R HIA hc + PHIc (e9 - q) -> hfr asegs R HIA h' <= hfr asegs R HIA hc + FFRc (e9 - q) (d + 1) ->
    Z.of_nat (length nodes) <= CNTc (e9 - q) ->
    BUD h' (SSEQ (rev nodes) ++ Lx) e9.
  Proof.
    (intros hc h' Lx nodes bp q e9 PHIc FFRc CNTc dd_H; ddestruct dd_H as (B1' & B2' & B3'); intros Hb Hq He LP LF0 LC HV HF HN). unfold BUD.
    pose proof (LP (e9 - q) ltac:(lia)). pose proof (LF0 (e9 - q) d ltac:(lia)). pose proof (LC (e9 - q) ltac:(lia)).
    pose proof (PHIx_sadd (bp - P) (e9 - q) ltac:(lia) ltac:(lia)). pose proof (FFRx_sadd (bp - P) (e9 - q) d ltac:(lia) ltac:(lia)).
    pose proof (CNTx_sadd (bp - P) (e9 - q) ltac:(lia) ltac:(lia)).
    pose proof (PHIx_mono (bp - P + (e9 - q)) (e9 - P) ltac:(lia)). pose proof (FFRx_mono (bp - P + (e9 - q)) (e9 - P) d ltac:(lia)).
    pose proof (CNTx_mono (bp - P + (e9 - q)) (e9 - P) ltac:(lia)).
    rewrite length_app. unfold SSEQ. rewrite length_map, length_rev. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L26892418956.1 L38087549238.74L46179325431.71L49806183697.71L52101693566.74L56658999053.1 L62030907467.71L698145521.71  00000402Z04;04T07507908K08dS2spS1R3HIA3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R2hc1a2HaS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPA2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp13SP1S1R3HIA3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT02D14SLOS4SLOL2FB3sp13APP5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4SP1R2hc1a2HaS2spS1R3NS14STKc5STKc12sp2PP3CRT2lo2bs3PP04CRT02D13SPH3LOS2FB3sp13SPR2F04SLOu3D1u4SP1RS2sp2PP3CRT2bs2FB3sp13SPR". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 STKc1 P END BUF lo slo bs LFB3 LFB PP0 PPLO BIN B1 B2 B3 DPB CRT0 CRTLO DXB D1 SLOS SLOL SLO SPA SPH LOS UW FB SP1 FRSH APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R"] Lemma uwc_callee : forall (hc : HST asegs R HIA) mq, presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) W m mq ->
    hstkhi asegs R HIA hc = hstkhi asegs R HIA h -> rw_cells asegs mq (bv_unsigned sp + -104) SAVEL ->
    uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1).
  Proof.
    intros hc mq PRES HSc SAVE. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UWa : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { rewrite <- HSc. eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | xl| rewrite HSc; apply hstkhi_le64; xl].
      intros a Ha. cbn [outside]. split; [| split; [| exact I]]; xl Ha. }
    pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| xl| xl| exact D0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac switch_hm hc h3 HCS3 HT3 HS3 HF3 :=
    lazymatch goal with PRx : presW _ _ _ hc _ _ _ _ _ _ _ |- _ => apply (presW_hmono R HIA hc h3) in PRx; [| exact HCS3| exact HS3] end;
    repeat match goal with H : aobj _ _ (hcs asegs R HIA hc) _ _ _ |- _ => eapply aobj_cs_mono in H; [| exact HCS3] end;
    repeat match goal with H : crange (hcs asegs R HIA hc) _ _ |- _ => eapply crange_mono in H; [| exact HCS3] end;
    lazymatch goal with HCz : (forall x, CS x -> hcs asegs R HIA hc x) |- _ =>
      let HCn := fresh "HCSn" in assert (HCn : forall x, CS x -> hcs asegs R HIA h3 x) by (intros ? Hxx; apply HCS3; apply HCz; exact Hxx); clear HCz end;
    lazymatch goal with HTx : htop asegs R HIA hc = htop asegs R HIA h |- _ => rewrite <- HT3 in HTx end;
    lazymatch goal with HSx : hstkhi asegs R HIA hc = hstkhi asegs R HIA h |- _ => rewrite <- HS3 in HSx end;
    lazymatch goal with HFx : hflag asegs R HIA hc = hflag asegs R HIA h |- _ => rewrite <- HF3 in HFx end;
    repeat match goal with CWx : client_wrange _ _ _ (htop asegs R HIA hc) _ _ |- _ => rewrite <- HT3 in CWx end;
    repeat match goal with LW : ainv_laws _ _ |- _ => clear LW end; repeat match goal with KW : kinv_laws _ _ _ |- _ => clear KW end;
    repeat match goal with OKx : cs_ok _ (hcs asegs R HIA hc) |- _ => clear OKx end;
    pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo0) as KINV;
    pose proof (hcs_ok asegs R HIA h3) as CSOKc.

  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.

  Ltac eks_upto a :=
    do 40 (try (lazymatch goal with
            | |- context [MS _ _ (Z_to_bv _ ?z) _ _ _ _] =>
                tryif constr_eq z a then fail else zstep
            end)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "05D0@D10821638613.335D10821638613.336D12658412039.335D12658412039.336D13883028887.336D20192390267.335D20192390267.336D24138570748.336D26320322782.336D32456904529.336D35872675691.336D39246065128.336D39393927417.297D40347303003.297D45734692876.295D45734692876.296D50818716548.295D50818716548.296D53931543010.336D54252419555.336D55359555307.336D59473897855.338D64542751972.336D68405377002.336D6910092783.336 L1103920410.2   L11102061048.7  L12159727117.328L12219578755.2  L12408116378.2  L12729978778.2  L13327730124.15 L13327730124.71 L13723086456.284L14447004729.1  L1495418167.1   L15880435332.0  L16482024986.2  L16665599946.329L1681965944.283 L1685717371.0   L17694163776.4  L17698511112.81 L18787422891.2  L18902662738.72 L19246785069.3  L1931356442.2   L19716925466.2  L19733363960.284L1973388888.2   L20038394650.2  L20132924173.1  L20407710113.0  L20591839669.4  L20764778599.3  L20977711877.2  L21230010724.3  L21543769459.1  L21868500043.2  L22429105105.3  L22939159100.2  L23615739305.3  L23766154372.3  L23766154372.327L23766295288.328L2397676628.0   L24274980288.8  L24882004373.71 L24982572641.328L26375085850.2  L27111942217.1  L27129241434.2  L27183073553.2  L27220347674.2  L27441344141.1  L27770558747.341L29113994439.72 L29113994439.73 L29115994680.75 L29680655011.1  L30317936740.339L30507144274.2  L30537593450.81 L30547658846.4  L30997223346.3  L30999827341.1  L32101379871.71 L32370222259.5  L32372465287.81 L3341165766.13  L33621928456.283L33621928456.329L33621928456.330L33685467802.2  L33944861052.3  L33949630190.82 L3556261661.2   L35655538583.72 L36284119432.284L36284119432.329L36284119432.330L36968206175.2  L37601257542.81 L37611590258.3  L37751024858.1  L38235734261.1  L39188636933.0  L39360202971.81 L39361869531.5  L39393878129.81 L40228640085.0  L40347352275.81 L40834179097.284L41384546593.328L43673066929.2  L44015431570.350L44024548616.284L44024548616.329L44024548616.330L44166924249.3  L44497566527.2  L45132626669.4  L45147209945.81 L45198854750.1  L45311526170.2  L45422963981.1  L45524555192.75 L45572707994.2  L4741393131.4   L4787798581.298 L48021273660.81 L48027698696.4  L48590263053.1  L48935655962.2  L52035364018.339L52035364018.340L52067437893.328L52298477466.2  L52364995805.3  L52674297804.1  L53519146049.328L56094209037.1  L57231218569.10 L57295000472.2  L57309571500.81 L57628700040.4  L57953772231.3  L57960470771.81 L58230853383.83 L58232966598.339L58774595815.7  L59308580059.18 L59308636694.4  L59314873579.340L59650586893.1  L59812994776.2  L59979071514.2  L62513011098.2  L63013399693.1  L63164192282.2  L63423827493.81 L63430210577.5  L63762452899.11 L63870280659.1  L64850595401.0  L65862516566.2  L67070089790.2  L68404552233.1  L7735748552.2   L7739070844.1   L8341522782.327 L8352289251.72  L847347010.2    L9090702513.71  L9356328015.3   L9968018885.4   L9976516746.1   P1091485627.336 P12226132804.295P12226132804.296P12406281821.295P12406281821.296P12717575483.336P16486071483.336P19252084101.336P1945250781.295 P1945250781.296 P19727149789.295P19727149789.296P20042703291.336P20304552209.335P20983968178.336P21870859916.295P21870859916.296P22810288773.336P22945712379.295P22945712379.296P23943998341.336P26387488187.336P27192773590.295P27192773590.296P27222706653.295P27222706653.296P30995810034.336P33658472965.336P33672769595.336P3541808554.336 P38358786053.336P41915405573.336P44164039966.295P44164039966.296P45298862011.336P45578736733.295P45578736733.296P48924907741.295P48924907741.296P49335259600.335P52308700509.295P52308700509.296P52375911837.336P58948478981.336P59993490141.295P59993490141.296P62525676347.336P63150298333.295P63150298333.296P63638537733.336P63855862036.295P63855862036.296P65856189921.336P7750690063.295 P7750690063.296 P845346805.336  Q1091485627.336 Q11701567452.292Q11923259256.295Q11923259256.296Q12717575483.336Q13115886455.335Q13218680698.339Q14342782865.292Q14439821615.292Q14633631689.292Q14748057007.292Q16464982057.295Q16464982057.296Q16486071483.336Q18694161525.292Q18775769389.336Q19548864598.336Q20042703291.336Q20983968178.336Q21234094818.335Q22318986966.295Q22318986966.296Q22712450012.295Q22712450012.296Q23622942117.292Q24266756109.338Q24266758939.339Q25662375842.292Q25744492968.336Q26387488187.336Q26630460045.338Q26630461851.339Q27141967068.336Q2757736384.295 Q2757736384.296 Q30513043447.336Q30995810034.336Q31228693025.292Q32681824661.295Q32681824661.296Q33185020915.292Q3346908627.292 Q33672769595.336Q34347144132.292Q35014420759.292Q3541808554.336 Q35538325567.292Q39240041937.335Q39929887636.338Q40490463228.338Q41215189549.291Q42439443119.295Q42439443119.296Q43684777527.336Q44501580190.336Q45298862011.336Q45736968716.294Q45736968716.295Q46047340060.338Q4746207366.292 Q48955085998.339Q48955088824.338Q49698585326.293Q49698585326.294Q49746415830.295Q49746415830.296Q52375911837.336Q52938668945.292Q53931543010.335Q53969773690.292Q54124877425.292Q54966019630.339Q54966021432.338Q55031048408.339Q55031185675.338Q55359555307.335Q56922339960.339Q56980812955.339Q56980815757.338Q5785216945.295 Q5785216945.296 Q59578101107.338Q60993336238.339Q60993337528.338Q62525676347.336Q64255469685.292Q64313098711.294Q64313098711.295Q65097480877.291Q65856189921.336Q67038978349.295Q67038978349.296Q67066825144.336Q67638958832.292Q67638958832.293Q68013150533.295Q68013150533.296Q68169048111.292Q68210664471.292Q68279191905.335Q8429011631.292 Q845346805.336  Q8699115497.295 Q8699115497.296 Q9351262153.335 Q9559455197.292 Q9646549417.336 00000[01F02102\02]02^02_03F04104X04Y04Z05;05\07B08h0:D0;`0<G0<n0=U0>A0>B0>C0>j0>k0>l0@L0@M0@N0@O0@P0B40BU0BZ0B_0B`0Ba0CH0Ci0Cj0Ck0Ei0Ej0FM0FN0FO0FP0G10G;0G<0GA0GB0GJ0GR0GS0GT0GY0GZ0Ge0Gf0H00H;0H<0H=0H>0H?0H]0ID0IE0II0IJ0IK0IL0IQ0K^0LN0N;0P70P<0Pj0Pk0SG0SH0SI0SN0Sg0Sh0TE0U30UT0V;0Vb0Vc0Vd0WN0WO0YA0Yb0ZI0[00[90[S0[T0[Y0[]0[^0]C0]D0]Y0]Z0]o0^R0^S0^T0_>0__0`F0`m0`n0`o0a00aH0aM0aN0aS0c@0cA0cB0cg0dE0dF0dK0dL0e30eZ0e[0e\0e]0ea0fH0fM0g20g30i40iA0iB0kD0mI0n>0nU0o30o:10?10D10N10O10P10U10V12d12e12f12g12h12i12j12k12l13114Q16I16J16f16g16o17317T18_19j1;:1<J1<k1=L1=j1?:1@J1AZ1Bj1CK1D31DS1E^1Fi1H01I;1JF1Jd1KE1LY1Mm1O=1PK1Pl1QJ1Qk1RL1Rj1SH1TU1Ub1VC1WS1Xc1Z31[C1[h1]81^H1^k1_I1`Y1ai1bJ1cZ1dj1eH1fW1gf1hF1i01iZ1j;1j<1j=1kH1lS1lT1mN1mh1n81o01o11o^1o_1o`1oa20821?22022122223423523623`24J24`25D25h25i25j25k26O27328529@2:K2;E2;F2;^2;_2;`2;a2;b2;c2;d2<<2<=2<>2<X2=22=32=`2>N2??2@F2AE2AF2BM2CT2Cn2Co2Di2Ec2FE2Fg2G_2HW2HX2HY2I32IK2Ia2J[2KU2Ko2LI2Lc2Mc2NG2Nk2P;2QK2Qi2Rc2S]2S^2S_2T[2UW2VO2VP2WW2X^2Y`2Z72ZN2\A2^42^a2^b2_T2`L2`M2aM2bM2cR2cS2coS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes1x2HxFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1R5nodesFFFFS1R3NS14STKc5STKc12sp2PP3CRT2lo3slo2bs3PP04CRT02D14SLOS4SLOL2FB3sp13SP13SPR3ALO3ACV2F04SLOu3D1u4SP1RS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3sp1S3CRTSFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS1R2sp2PP3CRT2bs2D12FB3sp13D1u4CSTKSFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3sp14SP1MFS3CRTSS2rc3Hr3S2rc3Hr3FFS3sp1FS2rc3Hr32KrFS1R3HIA2hcS2rc3Hr32KrFFSFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFS2PPFFFS3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B22B33DPB4CRT02FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R2p45nodes4Hp4'S1R3HIA1h2sp2PP3CRT2lo2bs5CRTLO2D12FB3sp13D1u2XXS1R2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR3ALO2F02F13APB3D1u4DXBu4SP1R3DLO2XXS1R2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR3ALO2F02F13APB3D1u4DXBu4SP1R1B1k2HR3Bce3FB'2n'3HR'S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12rc5nodes3Hr3FS1R4STKc4STKq5STKcq2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFS3CRTS2sp2PP3CRT2bs2FB3sp13SP1FS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S1R3NS14STKc5STKc02sp2lo3slo4SLOL3sp13SP14SLOuS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFS2sp2PP3CRT1P3END2bs2D12FB3sp13D1u2e94Hp4'FS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF4LFB3S2sp2PP3CRT2bs4CRT02FB3sp1FS3sp1S2loSS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9FS2sp2PP3CRT2bs2FB3sp1SS2sp2PP3CRT2bs2FB3sp1S1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes2csS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFS2sp2PP3CRT2bs2D12FB3sp1S3CRTFS3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9FFS2LF2sp2PP3CRT2bs4LFB33LFB1d2FB3sp11HS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS3CRTFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFS2x0S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS3CRTS1R3NS14STKc5STKc02sp2lo3sp13SP14SLOuFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2PP3CRT1x2HxFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE92p43Hp4S2LF2sp2PP3CRT1P3END2bs4LFB33LFB2FB3sp12p45nodes4Hp4'S1R2PP3CRT2lo2FB2x03APXS3CRT2r03ALC1r2Ka1q1H2H02q02H4S2rc2KsS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes1H3PP04CRT03SPR2F04SP1R2rc3Hr3S3CRTS3sp14SP1MFFS3CRTFS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFFSFFFFS3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1R5nodesS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1RFS2sp2PP3CRT2lo2bs2FB3sp13SP1FS2rc3Hr3S2x0S2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2bs4LFB33LFB3sp15nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB3sp15nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO3ACV4SLOu4EGSB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO3ACV4SLOu4EGSB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPB5nodesS2LF3CRT2bs4LFB33LFB3sp15nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS2LF3CRT2bs4LFB33LFB3sp15nodesS2LF3CRT2bs4LFB33LFB3sp15nodesS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF2PP2lo2bs4LFB33LFB4PPLO3sp15nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF3CRT3BUF2bs4LFB33LFB4DXBu5nodesS2LF3CRT2bs4LFB33LFB3sp15nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB3sp15nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO3ACV4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO3ACV4SLOu2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP5nodesS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_stS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC5nodesFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12hc3HSc5HTOPc5nodesS2LF3CRT2bs4LFB33LFB5nodesS2LF2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFFFS1R2LF2bs4LFB33LFB4EGSBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK5nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F85nodesFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesFFS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_stS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB3ELOS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesFFFS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu5nodesFS1R2LF2bs4LFB33LFB5ALWF'FFFFFFS1R2LF2bs4LFB33LFB5ALWF'FFS2LF2bs4LFB33LFB3sp15nodesS2LF3CRT2bs4LFB33LFB5nodesFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R2LF3slo2bs4LFB33LFB4SLOS3sp12HB5Ha_st5Hl_stS1R2LF2sp3slo2bs4LFB33LFB4SLOS3sp12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS4SLOu4CSTK5nodesFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB5nodesFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesS2LF2bs4LFB33LFB3sp14SP1R2HB5Ha_stS2LF2bs4LFB33LFB3sp14SP1R2HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPc2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB3sp15nodesS1R2LF2bs4LFB33LFB5ALWF'S1R2LF2bs4LFB33LFB3EHIS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesS2LF3CRT2bs4LFB33LFB5nodesS2LF3CRT2bs4LFB33LFB5nodesS2LF2bs4LFB33LFB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1R5nodesS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu4CSTK2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB5nodes1c2HcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS2LF2bs4LFB33LFB3sp12HBS2LF2bs4LFB33LFB3sp12HBS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB4PPLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu6CRTLOu4SBND4CSTK2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB4PPLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu6CRTLOu4SBND4CSTK2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPc5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesFS2LF2bs4LFB33LFB2FB2F05nodes".
  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIq FFRq CNTq STKq SEQOF STKc1 STKcq PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma eku_sub : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x5 x6 x7 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    Z.land (x_seen X) 2048 = 0 ->
    (forall b, b = 1 \/ b = 8 \/ b = 32 \/ b = 2048 -> Z.land (bv_unsigned (x_et X)) b = 0 -> Z.land (Z.lor (x_seen X) 2048) b = 0) ->
    (forall (h3 : HST asegs R HIA) (m4 : mem) (Lx3 : list blk) (X3 : xst) (rv p4 : Z)
            (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       xinv Lx3 m4 h3 X3 (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb ->
       rw_cells asegs m4 PP [C8 (Z_to_bv 64 p4)] -> P <= p4 <= END -> BUD h3 Lx3 e9 ->
       -2^31 < rv <= 0 -> (rv = 0 -> p4 = e9) ->
       aevtA asegs (KF asegs R HIA h3 mo0) POST
         (MS (mkR y1 (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rv) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
                  (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) y28 y29 y30 y31)
             F (Z_to_bv 64 0xaac60) fc None m4 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR (Z_to_bv 64 0xaac60) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 PP) (Z_to_bv 64 e9) (Z_to_bv 64 (CRT + 656)) x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 (CRT + 640)) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xab21c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HZ HSUB KCONT.
    dpose INV as (_ & _ & _ & _ & _ & XO0 & _). ddestruct XO0 as (_ & _ & _ & _ & _ & _ & _ & XZ4 & _). ddestruct (XZ4 HZ) as (Z1 & Z2 & Z3 & Z4). clear XZ4.
    open_xinv_mu INV hc.
    rewrite Z1, Z2, Z3 in XU.
    destruct (stk_carve asegs mm lo sp1 32 STlo ltac:(first [ clear - SP1 SLO SLOu NS1 STKc0; lia | xl ])) as [STF [jfr FRM]].
    replace (sp1 - Z.of_nat 32) with (sp1 + -32) in FRM, STF by (clear; lia).
    apply (rw_cells_split_CB asegs mm (sp1 + -32) [] 32 jfr [] [8; 8; 8; 8]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    cb8_at FRM 0%nat. cb8_at FRM 1%nat. cb8_at FRM 2%nat. cb8_at FRM 3%nat.
    pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB.
    destruct IMG' as (EGOT & ELO & EHI & EGSB).
    rewrite EGOT in GOT.
    assert (CSTK : CRT + 696 <= arl_stklo R).
    { destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [BR _]. rewrite Forall_forall in BR.
      pose proof (art_data_lo asegs R HIA) as DLO.
      destruct (CWX (CRT + 695) ltac:(first [ clear; lia | unfold EXT_SIZE; clear; lia ])) as [XX|[XX|XX]]; [xl XX| xl XX DLO|].
      ddestruct XX as ([B k] & HB & HR). cbn [fst snd] in HR. apply in_app_iff in HB. destruct HB as [HB|HB].
      - ddestruct (BR (B, k) ltac:(apply in_app_iff; left; apply in_or_app; right; exact HB)) as (_ & _ & Bce & _). cbn [fst snd] in Bce. xl Bce HR.
      - ddestruct (in_fdata_hull LF (B, k) (CRT + 695) HB ltac:(cbn [fst snd]; exact HR)) as ([FB' n'] & HF & HR').
        ddestruct (BR (FB', n') ltac:(apply in_app_iff; right; right; exact HF)) as (_ & _ & Bce & _). cbn [fst snd] in Bce, HR'. xl Bce HR'. }
    eks_upto (0x9a658)%Z.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    lazymatch goal with MU : munch _ ?m0 mg, WM : wmono _ ?m0 mg, XOx : xown _ ?m0 _ _, PMx : Permutation _ _, HHz : HM _ _ _ hc _ _ ?m0 /\ True |- _ =>
      lazymatch goal with HCz : (forall x, CS x -> hcs asegs R HIA hc x) |- _ => pose proof (xown_mu hc _ _ _ _ XOx PMx (proj1 HHz) HCz MU WM) as XOg end;
      clear XOx MU WM HHz end.
    rename XOg into XO.
    lazymatch goal with SSx : sshad _ _ mg slo sp1 |- _ =>
      destruct (sshad_split asegs AL mg slo (sp1 + -32) sp1 SSx ltac:(first [ clear - SP1 SLO SLOL SLOu SLOS NS1 STKc0; lia | xl ]) ltac:(clear - SP1M; lia)) as [SSa SSb]; clear SSx end.
    destruct (BUD_pre hc Lx bp q e9 PHIq FFRq HBUD HBP HQE ltac:(xl HE9 EX2) PHIq_le FFRq_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHc) as NDLx.
    assert (BINx : In (BUF, n) (Lx ++ LB)) by (apply in_app_iff; right; exact BIN).
    idtac "EKS-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SEQOF with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (CUR := CRT + 656) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                        (ct := x_ect X) (cpad := x_ecp X);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit (sp1 + -32)) by (first [ clear - SP1R SP1 SLO SLOu SLOS NS1 STKc0 LOS; lia | xl ]);
        rewrite ?HTc, ?HSc; unfold SEQ_SIZE;
        first [ exact HHc | exact HK1 | exact XU | exact HPP | exact BPV | exact BPF | exact NDLx | exact BINx | exact I | eassumption | reflexivity
              | (clear - SP1M; lia)
              | (apply uwc_data; [ pose proof (uwc_nonneg _ _ _ _ _ _ _ UW); lia | rewrite ?(unsigned_lit (CRT + 656)) by xl CSTK; xl CSTK ])
              | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "EKS-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & h3 & rc & p4 & hct & hcpad & hcl & hcp & hcn & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HHD4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn. cbv beta in HEND.
    replace (ret_pc (Z_to_bv 64 0xab248)) with (Z_to_bv 64 0xab248 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite ?(unsigned_lit (sp1 + -32)) in ST4, SS4, HP4 by (first [ clear - SP1R SP1 SLO SLOu SLOS NS1 STKc0 LOS; lia | xl ]).
    unfold SEQ_SIZE in HP4.
    idtac "EKS-BACK".
    xown_pres HP4 hc XO2.
    pres_call HP4.
    pose proof (BUD_post hc h3 Lx nodes bp q e9 PHIq FFRq CNTq HBUD HBP HQE ltac:(xl HE9 EX2) PHIq_le FFRq_le CNTq_le HV3 HFR3 HCNT3) as HBUD3.
    clear XO HHc HPP XU STF SSa MI.
    try clear AB. try clear GOT. try clear GSB.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc h3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, NC4.
    pose proof (xown_seteku asegs m4 (Lx ++ LB) ((SSEQ (rev nodes) ++ Lx) ++ LB) X hct hcpad hcl hcp (hd 0 nodes) nodes XO2
                  ltac:(intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb) HSUB eq_refl NC4) as XO3.
    pose proof (xblocks_seteku Lx X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 2048) PERM Z4) as PERM3.
    clear XO2 PERM. unfold seq_cells in HHD4.
    idtac "EKS-SWITCHED".
    assert (Hp4' : P <= p4 <= END) by (xl Hp4 HP0 HQ0 HQE HE9 EX1 EX2).
    assert (OBP : aobj asegs AL (hcs asegs R HIA h3) m4 (CRT + 672) 8) by (eapply aobj_sub; [exact OEXT| clear; lia| clear; lia]).
    pose proof FRM as FRK. chunk_to_stk FRK.
    stk_merge_into ST4 FRK.
    replace (sp1 + -32 + 32) with sp1 in ST4 by (clear; lia).
    pose proof (sshad_merge asegs AL m4 slo (sp1 + -32) sp1 SS4 SSb ltac:(first [ clear - SP1 SLO SLOL SLOu SLOS NS1 STKc0; lia | xl ])) as SSm.
    clear SS4 SSb.
    fold_xinv_at INV2 m4 h3 (SSEQ (rev nodes) ++ Lx) (seteku X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 2048))
                 (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    eks_upto (0xaac60)%Z.
    if_cases Kr; zify_cond Kr.
    {
      assert (Rc0 : rc = 0) by (clear - Kr Hr3; try kland Kr; rewrite ?Z.mod_small in Kr by lia; Z.div_mod_to_equations; lia).
      pose proof (HEND Rc0) as EP4. subst p4.
      eks_upto (0xaac60)%Z.
      if_cases Ka; zify_cond Ka.
      { exfalso. clear - Ka ALC CRT0.
        change 7 with (Z.ones 3) in Ka. rewrite Z.land_ones in Ka by (clear; lia).
        try (change (2 ^ 3) with 8 in Ka).
        Z.div_mod_to_equations. lia. }
      eks_upto (0xaac60)%Z.
      match goal with |- context [Z.b2z (0 <? ?c)] => destruct (0 <? c) eqn:Kp end; cbn [Z.b2z].
      {
        match goal with |- context [Z.land (Z.land (?u + -1) ?mm) ?nn] =>
          replace (Z.land (Z.land (u + -1) mm) nn) with 0 by (vm_compute; reflexivity) end.
        eapply (KCONT h3 m4 _ _ 0 e9);
          first [ exact INV2 | exact HPP4 | exact HBUD3 | (intros _; reflexivity) | (clear; lia) | xl Hp4' HP0 HQ0 HQE HE9 EX1 EX2
                | match goal with |- ?g => idtac "EKS-KC1-LEFT:" g end ]. }
      {
        match goal with |- context [Z_to_bv 64 (Z.land (Z.land (?u + -1) ?mm) ?nn)] =>
          replace (Z_to_bv 64 (Z.land (Z.land (u + -1) mm) nn)) with (Z_to_bv 64 (-9572))
            by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) end.
        eapply (KCONT h3 m4 _ _ (-9572) e9);
          first [ exact INV2 | exact HPP4 | exact HBUD3 | (intros ?; exfalso; lia) | (clear; lia) | xl Hp4' HP0 HQ0 HQE HE9 EX1 EX2
                | match goal with |- ?g => idtac "EKS-KC0-LEFT:" g end ]. } }
    {
      assert (RN : rc <> 0) by (clear - Kr Hr3; intros ->; apply Kr; reflexivity).
      eks_upto (0xaac60)%Z.
      match goal with |- context [Z.land rc ?mk] => change mk with (Z.ones 64) end.
      rewrite Z.land_ones by (clear; lia). rewrite swrap32_errsum by (clear - Hr3 RN; lia).
      if_cases Ks; zify_cond Ks.
      2: { exfalso. clear - Ks Hr3 RN. rewrite ?signed_lit64 in Ks by lia. lia. }
      eks_upto (0xaac60)%Z.
      eapply (KCONT h3 m4 _ _ (rc + -9472) p4);
        first [ exact INV2 | exact HPP4 | exact HBUD3 | (intros ?; exfalso; lia) | lia | xl Hp4' HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "EKS-KCN-LEFT:" g end ]. }
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L24882004373.71 L27111942217.1  L29311549712.298L29311549712.3  L29680655011.1  L33947524594.83 L35655538583.72 L38235734261.1  L40228640085.0  L58451408828.3  L60528857433.79 L63174242230.79 L64850595401.0  L9090702513.71  Q10033713946.279Q47385839290.27900000N00R00S00^00c02a04S04W04X04c06T08A08B08^09V0:CS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPFS2rv3Hr32KrS3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loSS2rv3Hr32KrS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HP03HQ03HQES2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPc". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIq FFRq CNTq STKq SEQOF STKc1 STKcq PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_eku : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HZ HSUB KLOOP.
    pose proof INV as INV0.
    open_xinv INV hc.
    (* [comment removed for export] *)
    do 4 zstep.
    idtac "EKU-CALL".
    eapply (eku_sub hc _ Lx X lenw otg opd olen op crit et w0 w1 w2 k16 j1 j2 j3 j4 ja jb q p0 bp e9);
      [ exact INV0 | exact HPP | exact HP0 | exact HQ0 | exact HQE | exact HE9 | exact HBUD | exact HBP | exact HZ | exact HSUB | ].
    intros h3 m4 Lx3 X3 rv p4 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 HPP4 Hp4' HBUD3 Hr3 HEND.
    idtac "EKU-BACK".
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "EKU-OK".
      assert (Rc0 : rv = 0) by (clear - Kr Hr3; try kland Kr; rewrite ?Z.mod_small in Kr by lia; try (change 18446744073709551615 with (Z.ones 64) in Kr); rewrite ?Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
      pose proof (HEND Rc0) as EP4. subst p4.
      (* [comment removed for export] *)
      eapply tail_walk with (q := e9) (p0 := p0) (bp := e9); first [ exact INV2 | exact KLOOP | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 | match goal with |- ?g => idtac "EKU-TAIL-LEFT:" g end ]. }
      (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "EKU-ERR".
    eapply errj_walk with (p' := p4) (bp := e9); first [ exact INV2 | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 Hr3 | match goal with |- ?g => idtac "EKU-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0290@D10821638613.332D12658412039.332D24138570748.332D32456904529.332D3257379396.332 D35872675691.332D3881865400.332 D39246065128.332D52058619531.332D54252419555.332D59404705115.290D59473897855.334D6191210037.332 D66909528057.290D68405377002.332D6910092783.332 D892632827.332  L1103920410.2   L12729978778.2  L13912981005.1  L1530387784.71  L16482024986.2  L17698511112.81 L18426407565.1  L18914500057.81 L19979573058.81 L20038394650.2  L20977711877.2  L21221397901.1  L21230010724.3  L22429105105.3  L23298740641.0  L23615739305.3  L23766154372.3  L23766154372.324L24882004373.71 L27111942217.1  L29680655011.1  L30507144274.2  L30997223346.3  L31862681339.81 L33044181501.81 L33685467802.2  L33947524594.83 L3482445079.81  L35049601053.2  L35627757325.1  L35655538583.72 L36254073843.81 L36968206175.2  L38235734261.1  L39360202971.81 L40228640085.0  L40635971975.81 L41755152410.2  L44015431570.343L45311526170.2  L45524555192.75 L50129184591.3  L50134603179.2  L51007954957.1  L52674297804.1  L53587231807.2  L55225352820.83 L56658528582.81 L57628700040.4  L58230853383.83 L58316244877.1  L58774595815.7  L59404623315.81 L60528857433.79 L60917793037.1  L62513011098.2  L63174242230.79 L64850595401.0  L65239471420.81 L65481755714.2  L65862516566.2  L66909577073.81 L67070089790.2  L6798120973.1   L68499263453.3  L9090702513.71  L9976516746.1   P1054078565.332 P1091485627.332 P12717575483.332P16486071483.332P19971921516.332P20042703291.332P20983968178.332P23093689016.332P26650324920.332P30995810034.332P32799512888.332P33672769595.332P35064246954.332P3986716216.332 P41742750395.332P43683373752.332P45298862011.332P48381565112.332P51938201016.332P62525676347.332P65496663797.332P65856189921.332P68488093341.332P8687283256.332 Q1091485627.332 Q12717575483.332Q12919304250.282Q15985628819.334Q16486071483.332Q19548864598.332Q20042703291.332Q20983968178.332Q21234094818.332Q24582045082.282Q30513043447.332Q30995810034.332Q33672769595.332Q35064246954.332Q41742750395.332Q45298862011.332Q50115671241.332Q50139727405.332Q53599962782.332Q59578101107.334Q6191210037.332 Q62525676347.332Q65496663797.332Q65856189921.332Q67066825144.332Q68279191905.332Q68488093341.332Q8935136078.332 Q9646549417.332 00000[01F01m02T02U02V02W02X03C03j04K05705^06?06@06g06h06i06j06o07H07I09G09L09d0<20<30<40<90<:0<E0<F0<P0<[0<\0=:0=>0=C0=D0=E0?F0Ab0Ac0Ca0Ed0Ee0Ej0G\0I^0Ig0Ik0KP0KQ0Kn0Ko0LY0LZ0NG0NH0NI0NN0NR0NS0O60OP0O]0Qb0Qg0R>0RS0TD0TI0TJ0V70V80VV0VW0VX0Vm0Vn0W30W40WP0WT0X90XZ0Y;0Y\0ZD0Ze0[E0\J0]O0^00_50_V0`70a<0a]0bb0cC0dH0eM0en0fO0fo0gR0hW0hX0hY0iF0iG0iH0j90j:0j;0k=0l50lo0m00m10m20m30m40n90o>10;10Y11311411511612812j12k13E13aS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFS3CRTS2sp2PP3CRT2bs2FB3sp13SP1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS2sp2PP3CRT2bs2D12FB3sp1S1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFS3CRTFS2rc3Hr32KrSS1R3HIA2hcS2rc3Hr32KrFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R4STKc4STKs5STKcs2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2LF4LFB3S2loS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9SS2sp2PP3CRT3BUF2bs3DXB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes2csFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9FFS3CRTS2x0FS2sp2PP3CRT2bs2D12FB3sp13D1u2rc3Hr3S2sp2PP3CRT2bs4CRT02FB3sp1S2PP3CRT1x2HxS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE92p43Hp4S3CRTS1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HP03HQ03HQES3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FFS2sp2PP3CRT2bs2FB3sp1FS3CRTFS2sp2PP3CRT2lo2bs2FB3sp13SP1S2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp15nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3BUF2bs4LFB33LFB3DPB5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS2LF3CRT3BUF2bs4LFB33LFB4DXBu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F85nodesFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu5nodesFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu5nodesS2LF2bs4LFB33LFB2FB5nodes1c2HcS2LF2bs4LFB33LFB3sp15nodesFFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPc5nodesFS2LF2bs4LFB33LFB3sp15nodesS2LF2bs4LFB33LFB2FB2F05nodes". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIs FFRs CNTs STKs GSAN STKc1 STKcs PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIs_le FFRs_le CNTs_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_san : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HZ HSUB KLOOP.
    dpose INV as (_ & _ & _ & _ & _ & XO0 & _). ddestruct XO0 as (_ & _ & _ & _ & XZ4 & _). ddestruct (XZ4 HZ) as (Z1 & Z2 & Z3 & Z4). clear XZ4.
    open_xinv INV hc.
    rewrite Z1, Z2, Z3 in XS.
    (* [comment removed for export] *)
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof (uwc_callee hc mg PRES HSc SAVE) as UWF.
    destruct (BUD_pre hc Lx bp q e9 PHIs FFRs HBUD HBP HQE ltac:(xl HE9 EX2) PHIs_le FFRs_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHc) as NDLx.
    assert (BINx : In (BUF, n) (Lx ++ LB)) by (apply in_app_iff; right; exact BIN).
    idtac "SAN-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GSAN with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (CUR := CRT + 448) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                        (ct := x_sct X) (cpad := x_scp X);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold SEQ_SIZE;
        first [ exact HHc | exact HK1 | exact XS | exact HPP | exact UWF | exact BPV | exact BPF | exact NDLx | exact BINx | exact I | eassumption | reflexivity
              | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "SAN-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & h3 & rc & p4 & hct & hcpad & hcl & hcp & hcn & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HHD4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn. cbv beta in HEND.
    replace (ret_pc (Z_to_bv 64 0xaac28)) with (Z_to_bv 64 0xaac28 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold SEQ_SIZE in HP4.
    idtac "SAN-BACK".
    xown_pres HP4 hc XO2.
    pres_call HP4.
    pose proof (BUD_post hc h3 Lx nodes bp q e9 PHIs FFRs CNTs HBUD HBP HQE ltac:(xl HE9 EX2) PHIs_le FFRs_le CNTs_le HV3 HFR3 HCNT3) as HBUD3.
    clear XO HHc HPP XS STlo SS1 MI.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc h3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, NC4.
    pose proof (xown_setsan asegs m4 (Lx ++ LB) ((SSEQ (rev nodes) ++ Lx) ++ LB) X hct hcpad hcl hcp (hd 0 nodes) nodes XO2
                  ltac:(intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb) HSUB eq_refl NC4) as XO3.
    pose proof (xblocks_setsan Lx X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 32) PERM Z4) as PERM3.
    clear XO2 PERM. unfold seq_cells in HHD4.
    idtac "SAN-SWITCHED".
    fold_xinv_at INV2 m4 h3 (SSEQ (rev nodes) ++ Lx) (setsan X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 32))
                 (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    assert (Hp4' : P <= p4 <= END) by (xl Hp4 HP0 HQ0 HQE HE9 EX1 EX2).
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "SAN-OK".
      assert (Rc0 : rc = 0) by (clear - Kr Hr3; try kland Kr; rewrite ?Z.mod_small in Kr by lia; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite ?Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
      pose proof (HEND Rc0) as EP4. subst p4.
      eapply tail_walk with (q := e9) (p0 := p0) (bp := e9); first [ exact INV2 | exact KLOOP | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 | match goal with |- ?g => idtac "SAN-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "SAN-ERR".
    eapply errj_walk with (p' := p4) (bp := e9); first [ exact INV2 | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 Hr3 | match goal with |- ?g => idtac "SAN-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@D10821638613.332D12658412039.332D24138570748.332D32456904529.332D3257379396.332 D35872675691.332D3881865400.332 D39246065128.332D52058619531.332D54252419555.332D59473897855.334D61493878265.290D6191210037.332 D68405377002.332D6910092783.332 D720277339.290  D892632827.332  L1103920410.2   L12646939609.81 L12729978778.2  L1530387784.71  L16482024986.2  L17698511112.81 L17770731399.81 L18482501974.81 L18544217926.81 L19979573058.81 L20038394650.2  L20977711877.2  L21230010724.3  L22344741005.1  L22429105105.3  L23615739305.3  L23766152848.3  L23766152848.325L23766154372.3  L23766154372.324L240421692.81   L24446230945.0  L24882004373.71 L25901114765.1  L26375085850.2  L27111942217.1  L2732061976.83  L29653029901.1  L29680655011.1  L30507144274.2  L30997223346.3  L31862681339.81 L3214724365.1   L3217675720.10  L32361667354.326L33685467802.2  L33947524594.83 L3482445079.81  L35655538583.72 L36968206175.2  L37729285695.2  L38235734261.1  L38247320911.3  L39352661901.1  L39360202971.81 L40228640085.0  L41159122461.2  L41755152410.2  L44015431570.343L44378559987.81 L45524555192.75 L46660938509.1  L52674297804.1  L5281495517.3   L54926292493.1  L55225352820.83 L57628700040.4  L58230853383.83 L58774595815.7  L60528857433.79 L61493960049.81 L62513011098.2  L63174242230.79 L63711754818.2  L64850595401.0  L65862516566.2  L67070089790.2  L67368535979.2  L68375730189.1  L720359379.81   L9090702513.71  L9976516746.1   P1054078565.332 P1091485627.332 P12717575483.332P16486071483.332P18401496248.332P19971921516.332P20042703291.332P20983968178.332P26387488187.332P26650324920.332P30995810034.332P32799512888.332P33672769595.332P3986716216.332 P41165378730.332P41742750395.332P43683373752.332P48381565112.332P51938201016.332P5270644893.332 P62525676347.332P63709884661.332P65856189921.332P8687283256.332 Q1091485627.332 Q12386737853.335Q12717575483.332Q15985628819.334Q16486071483.332Q17729138106.282Q18560747546.282Q19548864598.332Q20042703291.332Q20535473440.335Q20983968178.332Q21234094818.332Q26387488187.332Q27652796561.335Q30513043447.332Q30995810034.332Q31634409088.335Q33672769595.332Q37716620446.332Q38243213001.332Q41165378730.332Q41742750395.332Q5270644893.332 Q5692202400.335 Q59578101107.334Q6191210037.332 Q62525676347.332Q63041590845.335Q63709884661.332Q65856189921.332Q67066825144.332Q67372356653.332Q68279191905.332Q8935136078.332 Q9646549417.332 00000[01F01m02T02U02V02W02X03C03j04V05705^05_06F06g06h06i07A07B07[07\09Z0:70<S0<m0?;0?<0?=0?>0?C0?N0?X0?Y0?Z0?e0?f0@D0@E0@c0@h0@i0@m0AB0AG0AL0AM0AN0CO0CT0Ce0DL0DM0FK0HN0J@0JI0JJ0JN0JO0JT0L90L:0L;0L<0Lf0Nh0PU0PZ0P^0P_0Pd0QG0QT0SY0T00Ua0V60V70Wd0We0Wf0Wg0Wh0Wi0Wn0XC0X_0Xc0YH0Yi0ZJ0Zk0\00\X0]90]Y0^:0_?0_`0`e0aF0bK0bl0cM0dR0eW0f\0g?0g`0hA0ha0if0ig0ja0jb0jc0jd0kQ0lI0m:0m;0m_0m`0nb0nc0o<10610710P10Q11N12S12T12U12V13:13X14214314m14n14o16117617h18B18^S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT2bs2D12FB3sp1FS2sp2PP3CRT2bs2FB3sp13SP1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT3BUF2bs3DXB2FB3sp1S1R4STKc4STKp5STKcp2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2bs4CRT02FB3sp1S1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFFS3CRTS2rc3Hr32KrS1R3HIA2hcFFS2rc3Hr32KrFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1SS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S3CRTFS2PPS2sp2PP3CRT2bs2FB3sp1S3CRTS3CRTFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS2rc3Hr31r2Kf1q1HS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2LF4LFB3FS2loFS3CRTS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9SFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes2csS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9S3CRTS2x0FS3CRTS2sp2PP3CRT2bs2D12FB3sp13D1u2rc3Hr3S2PP3CRT1x2HxS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE92p43Hp4S1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HP03HQ03HQES2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQEFSFFFS3CRTS2sp2PP3CRT2bs2FB3sp1S2sp2PP3CRT2lo2bs2FB3sp13SP1S2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp15nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3BUF2bs4LFB33LFB3DPB5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF3CRT3BUF2bs4LFB33LFB4DXBu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesFFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F85nodesFS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesFS2LF2bs4LFB33LFB2FB5nodesS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu5nodesFS2LF2bs4LFB33LFB2FB5nodesFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesFFFS2LF2sp2lo2bs4LFB33LFB3sp13SP15nodesS2LF2bs4LFB33LFB2FB5nodes1c2HcS2LF2bs4LFB33LFB3sp15nodesFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu5nodesFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPc5nodesS2LF2bs4LFB33LFB3sp15nodesS2LF2bs4LFB33LFB2FB2F05nodes". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIp FFRp CNTp STKp GPOL STKc1 STKcp PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIp_le FFRp_le CNTp_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_pol : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HZ HSUB KLOOP.
    dpose INV as (_ & _ & _ & _ & _ & XO0 & _). ddestruct XO0 as (_ & _ & _ & _ & _ & _ & XZ4 & _). ddestruct (XZ4 HZ) as (Z1 & Z2 & Z3 & Z4). clear XZ4.
    open_xinv INV hc.
    rewrite Z1, Z2, Z3 in XP.
    (* [comment removed for export] *)
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof (uwc_callee hc mg PRES HSc SAVE) as UWF.
    destruct (BUD_pre hc Lx bp q e9 PHIp FFRp HBUD HBP HQE ltac:(xl HE9 EX2) PHIp_le FFRp_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHc) as NDLx.
    assert (BINx : In (BUF, n) (Lx ++ LB)) by (apply in_app_iff; right; exact BIN).
    idtac "POL-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GPOL with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (CUR := CRT + 608) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                        (ct := x_pct X) (cpad := x_pcp X);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold SEQ_SIZE;
        first [ exact HHc | exact HK1 | exact XP | exact HPP | exact UWF | exact BPV | exact BPF | exact NDLx | exact BINx | exact I | eassumption | reflexivity
              | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "POL-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & h3 & rc & p4 & hct & hcpad & hcl & hcp & hcn & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HHD4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn. cbv beta in HEND.
    replace (ret_pc (Z_to_bv 64 0xaab88)) with (Z_to_bv 64 0xaab88 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold SEQ_SIZE in HP4.
    idtac "POL-BACK".
    xown_pres HP4 hc XO2.
    pres_call HP4.
    pose proof (BUD_post hc h3 Lx nodes bp q e9 PHIp FFRp CNTp HBUD HBP HQE ltac:(xl HE9 EX2) PHIp_le FFRp_le CNTp_le HV3 HFR3 HCNT3) as HBUD3.
    clear XO HHc HPP XP STlo SS1 MI.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc h3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, NC4.
    pose proof (xown_setpol asegs m4 (Lx ++ LB) ((SSEQ (rev nodes) ++ Lx) ++ LB) X hct hcpad hcl hcp (hd 0 nodes) nodes XO2
                  ltac:(intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb) HSUB eq_refl NC4) as XO3.
    pose proof (xblocks_setpol Lx X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 8) PERM Z4) as PERM3.
    clear XO2 PERM. unfold seq_cells in HHD4.
    idtac "POL-SWITCHED".
    fold_xinv_at INV2 m4 h3 (SSEQ (rev nodes) ++ Lx) (setpol X hct hcpad hcl hcp (hd 0 nodes) nodes (Z.lor (x_seen X) 8))
                 (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    assert (Hp4' : P <= p4 <= END) by (xl Hp4 HP0 HQ0 HQE HE9 EX1 EX2).
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "POL-OK".
      assert (Rc0 : rc = 0) by (clear - Kr Hr3; try kland Kr; rewrite ?Z.mod_small in Kr by lia; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite ?Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
      pose proof (HEND (or_introl Rc0)) as EP4. subst p4.
      eapply tail_walk with (q := e9) (p0 := p0) (bp := e9); first [ exact INV2 | exact KLOOP | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 | match goal with |- ?g => idtac "POL-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Kf; zify_cond Kf.
    { (* [comment removed for export] *)
      do 2 zstep.
      idtac "POL-ERR".
      eapply errj_walk with (p' := p4) (bp := e9); first [ exact INV2 | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 Hr3 | match goal with |- ?g => idtac "POL-ERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    assert (Rc8 : rc = -8320) by (clear - Kf Hr3; try kland Kf; change 18446744073709551615 with (Z.ones 64) in Kf; rewrite ?Z.land_ones in Kf by lia; Z.div_mod_to_equations; lia).
    pose proof (HEND (or_intror Rc8)) as EP4. subst p4.
    do 2 zstep.
    do 2 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    { idtac "POL-TOLERATED".
      eapply tail_walk with (q := e9) (p0 := p0) (bp := e9); first [ exact INV2 | exact KLOOP | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 | match goal with |- ?g => idtac "POL-TAIL2-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep.
    idtac "POL-CRITICAL".
    eapply errj_walk with (p' := e9) (bp := e9); first [ exact INV2 | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 Hr3 | match goal with |- ?g => idtac "POL-CRIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0290@D10821638613.340D12658412039.340D15946834553.290D24138570748.340D32456904529.340D3257379396.340 D35872675691.340D3881865400.340 D39246065128.340D52058619531.340D54252419555.340D59473897855.342D6191210037.340 D65415172059.290D68405377002.340D6910092783.340 D892632827.340  L1103920410.2   L11157644813.1  L11197191467.2  L11935817741.1  L12729978778.2  L14536640710.81 L14537371021.1  L1530387784.71  L15946752753.81 L16482024986.2  L17698511112.81 L19227461517.1  L19979573058.81 L20038394650.2  L20977711877.2  L21230010724.3  L22429105105.3  L22877147997.3  L23615739305.3  L23766154372.3  L23766154372.332L23800082620.81 L24882004373.71 L26375085850.2  L26494951359.2  L27111942217.1  L27394147279.3  L29680655011.1  L30507144274.2  L30997223346.3  L31862681339.81 L33947524594.83 L3482445079.81  L35655538583.72 L36252031629.1  L36872692637.2  L36968206175.2  L38235734261.1  L39360202971.81 L40228640085.0  L41755152410.2  L41922416647.81 L43739201421.1  L44015431570.351L44515277197.1  L45311526170.2  L45524555192.75 L46274998387.81 L52674297804.1  L53434713509.81 L55225352820.83 L57628700040.4  L58230853383.83 L58774595815.7  L60528857433.79 L61523197069.1  L62513011098.2  L63174242230.79 L63573689121.0  L64850595401.0  L65415221075.81 L65862516566.2  L67070089790.2  L8257818969.81  L9090702513.71  L9146166978.2   L9976516746.1   P1054078565.340 P1091485627.340 P12717575483.340P16486071483.340P18401496248.340P19971921516.340P20042703291.340P20983968178.340P22875669021.340P23093689016.340P26387488187.340P26650324920.340P30995810034.340P36862372138.340P3986716216.340 P41742750395.340P43683373752.340P45298862011.340P48381565112.340P51938201016.340P62525676347.340P65856189921.340P8687283256.340 P9156486261.340 Q1091485627.340 Q11201496749.340Q12717575483.340Q15985628819.342Q16486071483.340Q19548864598.340Q20042703291.340Q20983968178.340Q21234094818.340Q22875669021.340Q24858448058.282Q26387488187.340Q26507615518.340Q27382468681.340Q30513043447.340Q30995810034.340Q36862372138.340Q41742750395.340Q45298862011.340Q54678264090.282Q59578101107.342Q6191210037.340 Q62525676347.340Q65856189921.340Q67066825144.340Q68279191905.340Q8935136078.340 Q9156486261.340 Q9646549417.340 00000[01F01g02N03503603703803903d04K05705^06?06@06g06h06i06n06o07407507O07T07m08B08C0:A0:F0<T0<U0<V0<W0<b0<c0<m0=80=90=W0>50>60>70>;0><0>A0>B0>C0@D0BB0DE0F70F<0F=0FF0FJ0Go0H00H10HN0HS0I=0IB0IC0K00M20M60OR0P50PB0RG0R^0TO0TT0TU0VB0VC0VD0VY0VZ0V[0W30WO0WP0WT0X90XZ0Y;0Y\0Za0[I0[j0\J0\m0^20^S0_X0`90`Z0a_0b@0cE0cf0dk0f00fQ0g10h60hW0hX0i]0i^0i_0i`0jQ0jR0jS0kU0kV0lC0lD0mA0nF0o@0oA0oB0oC0oD10<10Z11411511612812j13D13E13aS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodesFFS3CRTFS3CRTFS2sp2PP3CRT2bs4CRT02FB3sp1S3CRTS2sp2PP3CRT2bs2FB3sp13SP1S2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFFS2rc3Hr32KrFS1R3HIA2hcS2rc3Hr32KrFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FFS2PPFS3CRTFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS3CRTFS2LF4LFB3S2loS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9SFS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp15nodes2csS3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e93HE9S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2x0S1R4STKc4STKk5STKck2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S2sp2PP3CRT2bs2D12FB3sp13D1u2rc3Hr3S2PP3CRT1x2HxS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE92p43Hp4S1R2PP3CRT2lo2FB2x03APXS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HP03HQ03HQES3CRTFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESSS2sp2PP3CRT2bs2FB3sp1FFS2sp2PP3CRT2bs2D12FB3sp1S2sp2PP3CRT2lo2bs2FB3sp13SP1FS2x0S2LF2PP2lo2bs4LFB33LFB4PPLO3sp15nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS2LF3CRT3BUF2bs4LFB33LFB4DXBu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3BUF2bs4LFB33LFB3DPB5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF2PP3CRT2bs4LFB33LFB3D1u5nodesS2LF2PP2bs4LFB33LFB2FB3APP5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS2LF3CRT2bs4LFB33LFB2FB3APC5nodesFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F85nodesFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu5nodesS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu5nodesFFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FB5nodes1c2HcS2LF2bs4LFB33LFB3sp15nodesFFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu5nodesS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2hc3HSc5HTOPc5nodesS2LF2bs4LFB33LFB3sp15nodesFS2LF2bs4LFB33LFB2FB2F05nodes". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG HMND PHIk FFRk CNTk STKk AKID STKc1 STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma arm_akid : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP HZ HSUB KLOOP.
    dpose INV as (_ & _ & _ & _ & _ & XO0 & _). ddestruct XO0 as (_ & _ & _ & _ & _ & XZ4 & _). ddestruct (XZ4 HZ) as (Z1 & Z2 & Z3 & Z4). clear XZ4.
    open_xinv INV hc.
    rewrite Z1, Z2, Z3 in XA.
    (* [comment removed for export] *)
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof (uwc_callee hc mg PRES HSc SAVE) as UWF.
    destruct (BUD_pre hc Lx bp q e9 PHIk FFRk HBUD HBP HQE ltac:(xl HE9 EX2) PHIk_le FFRk_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHc) as NDLx.
    assert (BINx : In (BUF, n) (Lx ++ LB)) by (apply in_app_iff; right; exact BIN).
    idtac "AKID-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply AKID with (h := hc) (LB := Lx ++ LB) (LF := LF') (PP := PP) (AK := CRT + 504) (P := q) (END := e9) (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                        (k1 := x_a1 X) (k2 := x_a2 X) (k3 := x_a3 X) (k4 := x_a4 X) (ct := x_act X) (cpad := x_acp X) (r1 := x_r1 X) (r2 := x_r2 X) (r3 := x_r3 X) (r4 := x_r4 X);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold SEQ_SIZE;
        first [ exact HHc | exact HK1 | exact XA | exact HPP | exact UWF | exact BPV | exact BPF | exact NDLx | exact BINx | exact I | eassumption | reflexivity
              | xside HP0 HQ0 HQE HE9 EX1 EX2
              | match goal with |- ?g => idtac "AKID-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & h3 & rc & p4 & ka1 & ka2 & ka3 & ka4 & hct & hcpad & hcl & hcp & hcn & kr1 & kr2 & kr3 & kr4 & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HHD4 & HCB4 & ECN & NC4 & ND4 & APN4 & HH4 & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0 hcn. cbv beta in HEND.
    replace (ret_pc (Z_to_bv 64 0xaaae4)) with (Z_to_bv 64 0xaaae4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold SEQ_SIZE in HP4.
    idtac "AKID-BACK".
    xown_pres HP4 hc XO2.
    pres_call HP4.
    pose proof (BUD_post hc h3 Lx nodes bp q e9 PHIk FFRk CNTk HBUD HBP HQE ltac:(xl HE9 EX2) PHIk_le FFRk_le CNTk_le HV3 HFR3 HCNT3) as HBUD3.
    clear XO HHc HPP XA STlo SS1 MI.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc h3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, NC4.
    pose proof (xown_setakid asegs m4 (Lx ++ LB) ((SSEQ (rev nodes) ++ Lx) ++ LB) X ka1 ka2 ka3 ka4 hct hcpad hcl hcp (hd 0 nodes) nodes kr1 kr2 kr3 kr4 XO2
                  ltac:(intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb) HSUB eq_refl NC4) as XO3.
    pose proof (xblocks_setakid Lx X ka1 ka2 ka3 ka4 hct hcpad hcl hcp (hd 0 nodes) nodes kr1 kr2 kr3 kr4 (Z.lor (x_seen X) 1) PERM Z4) as PERM3.
    clear XO2 PERM. unfold CrtExtStmts.akid_cells, seq_cells in HHD4; cbn [app] in HHD4.
    idtac "AKID-SWITCHED".
    fold_xinv_at INV2 m4 h3 (SSEQ (rev nodes) ++ Lx) (setakid X ka1 ka2 ka3 ka4 hct hcpad hcl hcp (hd 0 nodes) nodes kr1 kr2 kr3 kr4 (Z.lor (x_seen X) 1))
                 (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb.
    assert (Hp4' : P <= p4 <= END) by (xl Hp4 HP0 HQ0 HQE HE9 EX1 EX2).
    (* [comment removed for export] *)
    do 2 zstep. if_cases Kr; zify_cond Kr.
    { idtac "AKID-OK".
      assert (Rc0 : rc = 0) by (clear - Kr Hr3; try kland Kr; rewrite ?Z.mod_small in Kr by lia; change 18446744073709551615 with (Z.ones 64) in Kr; rewrite ?Z.land_ones in Kr by lia; Z.div_mod_to_equations; lia).
      pose proof (HEND Rc0) as EP4. subst p4.
      eapply tail_walk with (q := e9) (p0 := p0) (bp := e9); first [ exact INV2 | exact KLOOP | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 | match goal with |- ?g => idtac "AKID-TAIL-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    idtac "AKID-ERR".
    eapply errj_walk with (p' := p4) (bp := e9); first [ exact INV2 | exact HBUD3 | eassumption | xl HP0 HQ0 HQE HE9 EX1 EX2 Hr3 | match goal with |- ?g => idtac "AKID-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Loop.
  End Body.
  End Call.
End Walk.
