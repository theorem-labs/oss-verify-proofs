(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse P_x509_crt_ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo
     A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_seq_stmtsE A_x509_get_san_A A_x509_crt_ext_stmt A_x509_crt_ext_A
     A_asn1_get_bool A_oid_x509_ext A_x509_get_ext_A A_x509_basic_A A_x509_key_usage_A A_x509_skid_A A_x509_ns_cert_type_A A_x509_crt_ext_area A_x509_crt_ext_B A_x509_crt_ext_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
  Hypothesis SM2 : arl_smalloc R 2 = 0x52c88.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.
  Hypothesis AMS : arl_amemset R = 0x67ce4.
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
  Hypothesis SEQOF : seq_parser_stmtE asegs R HIA PHIq FFRq CNTq STKq (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0) 0x9a3f8.
  Hypothesis GSAN : seq_parser_stmtE asegs R HIA PHIs FFRs CNTs STKs (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0) 0xae3f0.
  Hypothesis GPOL : seq_parser_stmtE asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 4) (fun _ => True) (fun r => r = 0 \/ r = -8320) 0xab024.
  Hypothesis AKID : x509_akid_stmtE asegs R HIA PHIk FFRk CNTk STKk (LFMAX_CRT + 4) 0xaac4c.
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
  Hypothesis SP1 : bv_unsigned sp - 336 <= sp1 <= bv_unsigned sp - 320.
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
  Local Notation RSLK k16 ja jb :=
    [CB 16 ja; C8 k16; C8 (Z_to_bv 64 (CRT + 672)); C8 (Z_to_bv 64 18446744073709542042); C8 (Z_to_bv 64 (CRT + 648));
     C8 (Z_to_bv 64 (CRT + 644)); C8 (Z_to_bv 64 (CRT + 656)); C8 (Z_to_bv 64 (CRT + 688)); C8 (Z_to_bv 64 (CRT + 652));
     C8 (Z_to_bv 64 (CRT + 480)); C8 (Z_to_bv 64 (CRT + 504)); C8 (Z_to_bv 64 (CRT + 448)); C8 (Z_to_bv 64 (CRT + 608));
     C8 (Z_to_bv 64 2048); C8 (Z_to_bv 64 (CRT + 640)); C8 a4e; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (FB + 32));
     C8 (Z_to_bv 64 ENDX); C8 (Z_to_bv 64 (FB + 72)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (FB + 144));
     C8 (Z_to_bv 64 (FB + 128)); CB 16 jb; C8 (Z_to_bv 64 FB)].
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
    /\ rw_cells asegs mm sp1 (RSLK k16 ja jb)
    /\ stk asegs mm (sp1 + 216) (bv_unsigned sp + -104) /\ stk asegs mm lo sp1 /\ mem_inv asegs mm /\ bytes_at asegs mm BUF bs
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
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4v s10v x28 x29 x30 x31 : word),
      xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p)] ->
      BUD hc Lx p ->
      aevtA asegs (KF asegs R HIA hc mo0) POST
        (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (FB + 64)) x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v (Z_to_bv 64 ENDX) (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                 (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (FB + 32)) s10v (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
            F (Z_to_bv 64 0x0aa0dc) fc None mm (seg_rom asegs)).


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
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v s5v s6v s8v s9v s10v s11v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END -> -2^31 < r <= 0 ->
    BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v (Z_to_bv 64 r) s5v s6v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s8v s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa4d8) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.errj_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.errj_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.errj_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma tail_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v s9v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) s9v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa2c4) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa3a0) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa3e8) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa314) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa3b8) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa400) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa3d0) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa330) fc None mm (seg_rom asegs)).
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
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa294) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_ext_C.arm_akid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_C.arm_akid with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_C.arm_akid ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@D28498761192.285D4451634193.285 D60109196847.285K10093203181.285K17397425005.285K23551032557.285K2431698795.285 K30840574317.285K37953334125.285K44164039966.285K49978975725.285K52576198765.285K60822670701.285K9136277101.285 K9840090748.285 L10091109645.2  L1685717371.0   L17382748301.2  L23182876091.2  L23540543245.2  L2419170461.2   L24882004373.71 L27111942217.1  L29680655011.1  L30851056269.2  L35655538583.72 L37963823245.2  L38235734261.1  L41202929119.273L44168742175.3  L47042279518.81 L49964299789.2  L52565717901.2  L53271535775.273L54261998223.2  L60828966541.2  L63174241565.81 L64850595401.0  L9090702513.71  L9134183821.2   L9835808138.2   P23170010975.285P54268551240.285Q10649498890.282Q10651748618.281Q13733106231.281Q17701933584.282Q28496781288.284Q28498761192.285Q37216054521.282Q39600066516.282Q40916972731.282Q42439443119.285Q4451634193.285 Q4453582353.284 Q45353769141.281Q49746415830.285Q60529412798.285Q61556549392.283Q61847600945.282Q67038978349.285Q68013150533.285Q8699115497.285 00000c01V02R03?03l04Y05E06206_07L08908f09S0:@0:l0:m0:n0:o0;00;10;20;P0;T0;Y0;Z0=L0=M0=Q0>20>30?`0?a0?b0@C0@D0@E0B20B30BO0BP0BQ0CW0De0E80EK0E^0F10FV0G;0GU0GV0GW0HG0Hl0IQ0Id0Jb0Jc0K?0L90MF0N:0O@S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPB2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stFSFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTFS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HQE3HBPFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2e92HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3PP02HBFFS1R2LF2PP3slo2bs4LFB33LFB4SLOS2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2PP2bs4LFB33LFB3TOP3sp12e95HTOPc2HB5Ha_st5Hl_stFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2e92HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs4LFB33LFB3TOP3sp13SP12e95HTOPc2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma skip_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa21c) fc None mm (seg_rom asegs)).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L13527335811.83 L24882004373.71 L27111942217.1  L2732059965.83  L29680655011.1  L32361667354.270L35655538583.72 L38235734261.1  L49334198535.83 L64850595401.0  L9090702513.71  Q13546762522.278Q27663295649.278Q31632298672.278Q44341577914.27800002502S02W02l03103R05D05H07M07N07j08b09509H0:5S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS2sp2PP3CRT2bs2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2loS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPSS2sp2PP3CRT2lo2bs2FB3sp13SP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPc". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma default_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa42c) fc None mm (seg_rom asegs)).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@D28498761192.285D4451634193.285 D60109196847.285K10093203181.285K17397425005.285K23551032557.285K2431698795.285 K30840574317.285K37953334125.285K44164039966.285K49978975725.285K52576198765.285K60822670701.285K9136277101.285 K9840090748.285 L10091109645.2  L13527335811.83 L15902870269.83 L1685717371.0   L17382748301.2  L23182876091.2  L23540543245.2  L2419170461.2   L24882004373.71 L27111942217.1  L29680655011.1  L30851056269.2  L32361667354.273L33947518423.83 L35655538583.72 L37963823245.2  L38235734261.1  L41202929119.273L44168742175.3  L47042279518.81 L49964299789.2  L52565717901.2  L53271535775.273L54261998223.2  L60828966541.2  L63174241565.81 L64850595401.0  L9090702513.71  L9134183821.2   L9835808138.2   P23170010975.285P54268551240.285Q10649498890.282Q10651748618.281Q13549040546.281Q13733106231.281Q17701933584.282Q27652695577.281Q28496781288.284Q28498761192.285Q31633985544.281Q37216054521.282Q39600066516.282Q40916972731.282Q42439443119.285Q44326455810.281Q4451634193.285 Q4453582353.284 Q45353769141.281Q49746415830.285Q60529412798.285Q61556549392.283Q61847600945.282Q67038978349.285Q68013150533.285Q8699115497.285 00000c01V02R03?03l04Y05E06206_07L08908f09S0:@0:l0:m0=20=G0=H0=I0=J0=K0=L0=j0=n0>30>40>U0@Z0BL0BM0BQ0C20C30D`0Da0Db0EC0ED0EE0G20G30GO0GP0GQ0HW0Ie0J80JK0KC0KV0Ki0L<0La0MF0MY0N30N40N50Ne0OR0P70P\0Po0Qm0Qn0RJ0SD0TQ0UE0VKS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPB2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2e92HB5Ha_st5Hl_stFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2sp2PP3CRT2bs2FB3sp1SFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2PPS3CRTFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2bp2e93HQE3HBPFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02e93HQ03HQESS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2e92HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFB3PP02HBFFS1R2LF2PP3slo2bs4LFB33LFB4SLOS2e92HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2e92HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2PP2bs4LFB33LFB3TOP3sp12e95HTOPc2HB5Ha_st5Hl_stFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2e92HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2e92HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3slo2bs4LFB33LFB3TOP3sp13SP12e95HTOPc2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH LOS SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma unknown_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa2ac) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 5 zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "07M0@D16464982057.290D54752915971.290D60109196847.290K12226132804.290K21870859916.290K22945712379.290K44164039966.290L11390588661.295L11404653746.295L12219836580.2  L12365671214.295L12382995637.295L12408374717.1  L13433771118.295L13527335811.83 L14447004729.2  L14499315374.295L14732077592.0  L15100179189.295L15489369424.2  L15563204590.295L15613930590.1  L16158308341.295L16640213038.295L1685717371.0   L17706150254.295L18769531822.295L18877703477.295L1930573885.1   L19716667709.1  L19835534574.295L20904207662.295L21605962613.295L2166507061.295 L21866712442.2  L21968113262.295L22941438733.2  L23033587886.295L23710501914.276L24061693967.278L24326341301.295L24750577586.295L24882004373.71 L25325059957.295L25979698165.295L27111942217.1  L27220613693.1  L28035935925.295L28700010805.295L29680655011.1  L29695142424.0  L30252456425.276L30252456425.278L3137102497.0   L31762047794.295L31811310069.295L34224753458.295L34531233589.295L34927381870.295L35203697589.295L35497694602.3  L35655538583.72 L35993319342.295L37056696558.295L37631907489.0  L37744465018.275L38122699054.295L38235734261.1  L38921746357.295L40255278254.295L41320756718.295L41633670645.295L42380467758.295L43446388590.295L44168742175.3  L44353540917.295L44510814638.295L44598345021.83 L45411141685.295L45572442045.1  L45578914542.295L4575410798.295 L47706788769.0  L48139454069.295L48387988182.2  L4894766197.295 L49138168885.295L49334198535.83 L50856703413.295L51857498741.295L52067440306.286L52298219197.1  L52385715068.1  L54568980917.295L54685946034.295L58344801525.295L58542442990.295L59109295640.0  L5941946741.295 L59607921198.295L59978813757.1  L60667632494.295L61064737333.295L61639115041.0  L61733553582.295L6269429426.295 L62797983470.295L63164974909.1  L63792455797.295L63866083118.295L64850595401.0  L64931623022.295L65995528878.295L67072525294.295L68138462254.295L68166715637.295L7369768728.0   L7421422752.2   L7736014575.2   L8670206133.295 L9090702513.71  L9636196114.10  L9671529845.295 P14461423358.290P7750690063.290 Q10133300851.294Q10202675027.294Q10239123748.294Q10456093695.294Q10468039550.294Q1047666609.294 Q10631183217.294Q10657618686.294Q1069447827.294 Q11307468516.294Q11519723711.294Q11534315582.294Q11707387953.294Q11721274302.294Q12365563379.294Q12371132324.294Q1249392519.294 Q12554004252.295Q12586004095.294Q12597946878.294Q12798011774.294Q12819673373.294Q13433420467.294Q13657902782.294Q13662209855.294Q13863996990.294Q13883823837.294Q14331894308.294Q14499663987.294Q14723654782.294Q14726397183.294Q14927652862.294Q14951649181.294Q15272553543.294Q15425851539.294Q15563295027.294Q15615935677.284Q15792117183.294Q1597190259.294 Q15993904318.294Q16017925469.294Q16338797831.294Q16464982057.290Q16640061171.294Q17015192447.294Q17061753470.294Q17081817629.294Q17402460871.294Q17705781171.294Q18125908798.294Q18147570653.294Q183639751.294  Q18470802311.294Q18769968499.294Q19191628030.294Q19224307869.294Q19481414227.294Q19502301075.294Q19536791879.294Q19576760198.284Q19835687475.294Q20287934045.294Q20600450567.294Q20904037363.294Q2113418609.294 Q21354211101.294Q21656387454.294Q21666695111.294Q21967691955.294Q22014231475.294Q22422035677.294Q22726163591.294Q23033939571.294Q23079991667.294Q2313284935.294 Q23136260739.289Q23590189681.294Q23790309959.294Q24103854931.294Q24156724787.294Q24654336817.294Q24856038151.294Q2516139692.284 Q25220380659.294Q25330663076.294Q25711909118.294Q25720064241.294Q25924411591.294Q26286632115.294Q26396382308.294Q26623197630.294Q2662918451.294 Q26788438449.294Q27354710643.294Q27460537636.294Q27687380862.294Q2768998628.294 Q28420471603.294Q28526289636.294Q28743259327.294Q28755205182.294Q28815276582.284Q28918348849.294Q28974276947.294Q29484617971.294Q29594639268.294Q29806889599.294Q29821482494.294Q29994554865.294Q30544054707.294Q30658294116.294Q30873166655.294Q30885112510.294Q31060806321.294Q31242882857.289Q31610335091.294Q31724541476.294Q3177310769.294 Q31945064574.294Q31949379839.294Q32124461169.294Q32151159806.294Q32673956915.294Q32784240612.294Q33010825534.294Q33013559743.294Q33192810801.294Q33214822590.294Q33219100935.294Q33629016531.294Q3379528199.294 Q33849992356.294Q33948699352.286Q33948765052.284Q33951215832.285Q33951215832.287Q33997911443.294Q34074975998.294Q34079283071.294Q34258566897.294Q34281070206.294Q34914146916.294Q34927223731.294Q35140728766.294Q35147631679.294Q35239973971.294Q35348920126.294Q35368984541.294Q35704961724.295Q35981996836.294Q35992951155.294Q36044430547.294Q36209077630.294Q36213384703.294Q36308855059.294Q36413074686.294Q36434736285.294Q37057134131.294Q3727068915.294 Q37272699454.294Q37277539007.294Q37478794686.294Q37511473757.294Q37596097811.294Q38122854387.294Q38336999551.294Q3836823972.294 Q38538787710.294Q38887613383.294Q39305383443.294Q39402989887.294Q39604506686.294Q39621797959.286Q39621863907.284Q39641381085.294Q39953864839.294Q40254857843.294Q4063929342.294 Q40668662270.294Q40709198237.294Q41013329479.294Q41321110323.294Q41736515262.294Q41773381469.294Q42077476615.294Q42380570867.294Q4243555313.294 Q42439443119.290Q42667631635.294Q42802758782.294Q42839108637.294Q43143204039.294Q43171129523.294Q43446561203.294Q43899061725.294Q43947429459.294Q44211578247.294Q44510711667.294Q4455037725.294 Q44964821661.294Q45277305671.294Q45578560563.294Q45641877299.294Q4575040691.294 Q46028968029.294Q46341484551.294Q46454566351.286Q46454631531.284Q46638274963.294Q46707637491.294Q47205511665.294Q47417698759.294Q47771784627.294Q47881805156.294Q4792821683.294 Q48281720497.294Q48483946119.294Q48831220595.294Q48899876819.294Q4903104356.294 Q49347972209.294Q49698585326.288Q49746415830.290Q49897496627.294Q50011712484.294Q50187123667.294Q50232231230.294Q50411627825.294Q50548298899.294Q50961127923.294Q51071402148.294Q5127559358.294 Q51297991422.294Q51479976689.294Q51798994259.294Q52029505203.294Q52137158244.294Q52362138558.294Q52366452799.294Q52545729457.294Q52879536915.294Q528816819.294  Q5303023793.294 Q53095224435.294Q53201313572.294Q53427865982.294Q53434794495.294Q53609621873.294Q53971975064.294Q54159379763.294Q54259691283.294Q54269162724.294Q54496243262.294Q54500550335.294Q54675869233.294Q54700237246.294Q54752915971.290Q55225131763.294Q55335415204.294Q55559866366.294Q55564704895.294Q55735330801.294Q55861997779.294Q5589485587.294 Q5597152147.294 Q56399037284.294Q56624166207.294Q56626150590.294Q56799485105.294Q56825953342.294Q57475807268.294Q57690155775.294Q57702355582.294Q57891673598.294Q57928547741.294Q58541527524.294Q58542024499.294Q5869559155.294 Q58754302911.294Q58768345918.294Q58955827902.294Q58996364125.294Q59011533944.285Q59011533944.287Q59608276211.294Q59662173907.294Q5966726180.294 Q59820063103.294Q60023677054.294Q60060518429.294Q60151466067.294Q60667737523.294Q60668400038.284Q60888407615.294Q61089929534.294Q61126271453.294Q61430366599.294Q61733727091.294Q6191855359.294 Q6193839742.294 Q61952063487.294Q62153588478.294Q62186227357.294Q62467997553.294Q62498744135.294Q62797873203.294Q63197552275.294Q63230318526.294Q63251987549.294Q63564471303.294Q6367174257.294 Q63865731571.294Q64296308094.294Q64316134685.294Q64628651463.294Q64931978931.294Q6530428934.284 Q65359962686.294Q65383959261.294Q65704864391.294Q65995633779.294Q66450236317.294Q66771107911.294Q67038978349.290Q67072372019.294Q67514128733.294Q6769594904.287 Q68013150533.290Q68138091251.294Q68184663539.294Q68579884573.294Q6933213747.294 Q6999000954.285 Q6999000954.287 Q7043497444.294 Q716645843.294  Q7257845695.294 Q7270045502.294 Q727190035.294  Q7432927025.294 Q7999466483.294 Q8100524755.294 Q8109216420.294 Q8321992063.294 Q8336035070.294 Q8501275889.294 Q8699115497.290 Q9173370980.294 Q9387751999.294 Q9400214974.294 Q9566995889.294 Q9591366974.294 00000e01Z02X03G04604e05V06706X06Y07:07[07`08A0:F0:G0:h0:i0;J0;P0<10<60<W0=80=90=Z0>;0>\0>a0>f0?G0?h0@I0@j0@k0AL0AM0An0BO0C00CQ0D20DP0E10ER0EV0E[0F<0F]0Fb0Fc0GD0Ge0Gf0HG0Hh0II0Ij0JK0Jl0Jm0L_0M@0Ma0Mb0O<0O]0Oa0PB0Pc0QD0Qe0RF0Rg0Rh0SI0Sj0T?0T`0Te0UF0Ug0Uh0VI0VP0W10WR0YW0Z80ZY0ZZ0Z_0Zd0[E0[f0\G0\h0\i0]J0]k0^00^Q0_20_30_T0`50`V0`[0a<0a]0a^0b?0b`0cA0cb0dC0dD0dK0dL0dm0eI0e\0f=0gP0h[0h\0i30i40i50i60i70i80i90iP0iQ0iR0iS0iT0iU0ie0if0j=0k50k60k70k80k90kI0kJ0kK0kL0kM0kN0k^0k_0k`0ka0kb0l90lP0l`0m30m40m50m60m70mN0n60nF0nG0nH0nI0n`0o00o10o20oI0o`10010110210I10`11711o12?12@12W12g12h12i12j13A13Q13R13S13j14:14;14R15:15;15R15i15j15k16B16U16V16W16X16Y17017117217317417517617717817917:17;17<17=17j17k18B18C18D18E18F18G18H18I18J18K18L19419519619719819919:19;19<19=19>19?19@19A19X19o1:F1:G1:[1:o1;C1;W1;n1;o1<01<11<21<31<C1<D1<E1<\1<]1<^1=K1=L1=\1>31>41>51>L1>M1>N1>^1>_1>`1>a1>b1>c1?:1?J1?K1?L1?M1?d1@;1@<1@=1@Q1@e1@f1A=1AM1AN1AO1AP1Ag1B71B81B91BP1B`1Ba1CT1Ck1Cl1Cm1DD1DE1DU1DV1Dm1ED1ET1EU1EV1Em1F=1F>1FN1FO1Ff1G:1GN1Ge1Gf1Gg1H>1H?1H@1HA1HB1HY1HZ1I11I21I31IP1JQ1JR1JS1Jj1Jk1Jl1KC1KD1KE1KF1KG1KH1K_1K`1Ka1Kb1Kc1Kd1L;1L<1L=1L>1L?1L@1LA1LB1LZ1L[1M21M31M41M51M61M71M_1M`1Ma1Mb1Mc1Md1N;1NR1Ni1Nj1Nk1Nl1Nm1Nn1No1O01O11O21O31O41OD1OE1OF1OG1OH1OI1PC1Q=1QM1Qd1Qe1Qf1Qg1Qh1R?1RO1S<1S=1S>1S?1SV1Sf1Sg1Sh1Si1Sj1Sk1Sl1TC1TS1Tj1Tk1Tl1UC1UD1UT1UU1UV1Um1V=1W51W61W71WN1W^1W_1X61YF1YV1YW1Z31Zi1[91[:1[;1[<1[P1[d1[e1\<1\=1\>1\U1\V1\W1\n1\o1]01]11]21^;1^<1^=1^>1^?1^@S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11X2et2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11X2et2HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp11X2et2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u1X2et2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC1X2et2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC1X2et2HB5Ha_st5Hl_stS2LF3CRT3BUF2bs4LFB33LFB4DXBu1X2et2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1b2HbS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2PPS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2loS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2bs2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2et2HUS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e93HP03HQ03HQE3HE93HBPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS3CRTS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2b02HbFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT2lo2bs2FB3sp13SP1S2et2UR1r2KT1q1H2H0S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu1X2et2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOu1X2et2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB4IMG'FFFFFFS1R2LF2bs4LFB33LFB4IMG'FFFFFS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFFFS2LF2bs4LFB33LFBFFFFFS2LF2bs4LFB33LFBFFFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBS2LF2bs4LFB33LFB2FBFFFFS1R2LF2bs4LFB33LFB4IMG'S2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFB2FBFFFFS1R2LF2bs4LFB33LFB4IMG'FFFFFFFFFFFFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS1R2LF2bs4LFB33LFB4IMG'FFFFFFFFFFS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stFFFFFFFFFFFFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFFFS2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'FFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFS2LF2bs4LFB33LFBFFFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF3CRT3slo2bs4LFB33LFB4SLOS1X2et2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'FS1R2LF2bs4LFB33LFB4IMG'FFS2LF3CRT2bs4LFB33LFB2HB5Ha_stS1R3HIA1h2LF2sp3CRT2bs4LFB33LFB3TOP3sp11X2et5HTOPc2HB5Ha_st5Hl_stFFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFFFFS1R2LF2bs4LFB33LFB4IMG'FFFFFS1R2LF2bs4LFB33LFB4IMG'FFFFFFFS1R2LF2bs4LFB33LFB5ALWF'FS1R2LF2bs4LFB33LFB4IMG'FFFFFS2LF3CRT2bs4LFB33LFB1X2et2HB5Ha_st5Hl_stFFFFFS1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'S1R2LF2bs4LFB33LFB4IMG'FFFFFFFFFFFS2LF2bs4LFB33LFBFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFFFFFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FS2LF2bs4LFB33LFBFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS1R2LF2bs4LFB33LFB4IMG'S2LF2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3LOS3sp13SP14SLOu1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBFS2LF3CRT2bs4LFB33LFB4CRT02HBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB1X2et2HB5Ha_st5Hl_stS2LF2bs4LFB33LFBFFFS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFS1R2LF2bs4LFB33LFB4IMG'FFFFS1R3HIA1h2LF2sp3CRT3slo2bs4LFB33LFB3TOP3sp13SP11X2et5HTOPc2HB5Ha_st5Hl_stFFFFF". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma dispatch_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa22c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQE HE9 HBUD HBP KLOOP.
    pose proof INV as INV0.
    open_xinv_mu INV hc.
    pose proof (bv_unsigned_in_range 64 (sx32 et)) as UR. unfold bv_modulus in UR. cbn [Z.pow Z.of_N Pos.pow] in UR.
    pose proof (bv_unsigned_in_range 64 (sx32 (x_et X))) as ER. unfold bv_modulus in ER. cbn [Z.pow Z.of_N Pos.pow] in ER.
    assert (OET : aobj asegs AL (hcs asegs R HIA hc) mm (CRT + 640) 8) by (eapply aobj_sub; [exact OEXT| clear; lia| clear; lia]).
    (* [comment removed for export] *)
    do 9 zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L14406737544.205L19246787633.2  L40228640085.0  L51907746211.2  L64412859763.2  00000100200300:00AFSSS2rg2RRS2rg2RR". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 DIMG STKc1 PHIx_mono FFRx_mono CNTx_mono LFB3 PP0 CWP PPLO BIN B1 B2 B3 B47 B30 DPB CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPH SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma err_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd olen op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (rg p' bp : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4v s5v s9v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
    -0x7f < rg < 0 -> BUD hc Lx bp -> P <= bp <= END ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) s4v s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) s9v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa4a4) fc None mm (seg_rom asegs)).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "03:0@C17025492443.313C65802607699.314D27847976046.314D47770555849.314D47776798540.292D54661255290.292D55639571502.292D55641685675.314D60109446735.314D60128441358.314D61543520757.292D61549796208.314K14848440079.313K25709469327.313K30222305807.313K33779218703.313K40145229071.313K45693719410.314K5284942906.314 K54542738319.313K55499728911.313K63014653711.313K8693187983.313 L11845198509.3  L12252132089.3  L13176305223.2  L13947844548.3  L14313191351.1  L14358424541.3  L14861253785.2  L15340755406.78 L15618147883.1  L16772787627.1  L17605243636.86 L18966192929.0  L19103996075.1  L19566614582.86 L19964894411.86 L21218866939.2  L21619350327.1  L22212138180.3  L23710709032.1  L24139200548.300L24796913220.3  L24882004373.71 L25713366297.2  L26393260740.86 L27111942217.1  L27789073007.1  L28931833527.1  L29407717531.1  L29680655011.1  L30226661785.2  L30747922934.5  L31374222260.86 L32866598340.3  L33239412785.3  L33308163853.86 L33740837294.0  L33783050905.2  L3480350366.86  L35655538583.72 L36463206329.4  L37605408727.73 L38235734261.1  L39478371757.86 L40132288153.2  L41122741931.1  L41409160545.3  L41832806413.86 L42419476660.1  L4370579368.1   L43927446468.3  L45689297124.2  L46059794920.1  L47289743172.3  L47348680317.2  L4872004339.2   L48843152936.1  L49207136770.3  L49339385823.86 L52941874306.3  L5297692588.3   L53266624065.86 L54410352043.1  L54555682841.2  L55085943702.3  L55512605593.2  L56157302580.86 L57394714052.3  L57757144503.1  L57850745591.1  L58678780634.6  L59003401692.86 L59308586248.2  L59967748674.3  L60056205954.3  L63001773209.2  L64686745924.3  L64850595401.0  L65642230468.3  L66925110933.285L8705412633.2   L881835912.0    L9090702513.71  L9476387309.86  L9644563342.71  N13257356329.314N20884620581.314N22787815853.314N35806358206.314N49089372318.314N64789588100.314O12233548996.313O1358745554.314 O13649862898.314O1401750750.312 O14175554244.313O1478916974.314 O16961596029.313O17025492443.313O20169458429.313O20458779460.313O22479346685.313O23601537266.314O24352547140.313O26475597711.314O27265912465.314O33870522200.314O34052634180.313O39013788797.313O41306367357.313O42395367124.313O43849271089.314O44531015165.313O44879841026.314O45696702077.313O45947445700.313O47737000900.313O47972003709.313O50689527441.314O50702732434.313O51150049554.313O53449798340.313O56414299794.313O57957320900.313O59625529265.313O65672115325.313P11860422666.313P12257878110.314P13953656163.313P21212095580.313P22197995107.313P24812063971.313P30744236914.314P32881815395.313P33249419926.312P36465839390.314P41419110342.313P43934249315.313P47284020707.313P47359677658.314P4875970917.314 P49191944357.313P52940256805.313P55088519473.314P57379456867.313P58674176094.314P59973560549.314P60050384933.313P64680999907.313P65640603747.313Q11148838878.314Q1510474216.310 Q15605927357.314Q15766564435.314Q16670484879.314Q17372565576.310Q19561449455.285Q19576678430.285Q26318654066.314Q28815390142.285Q31124869336.314Q32681607669.314Q34363165844.314Q34671225381.285Q34964382778.314Q42439168719.314Q47061991091.314Q48118064779.314Q48360113622.314Q49746198710.314Q51518068631.314Q543084191.314  Q58496806552.314Q62380812747.314Q67038703949.314Q7757734246.285 Q8699324297.314 Q9356559679.292 Q9633967632.285 Q9644583048.314 00000100501O01P01Q02<02=02>03203]04H05305X06=06b07G07l08P09109V0:;0:`0;E0;F0;G0;O0;P0;T0;_0;`0=P0=T0=X0?V0?W0?[0BR0D`0Da0De0Df0Dj0Dk0Dl0EJ0EK0FS0FW0F[0F\0F`0Fe0Ff0Fg0IB0IC0ID0I\0I]0I^0K^0MP0MQ0N90N=0NZ0N[0N_0N`0O80O<0O@0OA0OB0OF0OG0OH0OI0OM0ON0QT0QU0QV0Qk0Qo0R00R10R20T00T10T50T90T:0VE0VK0VL0VM0VN0VO0VP0VQ0W<0W=0W>0WZ0X70XO0Y20Y`0ZG0[@0[A0[d0[e0[f0[g0[h0[i0[j0[k0[l0[m0[n0[o0\00\10\20\30\40\50\60\70\80\90\:0\;0\<0\=0\>0\?0\@0\A0\B0\C0\D0\E0\F0\G0]00]Y0^E0^F0_20_^0aQ0b=0cC0cj0dS0e?0ek0g10go0hX0iA0ii0jU0k\0lE0ln0mZ0nF0nG0oI0of10M10N11E12:13<13d14[14\14]14^15;16916^16_17]18E19819919V1:31:X1;Z1<71=21=U1>51>UFS2FBS1R3HIA1h2LF2sp2PP3CRT3BUF2lo2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc2OL2OP3HTcFFS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPFFS1R2LF2sp2PP3CRT3BUF2lo2bs4LFB33LFB3LOS2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF2PP3BUF2bs4LFB33LFB2FB3APP2OL2OPS2LF3BUF2bs4LFB33LFB2FB3APB2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPS2LF3CRT3BUF2bs4LFB33LFB2FB3APC2OL2OPFFS2lo3sp1FS2FBS2sp2lo3sp1FS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22OL2OP2e93HE94HOP2S2FBS2FBS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9SS2FBS1R2sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13APP3APC5BUFLO3SPR3ALO2F02F14FBLO3APB6CRTLOu3D1u4DXBu4SP1R4ENDX3EX22OL2OP1q2p02e93HP03HQ03HQE3HE94HOP2S1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2FBFS2FBFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2sp2PP3CRT3BUF2bs3PP02B54CRT02D12FB3sp13APP3APC3SPR2F03D1u4SP1R2OP4HOP1S2PPS2FBFS2FBS3CRTFFS1R3NS14STKc5STKc32sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FFS2sp2PP3CRT2bs2FB3sp12F0SFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9S1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2sp2PP3CRT3BUF2bs2D12FB3sp13D1u2OP4HOP1S2loS2sp2PP3CRT2lo2bs2FB3sp14FBLOFS2FBFS2sp2PP3CRT2bs2FB3sp12F0S2FBS2FBFFS2FBFFFS2FBFS1R3NS14STKc5STKc12sp2PP3CRT3END3BUF2lo2bs3PP04PPLO2B34CRT02D13SPH2FB3sp15BUFLO3SPR3ACV2F02F14SLOu3D1u4SP1R4ENDX3EX22OL2OP2e93HE94HOP2FFS2sp2PP3CRT2bs2FB3sp1S2FBFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e93HP03HQ03HQE3HE9FS2FBS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22OL2OP1q2p02e93HP03HQ03HQE3HE94HOP14HOP2S1i2HiFFFFSFS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp12OL2OPFSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2sp2PP3CRT2lo2bs2FB3sp14FBLOS2sp2PP3CRT2bs2FB3sp12F0S2LF3BUF2bs4LFB33LFB2FB2OL2OP3x331CS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OP3x331CS2LF3BUF2lo2bs4LFB33LFB3sp12OL2OP3x331CS1R2LF3BUF2lo2bs4LFB33LFB3LOS2FB3sp13ALO2OL2OP4SBND3x331CFS2LF3BUF2bs4LFB33LFB2FB2OL2OP3x331CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF2PP3BUF2lo2bs4LFB33LFB4PPLO3sp12OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPFS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF2PP3CRT1P3END3BUF2bs4LFB33LFB2B12B22B33DPB2FB3APP3APC3APB4DXBu4ENDX3EX22OL2OP1q2bp2e93HQE3HE93HBP4HOP14HOP23HXLS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2OL2OPS2LF3BUF2lo2bs4LFB33LFB3sp15BUFLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB4FBLO4SLOu2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3END3BUF2lo2bs4LFB33LFB2B33sp15BUFLO4ENDX3EX22OL2OP2e93HE94HOP23HXLS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3BUF2lo2bs4LFB33LFB2FB3sp14FBLO2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB3sp16CRTLOu2OL2OPFS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R2LF3BUF2lo2bs4LFB33LFB3LOS3ALO2OL2OPFS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcS2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp13SPR2F02F82OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPS2LF3CRT3BUF2lo2bs4LFB33LFB6CRTLOu2OL2OPS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcFFFS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP14SLOu2OL2OPS1R2LF3BUF3slo2bs4LFB33LFB4SLOS2OL2OPFS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3ALO4SLOu2OL2OPS2LF2sp3BUF2lo2bs4LFB33LFB3sp13SP12OL2OPS1R3HIA1h2LF2sp3BUF2bs4LFB33LFB3TOP3sp12OL2OP5HTOPcFS2LF3BUF2bs4LFB33LFB2FB2OL2OPS2LF3BUF2bs4LFB33LFB2FB2OL2OPS2LF2PP3BUF2lo2bs4LFB33LFB4PPLO2OL2OPS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2OL2OPS2LF3BUF2bs4LFB33LFB2FB2OL2OPS1R3HIA1h2LF2sp3BUF3slo2bs4LFB33LFB3TOP3sp13SP12OL2OP5HTOPcS2LF3BUF2bs4LFB33LFB3sp14SP1R2OL2OPS2LF3BUF2bs4LFB33LFB2FB2F02OL2OPS2LF3BUF2bs4LFB33LFB2FB2F02OL2OP". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma oidl_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (OL OP q p0 bp e9 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e9 -> e9 <= ENDX -> BUD hc Lx bp -> P <= bp <= q ->
    BUF <= OP -> 0 <= OL -> OP + OL <= e9 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e9) s5v (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 e9) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa1c8) fc None mm (seg_rom asegs)).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "03f0@C40858145355.308C60410007123.307D10636937134.308D16071854214.308D16901939902.308D2457516971.308 D32458870384.308D39243574473.308D46794843979.308D60109446735.308D66237350158.308K1093189274.306 K12719279130.306K16483843482.306K17012660943.306K20040736922.306K20981739667.306K24527616463.306K26389978266.306K27873714767.306K28081892559.306K29378133114.308K30993319891.308K33674735898.306K41744454554.306K42309482703.306K45300827802.306K49805008847.306K53361377999.306K54996069696.307K56707495759.306K62527904282.306K65858155712.307K67776174415.306L10044042153.298L10079012065.2  L10323762809.81 L1103920410.2   L12729978778.2  L12800118897.3  L12865196093.88 L12867456647.85 L13527341863.85 L13529531805.88 L13636442081.2  L14115679076.3  L14402536676.299L14402536676.3  L15940222605.298L16482024986.2  L17025536345.2  L17698511111.81 L18259764001.0  L18501743953.81 L19700477810.81 L20038394650.2  L20977711877.2  L21122558689.2  L21654730866.2  L24514671193.2  L24882004373.71 L2621559066.1   L26375085850.2  L27111942217.1  L27832549545.282L27877616089.2  L27940752049.81 L28068947801.2  L29391009772.3  L29680655011.1  L30507144274.2  L30997223346.3  L32749673313.2  L33685467802.2  L3482445080.81  L35248710037.81 L35655538583.72 L35916062914.81 L36307103329.2  L38235734261.1  L38434951640.2  L40058613985.2  L40228640085.0  L41114250170.81 L41202929119.298L41251426164.1  L41755152410.2  L42296603481.2  L42488948659.2  L43317526968.81 L45193043736.24 L45311526170.2  L45382656977.84 L47870616696.2  L49233373885.2  L49800647769.2  L5021251703.1   L50678314462.3  L53357021529.2  L53530411688.1  L53704106081.2  L55008356054.2  L55182816650.81 L5659140096.84  L56719719641.2  L57083180513.2  L57389346443.81 L576250137.298  L58972694988.81 L59308586248.2  L6008604205.3   L60558678699.1  L61774255627.2  L62275882349.3  L62417043471.88 L62513011098.2  L62873986039.1  L64179129035.1  L64850595401.0  L65331221217.2  L656832749.85   L65862516566.2  L66298372189.2  L66812728480.3  L67070089790.2  L67763426009.2  L866928845.84   L881835912.0    L9090702513.71  N15340698282.307N18792612241.307N26872553873.307N48204456022.307N60733400192.307N66590330291.307O12232075104.306O14559438816.306O14912726833.307O151759997.306  O15540865262.306O16086026184.307O16723931389.306O18988691132.307O20866770946.308O21058125422.306O22525005962.307O2463212925.306 O24727989486.306O25722042592.306O25895279840.306O30010457231.307O34577654238.305O34618340093.306O3493317847.306 O37559489567.308O37860830077.306O3821773283.308 O424351700.306  O43490832480.306O44938202843.306O45423855982.306O46148948448.306O4719021806.306 O49076961262.306O49701823576.307O50011839873.306O52019636960.306O55209884805.306O55738917358.306O59000851965.306O59916692861.306O61256669038.306O64251960330.307O64474006218.307O66186539689.305O66725143264.306O6754613856.306 O6815798909.306 O8878376686.306 O9125703549.306 P10069038662.306P12785976022.305P13625410886.306P14121499075.305P21137750086.306P21647862485.306P30511339222.307P32763840966.306P36322327750.306P40051745350.306P42484919333.307P47876372191.306P49230739482.307P50671478649.306P53719298758.306P57084798790.306P61788423340.307P62260666314.306P65345388614.306P66292560634.307P66818508295.308P67064334489.307Q10592389669.306Q10592533181.308Q10598691865.282Q10636937134.308Q10637080374.306Q10649498890.307Q11133374175.308Q11657053839.308Q13191591773.307Q13731015691.306Q15673955380.306Q16071854214.308Q16178735000.308Q17027695041.308Q17681074618.308Q17701933584.307Q19561451475.282Q21767670690.308Q27573751300.308Q2803826605.308 Q29775981542.308Q3166354565.307 Q32681607669.308Q36985122307.308Q39600066516.307Q40904410655.308Q40916972731.307Q42439168719.308Q45360064137.306Q46794843979.308Q48118064779.308Q48669157117.307Q49746198710.308Q5638148954.282 Q56530976407.308Q57828105177.308Q60314416515.308Q6132825310.308 Q61847600945.307Q67038703949.308Q8699324297.308 Q9356559674.285 Q9633965612.282 Q9644583048.308 00000400800Y02003=03>03_03`04A04k05L05g06B06]07807S07m08H08c09>09Y0:40:O0:j0;E0;`0<;0<V0=10=K0=f0>A0>[0?60AT0AU0C:0C;0C<0C=0EI0GU0IW0KY0KZ0K[0K\0Kg0NI0NJ0NK0PI0PJ0SI0UJ0UK0UL0UM0UN0UO0Um0V20V30V70VX0VY0Y40Y50Y60Y;0Y<0Y=0Y>0Y?0[B0]H0_:0_W0_X0_\0_d0_e0_f0`C0`d0`h0`i0`j0`k0aD0aZ0a[0bC0bD0bE0bF0bG0bH0bI0bM0bN0bO0eJ0g?0g@0gA0gY0h:0hW0h]0hh0hl0hm0hn0iT0iU0iY0iZ0i[0i\0j10j20j30j40j50j60kd0ke0lA0lZ0l[0m40mU0nO0oY0oZ0o[0o\0o]0o^0o_0o`0oa0ob0oc0od0oe0of0og0oh0oi0oj0ok0ol0om0on0oo10010110210310410510610710810910:10;10<10=10>10?10@10A10B10C10D10E10F11E12G13F14B15A15B16617518419319g1:c1;_1<>1==1><1?81?W1@V1A11Ao1Bk1C>1CQ1Cd1D71DJ1D]1E01E11E^1F11FD1G<1GO1Gb1H^1I11I\1JX1JY1Jm1KH1KI1KJ1KK1KL1KM1KN1Ki1L<1LO1MC1N;1Nd1O71O81Oe1Pd1Pe1Q_1RW1SH1Sa1T71TMS2PPS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTcFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3BUF2bs4LFB33LFB2FB3APBS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APCS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43LR44Hq4a4Hq4LFS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e43HE4FFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBP2q43Hq4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02bp2e43HP03HQ03HQE3HE43HBPFFFS2rg3RRg2KzS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4ENDX3EX21q2p02e43HP03HQ03HE42q43Lw43Hq43LR44Hq4a4Hq4LFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4SS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFFFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S3sp1FS2PPS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4FFS3CRTFFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs2FB3sp13APBFS2loS2sp3sp1FSS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2FBFFFS2sp2PP3CRT2bs2FB3sp13APPS2bs2e42q43Lw44Hq4L2KmFS2sp2PP3CRT2bs2D12FB3sp13D1u1q2e42q43Hq4FFFFFFS2FBFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21q2p02e43HP03HQ03HQE3HE4S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p02bp3HQ03HBP2q44Hq4aFFS2sp2PP3CRT2bs2FB3sp12F0S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2sp2PP3CRT3BUF2bs3B472FB3sp1S1i2HiS2rg3RRg2KzS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNFS2FBFSFS2sp2PP3CRT2bs2FB3sp1FFFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R1q2p03HQ02q44Hq4aSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2LF2bs4LFB33LFB2FB3x341CFS2LF2bs4LFB33LFB2FB3x341CS2LF2sp2bs4LFB33LFB3sp13SP13x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu3x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2lo2bs4LFB33LFB2FB3sp14FBLOS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP1S1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB2FBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOuFS2LF2bs4LFB33LFB3sp1S2LF2sp2bs4LFB33LFB3sp13SP1FFFFFFS1R2LF3slo2bs4LFB33LFB4SLOSS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPcS2LF2bs4LFB33LFB2FBFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB3sp14SP1RS2LF2bs4LFB33LFB2FB2F0S2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma octet_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (OL OP q p0 bp e4 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd (Z_to_bv 64 OL) (Z_to_bv 64 OP) j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q)] ->
    P <= p0 -> p0 < q -> q <= e4 -> e4 <= ENDX -> BUD hc Lx bp -> P <= bp <= p0 ->
    BUF <= OP -> 0 <= OL -> OP + OL <= e4 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e4) (Z_to_bv 64 ENDX) (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa198) fc None mm (seg_rom asegs)).
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
