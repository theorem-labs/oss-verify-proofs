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
     A_asn1_get_bool A_oid_x509_ext A_x509_get_ext_A A_x509_basic_A A_x509_key_usage_A A_x509_skid_A A_x509_ns_cert_type_A A_x509_crt_ext_area A_x509_crt_ext_B A_x509_crt_ext_C A_x509_crt_ext_D.
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
    intros. first [ eapply A_x509_crt_ext_D.err_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_D.err_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_D.err_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SLOu EX1 EX2"] Lemma octet_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
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
    intros. first [ eapply A_x509_crt_ext_D.octet_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) (STKc := STKc) | eapply A_x509_crt_ext_D.octet_walk with (ENDX := ENDX) (BUF := BUF) (bs := bs) (a4e := a4e) | eapply A_x509_crt_ext_D.octet_walk ]; eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05f0@C40858145355.311C51712377427.310D10636937134.311D16071854214.311D16901939902.311D28498761192.285D33317801621.284D33317801621.285D35749367497.311D40338479819.284D40338479819.285D4451634193.285 D46794843979.311D49496112240.311D57793146470.284D57793146470.285D60109196847.285D60109446735.311D64280614944.284D64280614944.285D67666003371.311D717153038.311  K10093203181.285K1093189274.309 K12226132804.284K12226132804.285K12406281821.284K12406281821.285K12719279130.309K13517334159.309K16483843482.309K16863439631.309K17397425005.285K18972714752.310K1945250781.284 K1945250781.285 K19727149789.284K19727149789.285K20040736922.309K20981739667.309K23551032557.285K2431698795.285 K26389978266.309K27222706653.284K27222706653.285K30840574317.285K30993319891.311K33674735898.309K37953334125.285K38603332111.309K41744454554.309K42157607183.309K44164039966.284K44164039966.285K45300827802.309K45507919247.309K45578736733.284K45578736733.285K48924907741.284K48924907741.285K49064812687.309K49655786511.309K49978975725.285K52308700509.284K52308700509.285K52576198765.285K52829345295.309K58743820992.310K59993490141.284K59993490141.285K60822670701.285K62527904282.309K62860102458.311K63150298333.284K63150298333.285K65858155712.309K9136277101.285 K9368417295.309 K9840090748.285 L10079012065.2  L10091109645.2  L10323825918.83 L1041429731.83  L10663055041.87 L1103920410.2   L11333811117.3  L11427873569.0  L12221849778.2  L12271194856.1  L12410523051.2  L12729978778.2  L13513501977.2  L13529531805.90 L13636442081.2  L14115679076.3  L14447004729.2  L14875714635.2  L15756275188.83 L15844971277.83 L16482024986.2  L1685717371.0   L16876183705.2  L17382748301.2  L18959903894.2  L1932750891.2   L19714617643.2  L20038394650.2  L20977711877.2  L21122558689.2  L21654730866.2  L21791022168.87 L21866712442.1  L23082226047.83 L23182876091.2  L23540543245.2  L24054617783.1  L2419170461.2   L24882004373.71 L2621559066.1   L26375085850.2  L27111942217.1  L27218465323.2  L27650499371.1  L27940814902.83 L29680655011.1  L30507144274.2  L30851056269.2  L30929952171.1  L30997223346.3  L32361341480.1  L32749673313.2  L33685467802.2  L33740837294.0  L3482382239.83  L35098291383.1  L35655538583.72 L35915999813.83 L36307103329.2  L3740020506.87  L37963823245.2  L38235734261.1  L38434951640.2  L38591107481.2  L40058613985.2  L40419466676.1  L41114181949.83 L41202929119.273L41755152410.2  L42145383065.2  L44168158952.3  L44168742175.3  L4501932337.3   L45121863851.1  L45311526170.2  L45512275481.2  L45574590379.2  L47870616696.2  L48842827546.272L48937534251.2  L49068649241.2  L49651296153.2  L49964299789.2  L50678314462.3  L50925318027.2  L51578009499.1  L52296038059.2  L52565717901.2  L52783746038.87 L52816403865.2  L52836486813.90 L53271535775.273L53704106081.2  L53888385548.83 L54261998223.2  L55114843957.83 L55343106074.273L57083180513.2  L57933456208.301L57935548298.300L58747656534.2  L58972627787.83 L59980994859.2  L60828966541.2  L61207844268.83 L61310511514.273L6198624755.2   L62513011098.2  L62847746220.3  L63162830635.2  L63557664125.2  L64038109431.1  L64179129035.1  L64850595401.0  L65153465678.272L65331221217.2  L65693950831.1  L65862516566.2  L66298372189.2  L66660965579.90 L66812728480.3  L67070089790.2  L7656564418.83  L7738195705.2   L8470911054.273 L881835912.0    L9090702513.71  L9134183821.2   L9372385177.2   L9644563342.71  L9835808138.2   N15340698282.310N18792612241.310N26872553873.310N48204456022.310N60733400192.310N66590330291.310O12232075104.309O14559438816.309O14912726833.309O15540865262.309O18086641154.311O18988691132.309O21058125422.309O22525005962.309O24727989486.309O25722042592.309O25895279840.309O25975595998.308O26607118461.309O33254904445.309O3493317847.309 O35563760509.309O36529296776.310O37559489567.311O3821773283.311 O4028702351.309 O43490832480.309O44938202843.309O45423855982.309O46148948448.309O4719021806.309 O47747662589.309O48233649620.309O49076961262.309O50011839873.309O50038152189.309O52019636960.309O53951749322.310O54421585546.310O55209884805.309O55539665277.309O55738917358.309O56496609880.309O57620671869.309O61256669038.309O62222087037.309O64474006218.309O65961212488.309O66186539689.308O66725143264.309O6754613856.309 O67738280189.309O8878376686.309 P10069038662.309P11331234058.309P13625410886.309P14121499075.308P14461423358.284P14461423358.285P14868920044.310P21137750086.309P21647862485.309P23170010975.285P30511339222.309P32763840966.309P36322327750.309P40051745350.309P4508801942.308 P47876372191.309P50671478649.309P50927926572.309P53719298758.309P54268551240.285P57084798790.309P6202460773.309 P63564427226.309P65345388614.309P66292560634.309P66818508295.311P67064334489.309P7750690063.284 P7750690063.285 Q10636937134.311Q10639328735.281Q10649498890.282Q10752139055.284Q10752139055.285Q11697867869.281Q13546929313.284Q13728816866.281Q16071854214.311Q17027695041.311Q17681074618.311Q17701933584.282Q17757173815.281Q17757173815.282Q21767670690.311Q22647423948.281Q23170048734.311Q27573751300.311Q27663313085.311Q2803826605.311 Q28496781288.284Q28498761192.285Q28694295695.311Q29775981542.311Q32681607669.311Q32681824661.284Q32681824661.285Q34671223321.280Q36508117400.311Q36985122307.311Q37216054521.282Q39460178071.311Q39600066516.282Q40686361676.281Q40904410655.311Q40916972731.282Q42439168719.311Q42439443119.284Q42439443119.285Q43204903389.281Q44341150977.284Q4451634193.285 Q4453582353.284 Q45357732960.281Q46794843979.311Q46922786263.284Q46922786263.285Q48117823211.284Q48117823211.285Q48118064779.311Q49698585326.282Q49698585326.283Q49746198710.311Q49746415830.284Q49746415830.285Q520094728.280  Q52744951088.283Q52744951088.284Q52747231024.284Q52747231024.285Q53354853794.284Q53354853794.285Q57828105177.311Q60314416515.311Q60529412798.285Q61556549392.283Q61847600945.282Q65424847505.283Q65424847505.284Q65426765969.284Q65426765969.285Q67038703949.311Q67038978349.284Q67038978349.285Q68013150533.284Q68013150533.285Q7136501407.311 Q8699115497.284 Q8699115497.285 Q8699324297.311 Q9356559660.288 Q9644583048.311 00000400800Y02003=04404504604704804905005Q06206b07U08U09?09o0:b0:c0;D0<50<P0=90=e0>O0?<0?W0@20@M0@h0AY0B30B]0CJ0D40Da0E<0EV0FG0G70GR0H<0Hi0IZ0J50JP0KA0K\0L70LR0M<0N40NO0Nj0OT0PA0Pk0QX0R30RN0S?0Si0TV0UG0Ub0V<0Vf0WS0XD0X_0Y:0Yd0ZQ0Zk0[\0\70\g0\h0\i0^N0^k0a<0a=0a>0a?0a@0aD0aE0aF0aG0cY0cZ0c[0c\0c]0f;0f]0f^0f_0f`0fa0fb0fc0fd0fe0ff0fg0fh0gL0gP0gi0gj0gk0go0h00hN0hS0hT0hX0hY0h]0k>0kC0kD0kE0kI0kJ0kN0kO0kP0kQ0mZ0m[0oM0oj0ok12A12B12F12N12O12P12T13113R13S13T13U13V13W13[13\13]13^13_14@14A14B14C14D14E14F14J14K14L15915:17O18018118I18J1:Q1;21;31;41;51;61;S1;T1;U1<21<S1<T1<U1<V1<W1<X1<\1<]1<^1=?1=@1=D1=E1=F1=l1=m1=n1@51@61@W1@X1A41A51A61AN1AO1Ah1Ai1BB1Bc1C]1Dg1Dh1Di1Dj1Dk1Dl1Dm1Dn1Do1E01E11E21E31E41E51E61E71E81E91E:1E;1E<1E=1E>1E?1E@1EA1EB1EC1ED1EE1EF1EG1EH1EI1EJ1EK1EL1EM1EN1EO1EP1EQ1ER1ES1ET1EU1EV1FU1G41H31Ho1J:1KH1LD1MC1MD1NN1OB1PA1Q@1R?1SA1T=1T\1UX1VW1Wi1Xh1Y\1ZX1[W1\21]01]l1^o1`51`H1`[1`n1`o1a01aC1b;1bN1cF1cY1dU1dh1eA1eZ1fV1fi1fj1fk1g>1gR1h;1hd1he1i@1iA1iB1iC1iV1ii1ij1jD1jE1jF1jY1jZ1j[1k61kc1lZ1lm1mZ1nC1nl1o?1oR1oS1oT20Z21c22W23323O24825326826K26m27R28428Y28Z28[29H2:G2:H2:d2;^2<@2<e2=G2=l2>d2?n2AB2B32Bk2C>2DA2EN2F?2FX2FnS2PPS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTcS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13Lw12q12HB5Ha_st5Hl_stFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13Lw12q12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12q12HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp13Lw12q12HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12q12HB5Ha_st5Hl_stFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3BUF2bs4LFB33LFB3DPBS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_stS2LF3BUF2bs4LFB33LFB2FB3APB2q12HB5Ha_st5Hl_st2PP3DPB3Lw1S2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APPS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF3BUF2bs4LFB33LFB2FB3APBS2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APPS2LF2PP3CRT2bs4LFB33LFB3D1u3Lw12q12HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP2bs4LFB33LFB2FB3APP3Lw12q12HB5Ha_st5Hl_stFFS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22e43HE4S2sp2PP3CRT2lo2bs4PPLO2FB3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HE43HBP3LR12q23Hq2FFSFS2FBFFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2FFFFS1R2sp2PP3CRT1P3END3BUF2lo3slo2bs3PP02B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13APP3APC3SPR3ALO2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOFSFFFFFFFFFS2sp2PP3CRT2bs2D12FB3sp13D1u3Lw13LR1S2FBS2sp2PP3CRT2bs2FB3sp13APPFFS2FBFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S3sp1FS2PPFS2FBS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S3CRTFFS2FBFS2FBFFSS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1FS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcS2sp2PP3CRT3BUF2bs2FB3sp13APBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2FS2loS2sp3sp1FFS2FBS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2FBFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFFS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u3Lw12q12e42q23Hq2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02bp2e43HP03HQ03HQL3HE43HBP3LR12q23Hq2S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT2bs2FB3sp12F0FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2sp2PP3CRT3BUF2bs3B472FB3sp1FFS2sp2PP3CRT2lo2bs2FB3sp14FBLOS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2FBFSS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2rb3RRb2RNFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX23Lw12q12p02e43HP03HQ03HQL3HE43LR1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1SS2sp2PP3CRT2lo2bs2FB3sp13SP1FFS2sp2PP3CRT2bs2FB3sp12F0FS2LF2bs4LFB33LFB2FB3x341CFS2LF2bs4LFB33LFB2FB3x341CS2LF2sp2bs4LFB33LFB3sp13SP13x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu3x341CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2lo2bs4LFB33LFB2FB3sp14FBLOS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu3Lw12q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu3Lw12q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP1S1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOuS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS2LF2bs4LFB33LFB2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS2LF2bs4LFB33LFB2FB2F02HBS2LF2bs4LFB33LFB2FB2F02HBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOuS2LF2bs4LFB33LFB2FBFFS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB3sp1S2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stFS2LF2sp2bs4LFB33LFB3sp13SP1FFFS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBFS2LF2PP2bs4LFB33LFB3PP02HBFFS2LF2bs4LFB33LFB2FBFFS1R2LF3slo2bs4LFB33LFB4SLOSS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_stS1R2LF3slo2bs4LFB33LFB4SLOS2FB2q12HB5Ha_st5Hl_st2PP3Lw1S2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB3Lw12q12HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOuS2LF2bs4LFB33LFB2FB2HB5Ha_stS2LF2bs4LFB33LFB2FB2HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOPcS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12q15HTOPc2HB5Ha_st5Hl_st2PP3Lw1S2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOPcS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuFS2LF2PP2bs4LFB33LFB2HB5Ha_stS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2q12HB5Ha_st5Hl_st2PP3Lw1S1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2q12HB5Ha_st5Hl_st3Lw1S2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12q15HTOPc2HB5Ha_st5Hl_st2PP3Lw1S1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOPcS2LF2bs4LFB33LFB3sp14SP1RS2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 DIMG HMND GT GB OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma mid_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lx : list blk) (X : xst) (lenw otg opd Lw1 op crit et w0 w1 w2 k16 : word) (j1 j2 j3 j4 ja jb : list byte)
      (q1 p0 bp e4 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    xinv Lx mm hc X (FLOC lenw j1 otg opd Lw1 op j2 crit j3 et j4) FSHB w0 w1 w2 k16 ja jb -> rw_cells asegs mm PP [C8 (Z_to_bv 64 q1)] ->
    P <= p0 -> p0 < q1 -> q1 + bv_unsigned Lw1 <= e4 -> e4 <= ENDX -> BUD hc Lx bp -> P <= bp <= p0 ->
    (forall p', p0 < p' -> p' < ENDX -> LoopOblig p') ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 e4) (Z_to_bv 64 ENDX) (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0aa158) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV HPP HP0 HQ0 HQL HE4 HBUD HBP KLOOP.
    pose proof (bv_unsigned_in_range 64 Lw1) as LR1. unfold bv_modulus in LR1. cbn [Z.pow Z.of_N Pos.pow] in LR1.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 9 zstep.
    idtac "MID-A".
    replace Lw1 with (Z_to_bv 64 (bv_unsigned Lw1)) in FLOCc by (apply Z_to_bv_bv_unsigned).
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
    zstep. zstep. if_cases K98; zify_cond K98.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0=i0@C17025492443.313C23922862675.314C40860242540.358C40860242543.334C54716835444.359C60407910007.335D10051067940.294D10639034249.359D10639034250.335D12007639820.359D15167092818.294D15181789897.314D16069757089.359D16069757090.335D16899842713.359D16899842714.335D21198918766.359D2455419791.335 D24860224160.315D27847976046.314D32118226965.315D32456773204.335D39172463691.315D39245671661.335D45941514153.359D46792746860.359D46792746863.335D56525861611.294D56536395888.314D57793146470.315D5977889584.294 D5984197035.314 D60109446735.314D60111543912.359D60111543915.335D62557220311.359D6359981838.314 D66239447338.335K10528470632.357K1091092157.357 K1091092158.333 K11279907944.357K12226132804.315K12406281821.315K12717182013.357K12717182014.333K16485940669.357K16485940670.333K17014758123.333K18289619279.314K18774905704.357K1945250781.315 K19727149789.315K20042834109.357K20042834110.333K20983836852.357K20983836855.333K21848089679.314K24525519339.333K24934862056.357K25612096975.314K25644846817.314K26387881149.357K26387881150.333K27222706653.315K2725917647.314 K27871617643.333K28083989739.333K29380230238.335K29718646631.359K30995417076.359K30995417079.335K33672638781.357K33672638782.333K35305884239.314K35791180904.357K40515338856.357K41742357437.357K41742357438.333K42311579883.333K42628394703.314K44073300328.357K44164039966.315K45298730685.357K45298730686.333K45578736733.315K48924907741.315K49807106027.333K50870635471.314K51307378141.359K52308700509.315K53363475179.333K54998166884.335K56709592939.333K59993490141.315K62299668967.359K62525807165.357K62525807166.333K63150298333.315K64331061711.314K64816380904.357K65584587240.357K65856058596.335K65856058599.358K67778271595.333K67886910671.314K6992036218.314 K9992062130.314 L10079012065.2  L10166012279.1  L10526539225.2  L1066678333.2   L10685100449.0  L1074142290.76  L11035350155.2  L1103920410.2   L11063982577.3  L11285837785.2  L12221849778.2  L12252132089.3  L12366868378.303L12410523051.2  L12729978778.2  L12800118897.3  L13176305223.2  L13236461722.303L13636442081.2  L13947844548.3  L14115679076.3  L14358424541.3  L14371014045.81 L14371014045.87 L14402536676.3  L14402536676.325L14402536676.348L14447004729.2  L14508908083.2  L15822417165.1  L15934535645.1  L16482024986.2  L16772787627.1  L1685717371.0   L17025536345.2  L17618613065.87 L17901108232.82 L18301909721.2  L18491248361.82 L18503839381.76 L18560700843.1  L18789947609.2  L19103996075.1  L1932750891.2   L19698382006.76 L19714617643.2  L19965341035.71 L20038394650.2  L20977711877.2  L21122558689.2  L21218866939.2  L21654730866.2  L21860380633.2  L21866712442.1  L22212138180.3  L22941438733.1  L24023900370.0  L24514671193.2  L24796913220.3  L24882004373.71 L24945510233.2  L25582886452.76 L25608068697.2  L25639998743.2  L2621559066.1   L26375085850.2  L27111942217.1  L27218465323.2  L2730473561.2   L27803524787.2  L27817441514.286L27817441514.287L27832386217.309L27877616089.2  L27938656629.76 L27942859017.82 L28068947801.2  L29391009772.3  L29680655011.1  L29719275082.82 L29724706006.2  L30222833085.291L30507144274.2  L30997223346.3  L31116369961.87 L32431276449.0  L32749673313.2  L32755215223.1  L32866598340.3  L33685467802.2  L3480346272.82  L3484548828.76  L35234028077.82 L35246619217.76 L35309781465.2  L35655538583.72 L35797835737.2  L35905575802.82 L35918166790.76 L36279126350.310L36307103329.2  L36463206329.4  L37221859762.82 L38235734261.1  L38434951640.2  L39327145395.82 L39432216734.82 L40058613985.2  L40228640085.0  L40500365785.2  L41112145922.82 L41116348542.76 L41202929119.324L41251426164.1  L41409160545.3  L41755152410.2  L42296603481.2  L42411609006.0  L42488948659.2  L42615973209.2  L42747432695.1  L42888316781.71 L42932240884.1  L43315436156.76 L4370579368.1   L43927446468.3  L44058852057.2  L44168158952.3  L45176358486.87 L45311526170.2  L45574590379.2  L4606099115.1   L46301709303.1  L47200528500.1  L47289743172.3  L47441473005.3  L47870616696.2  L48022350876.310L48134333217.0  L48843152936.1  L48937534251.2  L49207136770.3  L49233373885.2  L49800647769.2  L50065846443.87 L5021251703.1   L50678314462.3  L50770721805.82 L50883575897.2  L50925318027.2  L51318226540.3  L52296038059.2  L52941874306.3  L53357021529.2  L53530411688.1  L53704106081.2  L54390426909.81 L54504511085.3  L55008356054.2  L55085943702.3  L55180717646.76 L55342919976.1  L5660843561.76  L56664292285.2  L56719719641.2  L57016247721.71 L57083180513.2  L57387251023.76 L57394714052.3  L576250137.324  L58800644485.71 L58974794248.76 L58987369076.82 L59308586248.2  L59980994859.2  L6008604205.3   L60558678699.1  L61310308520.1  L61643025177.87 L61774255627.2  L61778427895.1  L62275882349.3  L62306126422.2  L62353614618.87 L62417043471.81 L62417043471.87 L62513011098.2  L62873986039.1  L63162830635.2  L64009471222.1  L64179129035.1  L64335090265.2  L64686745924.3  L64818164174.303L64822898777.2  L64850595401.0  L65261890929.3  L65331221217.2  L65594780249.2  L65642230468.3  L65862516566.2  L66298372189.2  L66812728480.3  L66925338641.288L67070089790.2  L67763426009.2  L67891464025.2  L6979816172.3   L7738195705.2   L8136662222.303 L8171953640.286 L8171953640.287 L881835912.0    L9090702513.71  L9225258773.332 L9476030541.71  L988506752.82   L9988165412.2   N10400473443.314N14342935073.314N15139586140.358N21881295695.358N23667955994.334N25297080393.334N29731080008.314N34470429922.334N34515723252.314N34870951589.334N38481866511.314N4182430466.314 N4217864246.358 N47900433899.358N54376292405.358N59706724824.334N62331351520.358N63610817641.334O10378001882.357O12233548996.314O12234172228.333O12234172231.357O14175554244.314O14561535940.333O14561535943.357O1478916974.314 O14914823957.333O14914823958.357O153857113.333  O15542962377.357O15542962378.333O16088123372.335O16620552189.314O16726028505.333O17025492443.313O17044154330.357O17758872154.357O18990788248.333O18990788251.357O20059408765.314O20458779460.314O20868868134.335O21056028233.357O21056028234.333O22138318205.314O22527103149.358O22527103150.335O22557709658.357O23922862675.314O24352547140.314O2465310041.333 O24725892297.357O24725892298.333O25719945412.333O25719945415.357O25893182660.333O25893182663.357O26950528889.356O28802357117.314O29946971610.357O30012554411.333O3078286936.314 O31587119912.357O32216486618.357O33083286018.314O34052634180.314O34575557114.332O34616242905.333O3491220720.357 O3491220723.333 O37557392440.359O37557392443.335O37858732889.333O3823870404.359 O3823870407.335 O38899942618.357O40034824061.314O40562546687.357O426448880.333  O43492929604.333O43492929607.357O43520387038.312O43849271089.314O44940300028.357O44940300031.333O45421758793.357O45421758794.333O45947445700.314O46146851268.333O46146851271.357O4721118921.357 O4721118922.333 O47737000900.314O48262126959.359O4864412762.357 O49074864073.357O49074864074.333O49585648037.359O49699726460.333O50009742757.333O50009742758.357O50401764781.359O50689527441.314O5099699757.359 O51150049554.314O52021734084.333O52021734087.357O52218726141.314O53449798340.314O55211981985.333O55211981986.357O55518239188.313O55741014473.357O55741014474.333O56414299794.314O57734935677.314O57957320900.314O58998754777.333O59625529265.314O59918789977.333O60978474237.314O61254571849.357O61254571850.333O64249863214.335O64417349245.314O64471909101.357O64471909102.333O65469896563.357O65963309679.358O66188636813.332O66188636814.356O66723046084.333O66723046087.357O66812877810.314O67171060367.314O6756710980.333 O6756710983.357 O6817896025.333 O7859127258.357 O8876279497.357 O8876279498.333 O9123606361.333 P10066941537.357P10066941538.333P1063054013.357 P11023336971.359P11068648305.356P12257878110.314P12788073202.332P13623313761.357P13623313762.333P13953656163.314P14119401956.356P14119401959.332P14461423358.315P14498256258.357P1637532236.317 P21135652961.357P21135652962.333P21212095580.313P21649959665.333P21649959666.357P22197995107.314P24812063971.314P25644846817.314P27816465701.314P30513436401.357P30513436402.333P324046647.293  P324046647.294  P324046647.317  P32761743841.357P32761743842.333P32881815395.314P36320230625.357P36320230626.333P36465839390.314P38605639612.293P38605639612.294P38605639612.317P40053842529.357P40053842530.333P41419110342.314P42487016449.333P43934249315.314P47284020707.314P47436775277.357P47874275064.357P47874275067.333P49191944357.314P49211061452.293P49211061452.294P49211061452.317P49228642366.333P50673575773.333P50673575774.357P50930023691.358P52940256805.314P53717201633.357P53717201634.333P54497641674.313P55088519473.314P56666925338.314P57086895969.357P57086895970.333P57379456867.314P61786326152.335P62262763502.333P64680999907.314P65246707670.312P65343291489.357P65343291490.333P65640603747.314P66294657757.357P66294657758.333P66816411168.359P66816411171.335P67066431677.333P67066431678.357P7740881908.293 P7740881908.294 P7740881908.317 P7750690063.315 P7903954312.293 P7903954312.294 P7903954312.317 Q10024872496.311Q10195749203.288Q10592318618.280Q10592389157.332Q10594415773.314Q10594630297.335Q10598528537.309Q10637079862.332Q10639034249.359Q10639034250.335Q10639171022.277Q10649498890.333Q10821824020.293Q10821824020.294Q10821824020.317Q1091606566.293 Q1091606566.294 Q1091606566.317 Q1091858145.359 Q1091858146.335 Q1093713574.315 Q1093955270.314 Q11093001477.288Q11135471355.335Q11659151019.335Q11796756721.288Q11988014288.287Q12658605510.293Q12658605510.294Q12658605510.295Q12658605510.296Q12658605510.317Q12658605510.319Q13241170297.290Q13731016203.332Q1403108299.278 Q14143836712.359Q14705649756.283Q14742886208.359Q14751535315.288Q15258109527.315Q15616052641.311Q15766564435.314Q15944836594.287Q16069757089.359Q16069757090.335Q16180832188.335Q16355141072.287Q16909570643.288Q17025597925.335Q17025597926.359Q17558758360.289Q17683171741.359Q17683171742.335Q17701933584.333Q17716263636.277Q1895155614.312 Q19546780655.332Q19561677163.288Q19561680339.309Q19955343048.359Q19955343051.335Q20187357108.332Q20517146075.290Q21365000441.312Q21765573509.359Q21765573510.335Q21797099320.311Q22374337363.288Q22516600531.288Q23232684382.285Q23613318552.314Q2363337691.290 Q24257074651.290Q24862400672.314Q2605063902.314 Q26314584654.293Q26314584654.294Q26314584654.317Q26316671538.274Q26318654066.314Q26432625456.359Q26729481055.284Q27118626695.311Q27575848480.335Q27575848483.359Q27665131166.311Q27863312744.332Q27865799639.359Q2805923721.335 Q2805923722.359 Q28449463941.333Q2863532638.285 Q28666805532.313Q2905254131.311 Q29097057975.312Q29322743127.359Q29324722152.332Q29732604428.273Q29778078657.359Q29778078658.335Q30265210969.312Q30319892460.311Q30387997187.332Q30441621865.279Q30645011775.359Q31124869336.314Q31339371283.288Q3166354565.333 Q32437204119.314Q32452805332.309Q32456773204.335Q32457080912.314Q32459013352.332Q32679510481.335Q32679510482.359Q32681607669.314Q32681824661.315Q32959886801.286Q3317830712.313 Q3339752862.280 Q342032561.311  Q34268448600.289Q34363165844.314Q3444200401.286 Q34667034333.312Q34669522109.314Q34671389857.288Q34877581972.288Q34952600272.287Q34964382778.314Q35164442047.359Q35378271416.311Q35895740379.290Q36652444704.314Q36759522011.290Q36768752385.332Q36983025188.359Q36983025191.335Q37039215513.314Q37065061723.290Q37654045871.315Q38555981400.289Q3886571317.311 Q39328755025.286Q39408379774.283Q39600066516.333Q39885187281.313Q40332524508.283Q40513116131.311Q40586814278.308Q40686657050.359Q40688626853.332Q40906507832.359Q40906507835.335Q40916972731.333Q40974010456.289Q41527591263.314Q41635797459.288Q4174339024.287 Q41794435086.332Q42295909976.289Q42301876062.314Q42352164051.311Q42439168719.314Q42439443119.315Q42441265896.359Q42441265899.335Q42441548847.293Q42441548847.294Q42441548847.317Q42757159386.309Q44113183171.335Q44298944140.274Q44298944140.289Q44298944140.309Q44298944140.312Q44301027056.293Q44301027056.294Q44301027056.317Q4473570896.287 Q44876980066.288Q45439978169.314Q45445507793.286Q45482765142.295Q45482765142.296Q45482765142.319Q45742292654.311Q45806042497.332Q45904387664.314Q46591526104.289Q46792746860.359Q46792746863.335Q47061991091.314Q47375526168.313Q47604779231.313Q48117823211.315Q48118064779.314Q48119910507.293Q48119910507.294Q48119910507.317Q48120161964.359Q48120161967.335Q48189903665.311Q48234175664.314Q48360113622.314Q4845047677.284 Q49494258259.311Q49698585326.313Q49746198710.314Q49746415830.315Q49748295825.359Q49748295826.335Q49748522582.293Q49748522582.294Q49748522582.317Q50324780992.359Q50445979747.311Q51379872473.288Q51959565846.279Q52387815135.284Q52690940469.289Q52690940469.309Q52747231024.315Q53317345084.335Q53328907473.286Q53466943967.314Q53774309119.282Q53850310965.312Q54196455217.288Q54196504185.308Q54200699147.288Q54295544543.313Q54661710218.311Q54785822014.288Q54856420359.311Q55401488351.314Q5540636085.312 Q5596578838.293 Q5596578838.294 Q5596578838.317 Q56186208347.290Q56452622865.314Q56454570001.315Q56525680748.288Q56533073587.335Q56536395888.314Q56538360336.312Q56900949851.290Q57209973095.314Q57830202365.335Q57830202366.359Q5857658577.313 Q58972088534.281Q59391892184.289Q59422879440.314Q59581939575.332Q59617550414.311Q59617553652.288Q59621696206.288Q59621745542.308Q59991740767.284Q60316513700.359Q60316513703.335Q60422877723.312Q60746685720.314Q6126053922.315 Q6134922490.335 Q61500136060.285Q61543209836.311Q61847600945.333Q6190817072.335 Q6190817075.359 Q6191098356.293 Q6191098356.294 Q6191098356.317 Q6192914196.314 Q6193188724.315 Q62380812747.314Q62555250536.332Q62557220311.359Q62603800435.286Q62635101267.288Q63236532495.311Q63435846322.289Q63435846322.309Q63435846322.312Q63488537438.285Q64228675114.292Q64228675114.293Q64228675114.316Q64411644381.282Q65430079568.287Q6562449867.308 Q65892967672.359Q66901779611.289Q66901779611.309Q66901779611.312Q66922076282.289Q66995821912.289Q67028497104.278Q67038703949.314Q67038978349.315Q67040801129.335Q67040801130.359Q67041068973.293Q67041068973.294Q67041068973.317Q67126152652.273Q68011063237.293Q68011063237.294Q68011063237.317Q68013150533.315Q6824367933.309 Q68336587110.332Q6912043752.281 Q705497310.285  Q7830203611.290 Q8126701711.314 Q8626407545.359 Q8699115497.315 Q8699324297.314 Q8701202793.293 Q8701202793.294 Q8701202793.317 Q8701421485.335 Q8701421486.359 Q8935019596.311 Q9356559649.294 Q9356559674.312 Q9356559674.336 Q9633866796.309 Q9633867924.288 Q9644448272.332 Q9644583048.314 Q9646680236.335 Q9646680239.359 00000100200600:00>00B00j01R02:02;02<02=03[05906M07a07b07c08Z0:10:20:Z0:[0:\0;D0;l0<T0=<0=d0>[0>\0>]0?N0@?0A00AX0B@0Bh0CJ0Cl0DN0E00E`0FQ0G30GU0H70HY0I;0I]0J?0K00Ka0LC0Le0MF0Mg0NI0Nk0OM0Oo0P00PR0Q40Qe0RG0Ri0SK0Sm0TN0U00UR0V40VV0W80WZ0X<0X^0Y@0Yb0ZD0Zf0[W0\90\[0]L0^=0^_0_A0_c0`T0a60aW0b90bj0cK0cm0dO0e@0eb0fD0ff0gG0gh0hJ0hl0iN0io0j00j10j20j30j40j\0j]0j^0j_0j`0ja0jb0kJ0kK0kL0kM0kU0l=0l>0l?0l@0lK0n60om10810910:10;10<10@10C10D10H10I10J12W14[14\17^1:J1:N1:O1:S1:T1<B1<C1>01>11>21>31>41>51>61>:1>;1>?1>@1>A1>B1>`1>a1@M1@N1@O1@T1@U1@Y1@Z1@[1@\1A_1Bb1CJ1CK1ES1H11H21H31H81J<1J=1J^1J_1J`1KM1KN1KO1KS1KT1KU1M[1OK1QQ1SW1SX1UJ1UK1Uh1VE1WP1WQ1WR1ZP1ZT1Z\1[41\^1\_1\`1\a1]>1][1^C1^G1^H1^I1^J1^K1^L1^M1^Q1_H1_L1_e1_i1_j1_k1_l1`T1`U1`V1`Z1`^1`b1`c1`d1`e1`f1`g1`k1`l1`m1`n1`o1aW1aX1aY1b@1bA1bB1bC1bD1bE1bF1bJ1bK1d=1d>1d?1d@1fh1fl1hJ1hK1hL1ha1hb1i:1i;1ic1k]1l:1lW1l]1l^1li1lm1m11o<1o=1oA1oB1oC20220X21>21?21C21D21E21F21G21H22022122222322422522622722822922Z22[22\22]22^22_23G23H23I23J23f24N24k25D25E25e26[27;27[28l29T2:42:52:`2;@2;A2;e2<f2<g2>82>X2?@2@A2@B2@C2@D2@E2@F2@G2@H2@I2@J2@K2@L2@M2@N2@O2@P2@Q2@R2@S2@T2@U2@V2@W2@X2@Y2@Z2@[2@\2@]2@^2@_2@`2@a2@b2@c2@d2@e2@f2@g2@h2@i2@j2@k2@l2@m2@n2@o2A02A12A22A32A42A52A62A72A82A92A:2A;2A<2A=2A>2A?2A@2AA2AB2AC2AD2AE2AF2AG2AH2AI2AJ2AK2AL2AM2AN2AO2AP2AQ2AR2AS2AT2AU2AV2AW2AX2AY2AZ2A[2A\2A]2A^2A_2A`2Aa2Ab2Ac2Ad2Ae2Af2Ag2Ah2Ai2Aj2Ak2Al2Am2An2Ao2B02B12B22B32B42B52B62B72B82B92B:2B;2B<2B=2CC2DI2EL2FO2GX2H>2IG2JM2KS2L<2M?2NB2OT2PO2Q@2RF2SL2SM2SN2SO2T82Ta2Tb2U]2VX2WS2XQ2YO2ZT2[Z2\`2]I2^O2_U2`=2`o2aa2bZ2c`2df2eL2fG2g02gY2h?2iB2jE2jk2k]2lO2mH2nK2o12oW30Z31@32F33L34234W35Z36`37f38O39R3:83:a3;j3=03>63>_3?A3?c3@h3Am3C03D33Dd3EU3FM3GW3Hh3J93KQ3KR3KS3L73LQ3M<3MV3N03NJ3Nd3O>3Oe3P?3Pm3Q[3RP3RQ3RR3RS3RT3RU3RV3RW3Rj3SD3SE3Sm3Sn3T\3UJ3VO3WT3XI3YU3Z=3ZW3[V3[W3[X3[Y3\A3\B3\\3]@3]h3^g3_f3`@3`A3`B3`\3a63a73b:3c=3cW3d>3di3e[3fF3g83g93g:3g;3g<3g=3h@3iC3i]3i^3i_3i`3j:3j;3j<3je3jf3kP3l:3lk3mC3mh3mi3mj3mk3ml3mm3nG3na3o;3oV40140240340^41941Y41Z41[41n42P43243343M43g44i45C45D45W45X45Y46346M47847R47S47T47U47V47W47X48<48V48W48X48Y49D49^4:14:D4:E4;@4;A4;B4;C4;l4;m4<G4<H4<I4<J4<K4<L4<M4<h4=P4>84>94>d4?L4?f4@@4@Z4A44A54A64A74A84A94A:4A;4AV4AW4BB4B\4C>4D24DT4E64Ei4F\4GV4GW4H14HI4Ha4I@4I_4JI4K34Kd4Ke4Kf4Kg4Kh4Lm4N24O>4OX4OY4OZ4O[4P54PO4PP4PQ4Q<4RI4SD4TP4U\4Vo4Wj4Xe4Xf4Xg4YL4Z44ZN4[14[a4\c4]S4^C4_D4`E4aM4ag4bA4bT4cK4d34dK4dj4eS4eT4eU4eo4fW4g64gI4gc4h64h74hR4he4i?4ih4ii4ij4ik4il4im4jV4k?4kR4kS4km4lX4m@4mZ4nN4oB4om50Q51951:51U51V51W51X51Y51Z52`53f54E54F54G54H55055J56K56f57A57o58]59R59m5:Z5;<5;V5<05<X5<Y5<Z5<[5<\5<]5<^5=n5?>5@U5A=5Ae5B?5BY5C15CP5Co5DW5DX5Eb5Fa5H25I15J05K@5LP5Mg5N:5O15Oh5Pf5Q^5R85R95R]5SE5SF5SG5SH5TR5UJ5VS5W\5Xl5Yd5Z\5[75[W5\75\W5]45]J5]g5^D5^a5_>FFS2PPS2PPS2FBS2FBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFFS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2hb3LHBS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2hc3HTc2hb3LHBFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stFFS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB3LOS2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBFS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP3BUF2bs4LFB33LFB3DPB2hb3LHBS2LF2PP3BUF2bs4LFB33LFB3DPB2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHB2HB5Ha_st5Hl_stS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF2PP3CRT2bs4LFB33LFB3D1u2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_stS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHBS2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHBS2LF2PP2bs4LFB33LFB2FB3APP2hb3LHBFFFFSS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFFS2lo3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFFS2sp2lo3sp1S2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2HpS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Hq04Hq0aS2rg3RRg2KzFFFFS2FBS1lFS2FBSFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21p2Hp2q03Lw03Hq04Hq0a4Hq0L2q13Hq14Hq1aS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B34CRT03DXB2D14SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS2FBFS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21p2HpFS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1RFFFFFFS2FBFS2FBSFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX13EX21p2HpFFS3sp1FS2PPFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFFS3CRTS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F02F83APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT2bs2D12FB3sp13D1u4ENDX2q03Lw04Hq0LSFS2FBFFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2HpS1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RS1R3NS14STKc5STKc12sp2PP3CRT3BUF2lo3slo2bs3PP04PPLO4CRT02D14SLOS4SLOL2FB3sp13SP13APP3APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4SP1RFS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOPcFS2sp2PP3CRT3BUF2bs2FB3sp13APBS2sp2PP3CRT3BUF2bs2FB3sp13APBS1R2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_st5SAEst5CM8st2x32HxFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0LS2loS2sp3sp1S2sp2PP3CRT2bs2FB3sp12F0S2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX22q03Lw04Hq0LFSFS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2FBFFFSFFS2FBS1R2sp2PP3CRT2bs3PP04CRT02D12FB3sp13SPR3ACV2F13D1u4SP1RS2FBS2sp2PP3CRT2bs2FB3sp13APPS2FBFFFS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFS2FBS2FBS2FBFFFFSS2FBFFFFS2sp2PP3CRT1P2bs2D12FB3sp13D1u4ENDX1p2HpFFS2sp2PP3CRT2bs2D12FB3sp13D1u2q03Lw03LR0FFFFFFS2FBFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Hq0FFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo3slo2bs3PP04PPLO2B12B22B33DPB4CRT03DXB2D14SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO4SLOu6CRTLOu3D1u4DXBu4SP1R4ENDX3EX21p2HpS2FBS2sp2PP3CRT3END3BUF2bs3PP02B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX2FFS2sp2PP3CRT2bs2FB3sp1FS2sp2PP3CRT2bs2FB3sp12F0FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS1R3NS14STKc5STKc22sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2sp2PP3CRT3BUF2bs3B472FB3sp1S2sp2PP3CRT3BUF2bs3B472FB3sp1S1i2HiFS2rg3RRg2KzS2FBS2FBS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R4ENDX3EX21p2Hp2q03Lw03Hq03LR04Hq0a4Hq0L2q13Hq1FS2FBFFS2sp2PP3CRT2bs2D12FB3sp13D1u2q03Lw02q13Lw14Hq1LS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNS2sp2PP3CRT2bs2D12FB3sp13D1u2rg3RRg2RNFS2FBFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFSFFFFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBFFSS2sp2PP3CRT2lo2bs2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp12hb3LHBS2sp2PP3CRT2lo2bs2FB3sp14FBLOS2sp2PP3CRT2bs2FB3sp13APPFS2LF2bs4LFB33LFB2FB2hb3LHB3x261CS1R2LF2lo2bs4LFB33LFB3LOS2FB3sp13ALO2hb4SBND3LHB3x261CS2LF2bs4LFB33LFB2FB2hb3LHB3x621CS2LF2bs4LFB33LFB2FB2hb3LHB3x621CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2hb4SBND3LHB3x471CS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHB3x471CS2LF2bs4LFB33LFB2FB2hb3LHB3x261CFS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHB3x261CS2LF2bs4LFB33LFB2FB2hb3LHB3x471CFS2LF2lo2bs4LFB33LFB3sp12hb3LHB3x261CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHB3x621CFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2hb4SBND3LHB3x621CS2LF2bs4LFB33LFB2FB2hb3LHB3x471CS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHB3x621CS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHB3x471CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBFFFS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOu2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp13ALO2F12hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3BUF2lo2bs4LFB33LFB3sp15BUFLO2hb3LHBS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB3APB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB3APC2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS2LF2PP2lo2bs4LFB33LFB4PPLO3sp12hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHBS2LF2lo2bs4LFB33LFB2FB3sp14FBLO2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOu2hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2HB5Ha_st5Hl_st5SAEstS1R2LF2PP2bs4LFB33LFB2FB3APP2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB4FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstFFFFFFFS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3BUF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2PP2bs4LFB33LFB2hb3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_stFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2lo2bs4LFB33LFB3LOS3ALO2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBFS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBS1R2LF2PP2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F82hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F82hb3LHBFFFFFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFFS2LF2bs4LFB33LFB2FB2hb3LHBFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HBS2LF3CRT2lo2bs4LFB33LFB6CRTLOu2hb3LHBFFFFFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHB2HBFFS2LF2bs4LFB33LFB2FBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBS2LF2sp2bs4LFB33LFB3sp13SP12hb3LHBFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB4SLOu2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFS2LF2bs4LFB33LFB2FBFFS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FBFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3sp13SP14SLOu2hb3LHBFFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFS2LF2bs4LFB33LFB3sp12hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBFFFFFFFS2LF2bs4LFB33LFB3sp12hb3LHBFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2hb3LHBS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4LFB33LFB4SLOS2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstFFFFS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2HB5Ha_st5Hl_st5SAEstS1R2LF3END3BUF2lo4LFB33LFB1l2B33B473B302FB5BUFLO2hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FB2hb3LHBFFFS2LF2PP2bs4LFB33LFB2hb3LHBS2LF2PP2bs4LFB33LFB2hb3LHBFFS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3ALO4SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3ALO4SLOu2hb3LHBFFS2LF2sp2lo2bs4LFB33LFB3sp13SP12hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12hb5HTOPc3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp12hb5HTOPc3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FBFS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB2FBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stFFFFFS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FBFS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS2LF2bs4LFB33LFB3sp12hb3LHBFFFFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2hb3LHBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBFFFS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1R2hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12HB5Ha_st5Hl_st5SAEstS1R2LF2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB2FB3sp12hb3LHB2HB5Ha_st5Hl_stS2LF2PP2lo2bs4LFB33LFB4PPLO2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFFFFS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT02FB3sp13SPR2F02F84SP1R2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBS2LF2bs4LFB33LFB2FB2hb3LHBS1R2LF2bs4LFB33LFB2FB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF2bs4LFB33LFB2FB2hb3LHB2HBS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2hb3LHB2HB5Ha_st5Hl_stS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2hb3LHBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2hb3LHB2HB5Ha_st5Hl_st5SAEstS2LF2bs4LFB33LFB2FBS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2PP3CRT2lo2bs4LFB33LFB2FB2hb3LHB2HB5Ha_st5Hl_stS2LF2bs4LFB33LFB2FB2hb3LHBFS1R2LF2bs4LFB33LFB2FB2HB5Ha_st5Hl_stS1R2LF3CRT2bs4LFB33LFB2FB2HB5Ha_st5Hl_stFFFS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12hb5HTOPc3LHB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP12hb5HTOPc3LHB2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP12hb5HTOPc3LHBS2LF2bs4LFB33LFB3sp12hb3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB3sp14SP1R2hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F0S2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHBS2LF2bs4LFB33LFB2FB2F02hb3LHB". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R EX1 EX2"] Lemma body_walk : forall p, P <= p < ENDX -> (forall p', p < p' -> p' < ENDX -> LoopOblig p') -> LoopOblig p.
  Proof.
    intros p Hp KLOOP. unfold LoopOblig. intros until x31. intros INV HPP HBUD.
    open_xinv_mu INV hc.
    (* [comment removed for export] *)
    do 7 zstep.
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
    pose proof (artA_amemset asegs R HIA 0x67ce4) as SPM.
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
    do 10 zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "04\0@D10651567411.270D10836317929.302D12656313659.302D13253490115.270D17704051241.270D24128083136.302D27806942224.308D27806942224.309D32454803565.302D3267863928.302 D35883161687.302D3883966340.302 D39256548052.302D52043936183.302D54246127327.302D56896494561.270D59473897855.304D60189065437.308D60189065437.309D6205886729.302 D68411668694.302D6899608275.302 D903115207.302  L10178881292.7  L10549786651.2  L1056244802.71  L10837002389.2  L1103920410.2   L1107925502.296 L1107965600.297 L11311055387.2  L11668953649.261L12126572370.2  L12654381620.1  L12729978778.2  L13000859167.71 L13238797400.71 L14115679076.3  L14402535660.294L14402535660.3  L14662949908.71 L1530387784.71  L15846663084.71 L16482024986.2  L1685717371.0   L17225908493.1  L19965341035.71 L20038394650.2  L20977711877.2  L21555046091.71 L22932634144.73 L23581863231.2  L24882004373.71 L25271426382.16 L25632820001.0  L2586398799.3   L26375085850.2  L27325864010.71 L27786096167.113L27796237965.71 L28090575245.1  L28632618922.2  L29241073293.1  L29813167690.296L30507144274.2  L30997223346.3  L31873504466.71 L3241370779.2   L32604013069.1  L32896879501.295L32951616581.4  L33685467802.2  L3480690494.71  L35655538625.72 L35822393883.2  L35905690340.71 L36035727278.2  L36963958045.2  L38056808157.3  L38235734261.1  L38259954321.2  L40228640085.0  L41112523164.71 L41202929119.261L41202929119.296L41334146114.2  L41755152410.2  L4196854811.2   L43519627435.2  L43892210075.2  L44166924249.3  L45311526170.2  L46743867632.71 L46868055498.296L51201023259.2  L51489524058.71 L51500665912.16 L52067411348.297L52758021441.71 L54318674701.1  L56902789754.71 L57037598615.71 L57628700040.4  L57692209838.320L57698627611.2  L58987451370.71 L6008603173.3   L60672126733.1  L61286871247.71 L61638990714.296L61639226404.297L62081227363.4  L64850595401.0  L65110679799.3  L65378998541.1  L65529229965.295L65862516566.2  L67070089790.2  L6713521051.8   L6798276507.2   L7330750477.1   L7696713571.3   L7753760539.2   L9090702513.71  L9190709528.5   L9397308949.7   L9817097297.261 P1043593561.302 P10540088028.308P10540088028.309P1106161799.302 P11322327260.308P11322327260.309P12115299733.308P12115299733.309P12732252679.302P16479777671.302P18391008132.302P19974019408.302P20036415111.302P20977680014.302P23095784836.302P26376999559.302P26652418180.302P28627113325.308P28627113325.309P30997907918.302P3252643420.308 P3252643420.309 P32814192132.302P33687453447.302P35832092892.308P35832092892.309P36964055190.302P38056382625.302P38261788758.308P38261788758.309P41334243785.302P41757433223.302P4207603420.308 P4207603420.309 P43677085060.302P43901909852.308P43901909852.309P44164039966.308P44164039966.309P45313542279.302P48371079044.302P51191324636.308P51191324636.309P51927712388.302P57713046236.308P57713046236.309P65862482653.302P6809023836.308 P6809023836.309 P7763983836.308 P7763983836.309 P8676795140.302 Q10048380702.305Q10649389620.269Q10649498890.305Q10651584438.304Q1106161799.302 Q11282309114.305Q12555692702.305Q12732252679.302Q12933971006.305Q13193308734.305Q13551006110.305Q13732682891.304Q14117173214.302Q1523115505.304 Q15985628819.304Q16479777671.302Q17376785489.304Q17701933584.305Q17722859966.305Q18567054366.305Q19559354218.302Q19576581790.305Q20036415111.302Q20977680014.302Q23583809698.302Q23831245502.305Q23893370942.304Q24281037434.305Q24592544158.305Q24852143294.305Q25585260574.304Q25587739552.306Q25816364734.305Q2584186101.302 Q25952160488.307Q25952160488.308Q26376999559.302Q26481470270.305Q28465177121.305Q28465177121.306Q28814963518.305Q29516740158.305Q30506752203.302Q30602945310.305Q30997907918.302Q31613498782.304Q32681824661.308Q32681824661.309Q33687453447.302Q33813839279.305Q33839800254.305Q35702454078.305Q36630502558.305Q36964055190.302Q37288026488.305Q37638973214.305Q37820510782.305Q38056382625.302Q38833220926.305Q38910192916.304Q39180574961.308Q39180574961.309Q39600066516.305Q39824755247.305Q40916972731.305Q41334243785.302Q41757433223.302Q42439443119.308Q42439443119.309Q42639330846.305Q43517348881.302Q43649290398.305Q44328945726.305Q44847628683.304Q44858487396.304Q44860571864.305Q44949809470.305Q45313542279.302Q45353866761.304Q45356129163.269Q45741809296.308Q45741809296.309Q47387953854.305Q48667442078.305Q49746415830.308Q49746415830.309Q50449559544.305Q50869415908.304Q50871508312.305Q50883927051.304Q51221331390.304Q51223105024.306Q519278494.305  Q5265442331.306 Q5265442331.307 Q53799279550.305Q53839787668.304Q5411072626.302 Q54692959518.305Q55415036769.308Q55415036769.309Q59578101107.304Q60191312605.307Q60191312605.308Q60668057790.305Q60703360670.305Q61018498547.304Q61847600945.305Q6205886729.302 Q63211573790.305Q64171619443.304Q6530087198.305 Q65862482653.302Q66459454699.302Q67038978349.308Q67038978349.309Q67068921476.302Q7538590622.305 Q8699115497.308 Q8699115497.309 Q9631868565.302 00000Q01601[02<02]03>04`06D06e06f06g06h06i07N07o08P0960:`0<L0<m0<n0=O0=P0=g0=h0>E0>M0>N0@P0BR0BS0DB0DC0DH0DI0F?0FT0FU0FV0Fa0HW0I00IR0IS0IT0IY0KF0KG0KH0Kf0LI0LJ0Lh0M80M90M:0M;0O30O40O50O:0O;0O@0Oa0Ob0Oc0QC0QD0QI0Rc0S10S20TT0VF0VG0Vd0Vm0Vn0Vo0W30W40W50WR0X30XT0XU0XV0XW0XX0XY0XZ0X[0Y30YT0YU0[60[K0[L0[j0[o0\D0^>0^K0_R0_S0`00`;0`@0`U0bY0d^0dk0dl0e60e;0fU0fV0fW0g00g10g60g@0gA0g]0h00hG0j60jU0kj0mA0m\0o110H11Z13213M13h14g15I15d16>17=17X18W19l1;L1;g1=<1>S1?R1?m1AB1BY1C41CQ1D`1F51FP1Fk1H@1IW1JV1Kk1MB1NV1P01PK1QJ1R_1T61U51Uf1V]1W71XL1Yc1[81\O1]N1^F1^Y1^l1_?1_@1_T1`L1`M1a:1ag1b_1c21cn1df1dg1dh1eU1eh1fU1gM1h81i01i11i21ii1jV1kC1kW1lO1m<1n41nl1oY20X21[22d22e23R23n24J25725d26X27P27Q28I28J28K28L28M29:29g2:_2:`2;Z2<R2=?2=@2=m2>A2?S2@k2@l2@m2@n2@o2A02Ae2B`2CX2DW2EO2F<2FP2Fd2G82Ge2Gf2H92HL2HM2HN2I;2J32K22L72M12ME2MY2Mm2NZ2OG2P?2P\2Q92Qf2R:2RN2SF2T72Tn2UF2VT2Wh2XU2YM2Ya2Z[2Zo2[g2\;2]32]42]a2^o2`C2a?2b72c>2dK2daS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT3BUF2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2h25Ehtop2HB5Ha_st5Hl_st3a4eS1R3HIA1h2LF2sp2PP3CRT2bs4LFB33LFB3PP04CRT03TOP2FB3sp13SP13SPR2F04SP1R2h25Ehtop2HB5Ha_st5Hl_st3len1qS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SP1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp11x2HxS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_st3a4eS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R2HB5Ha_st5Hl_st3len1qS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS1R3HIA4PHIx1h1P3END2PXFS2sp2PP3CRT2lo2bs4PPLO2FB3sp1S3BUF2bsFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R2p23len1q3Hp23Hq14Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R2p23len1q3Hp23Hq14Hp2aFS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1RFS3BUFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B34CRT03DXB2D13SPH2FB3sp13SPR3ACV2F02F14SLOu3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp1FFS2rg3Hrg2KrS1R4STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2sp2PP3CRT2bs2FB3sp13SP1S2sp2PP3CRT3BUF2lo2bs2FB3sp15BUFLOFSS3CRTS1R3HIA1h2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBu4SP1RFFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2sp2PP3CRT2bs2D12FB3sp13D1u2rg3HrgFS2sp2PP3CRT2lo2bs5CRTLO2FB3sp1S2bs2p23len1q2KlSFFS1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP04PPLO2B12B22B33DPB4CRT02D13SPH2FB3sp13SPR3ACV2F02F14SLOu6CRTLOu3D1u4SP1RFFS3CRTFS3CRTS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D13SPH2FB3sp13SP13APP3APC3SPR2F03APB3D1u4DXBuFS3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RS1P3END2p23Hp2FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp14SP1M3APP3APC3SPR2F03APB3D1u4DXBu4SP1RS1R3HIA1h2sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D13TOP2FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1R5HTOP1FS2sp2PP3CRT3BUF2bs3DXB2FB3sp1S2LF4LFB3FFS2loFSS2sp2PP3CRT3BUF2bs3DPB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FFFFFFFS2sp2PP3CRT2bs2D12FB3sp1S2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp1FS2sp2PP3CRT1P3END3BUF2bs3PP02B12B22B33DPB3ALC4CRT03DXB2D12FB3sp13APP3APC3SPR2F03APB3D1u4DXBu4SP1RS2bs2p23len1q4Hp2a2KlFS2sp2PP3CRT1P3END2bs2B22FB3sp1S3CRTS2sp2PP3CRT2bs2FB3sp1S1R3NS14STKc5STKc12sp2PP3CRT1P3END3BUF2lo2bs3PP02B12B22B33DPB4CRT03DXB2D12FB3sp13SP13APP3APC3SPR2F03APB4SLOu3D1u4DXBu4SP1RS2PP3CRT1x2HxS1R3HIA4PHIx4FFRx4CNTx1h2LF2sp2PP3CRT1P2bs4LFB33LFB1d2FB3sp12p21H2H02H1FS2sp2PP3CRT3BUF2bs3B472FB3sp1S2rg3Hrg2KrS3CRTS2sp2PP3CRT2bs2FB3sp1S1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R2p23len1q3Hq15Hqlen4Hp2aS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R2p23len1q3Hp23Hq14Hp2a2E2S3len1q2p22PLSS1P3END2B2S3CRTS1R3NS14STKc5STKc12LF2sp2PP3CRT2lo2bs4LFB33LFB3PP04CRT03SPH2FB3sp13SPR2F04SLOu6CRTLOu4SP1RFFS1R3HIA4FFRx1h1P3END1d2FXFS3CRTS1R3HIA2h1FS2sp2PP3CRT2lo2bs2FB3sp13SP1S1P3len1q3Hq15Hlen0S1P3END3len1q2p23Hp22PLS1R3NS14STKc5STKc12LF2sp2PP3CRT1P3END3BUF2lo2bs4LFB33LFB3PP02B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1RS2LF2PP2lo2bs4LFB33LFB4PPLO3sp1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRT3len1qS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF3CRT2lo2bs4LFB33LFB3sp16CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2HB5Ha_st5Hl_st3a4eS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO2F14SLOu2HB5Ha_st5Hl_st3CRT4FBLO3len1qS2LF2PP3BUF2bs4LFB33LFB3DPBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS2LF3CRT2bs4LFB33LFB2FB3APCS2LF3CRT3BUF2bs4LFB33LFB4DXBuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st3a4eS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB2FB3sp13SP14FBLO4SLOu2HB5Ha_st5Hl_st3CRT3len1qS2LF3CRT2bs4LFB33LFB2FB3APCS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3BUF2lo2bs4LFB33LFB2FB3sp13SP15BUFLO4SLOu2HB5Ha_st5Hl_st3CRT3len1qS2LF2PP3CRT2bs4LFB33LFB3D1uS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_st3a4e2FBS2LF2sp2bs4LFB33LFB2FB3sp13SP12HB5Ha_st5Hl_st3CRT3len1qS2LF2PP2bs4LFB33LFB2FB3APPS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB2FB3sp13SP14SLOu6CRTLOu2HB5Ha_st5Hl_st3len1qS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFS2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2PP2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF2PP2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2sp2PP3CRT2bs4LFB33LFB2FB3sp13SPR2F02F8S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB4SLOu6CRTLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP12HB5Ha_st5Hl_st3a4e2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp13SP15HTOP12HB5Ha_st5Hl_st3CRT3len1qFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF2bs4LFB33LFB3sp14SP1R2HBS2LF2bs4LFB33LFB3sp14SP1R2HBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO4SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFFFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1FS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP13ALO4SLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP13ALO4SLOu2HB5Ha_st5Hl_st3CRT3len1qFFFFFS1R2LF3slo2bs4LFB33LFB4SLOS3sp12HB5Ha_st5Hl_st3a4e2FBS1R2LF3slo2bs4LFB33LFB4SLOS2FB3sp12HB5Ha_st5Hl_st3CRT3len1qS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB33LFB3sp13SP14SLOu6CRTLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1FS2LF2PP2bs4LFB33LFBS2LF2PP2bs4LFB33LFBFFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp15HTOP12HB5Ha_st5Hl_st3a4e2FBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2FB3sp15HTOP12HB5Ha_st5Hl_st3CRT3len1qS2LF2sp2PP3CRT2bs4LFB33LFB3PP03ALC4CRT02FB3sp13SPR2F04SP1RS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS2LF3CRT2bs4LFB33LFBS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2bs4LFB33LFB3sp12HB5Ha_stS2LF2bs4LFB33LFB3sp12HB5Ha_stS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S2LF3CRT2bs4LFB33LFBS2LF2bs4LFB33LFB3sp1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF2sp2bs4LFB33LFB3sp13SP12HB5Ha_st5Hl_st3a4e2FBS2LF2sp2bs4LFB33LFB2FB3sp13SP12HB5Ha_st5Hl_st3CRT3len1qS2LF2bs4LFB33LFB2FB1c2HcS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRT3len1qS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP3sp13SP15HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF3CRT2bs4LFB33LFBS2LF2sp2PP3CRT2bs4LFB33LFB3ALP3PP04CRT02FB3sp13SPR2F04SP1RS2LF2bs4LFB33LFB3sp1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS2LF3CRT2bs4LFB33LFBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuFS1R3HIA1h2LF2sp2bs4LFB33LFB3TOP2h14Estk5HTOP1S1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOu2HB5Ha_st5Hl_st3a4e2FBS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS2FB3sp13SP14SLOu2HB5Ha_st5Hl_st3CRT3len1qS1R3NS14STKc5STKc12LF2sp2PP2lo2bs4LFB33LFB4PPLO3sp13SP14SLOuS1R3NS14STKc5STKc12LF2sp2lo2bs4LFB33LFB3LOS3sp13SP14SLOuS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP3sp13SP15HTOP12HB5Ha_st5Hl_st3a4e2FBS1R3HIA1h2LF2sp3slo2bs4LFB33LFB3TOP2FB3sp13SP15HTOP12HB5Ha_st5Hl_st3CRT3len1qS2LF2bs4LFB33LFB2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 AMS NA1 DIMG HMND GT GB OIDH GETEXT BASIC KUSE SKID NSCT PHIq PHIs PHIp PHIk FFRq FFRs FFRp FFRk CNTq CNTs CNTp CNTk STKq STKs STKp STKk SEQOF GSAN GPOL AKID STKc1 STKc2 STKc3 STKcq STKcs STKcp STKck PHIx0 FFRx0 CNTx0 PHIx_mono FFRx_mono CNTx_mono PHIx_sadd FFRx_sadd CNTx_sadd PHIq_le FFRq_le CNTq_le PHIs_le FFRs_le CNTs_le PHIp_le FFRp_le CNTp_le PHIk_le FFRk_le CNTk_le LFB3 LFB ALP PP0 CWP PPLO BIN B1 B2 B3 B47 B5 B30 DPB ALC CRT0 CWX CRTLO DXB D1 SLOS SLOL SLO TOP SPA SPH TPV LOS UW BUDV BUDF SP1 SP1M F64 FRSH CFB APP APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB SLOu CRTLOu D1u DXBu SP1R"] Lemma hdr_walk : forall (h1 : HST asegs R HIA) (m1 : mem) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (w0 w1 w2 : word)
           (jloc ja jb : list byte) (k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k128 k136 k144 k152 k160 k168 k176 k184 : word),
      HM asegs R HIA h1 LB ((FB, 256) :: LF) m1 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h
      -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h
      -> havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h
      -> rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      -> rw_cells asegs m1 (FB + 32) [CB 216 jloc]
      -> rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHX
      -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL
      -> rw_cells asegs m1 sp1 [CB 16 ja; C8 k16; C8 k24; C8 k32; C8 k40; C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88; C8 k96; C8 k104; C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 k152; C8 k160; C8 k168; C8 k176; C8 k184; CB 16 jb; C8 (Z_to_bv 64 FB)]
      -> stk asegs m1 (sp1 + 216) (bv_unsigned sp + -104) -> stk asegs m1 lo sp1 -> mem_inv asegs m1
      -> rw_cells asegs m1 PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m1 (CRT + 424) [CB 272 (zeros 272)] -> bytes_at asegs m1 BUF bs
      -> aobj asegs AL CS m1 PP 8 -> aobj asegs AL CS m1 (CRT + 424) 272 -> aobj asegs AL CS m1 BUF n
      -> presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m1
      -> sshad asegs AL m1 slo sp1 -> sshad asegs AL m1 sp1 (bv_unsigned sp) ->
    aevtA asegs (KF asegs R HIA h1 mo0) POST
      (MS (mkR (Z_to_bv 64 0x0a9ef8) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FB) (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
                   (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) a4e (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) x28 x29 x30 x31)
              F (Z_to_bv 64 0x0a9fd0) fc None m1 (seg_rom asegs)).
  Proof.
    intros until k184. intros HH1 Ehcs Ehtop Estk Eflag Evol Efr FHD FLOC0 FSH SAVE RSL SThi STlo MI1 HPP1 HEXT1 HB1 OPP1 OEXT1 OBUF1 PRES SS1 SS2.
    rewrite <- Ehcs in OPP1, OEXT1, OBUF1.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m1 PRES HCS1 Estk) as PRES1. clear PRES.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    (* [comment removed for export] *)
    assert (FINX : forall (hq : HST asegs R HIA) (mx : mem) (r p' : Z) (X : xst) (ja' jb' : list byte)
                     (c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 : word)
                     (yra y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 t3v t6v t8v t9v t10v t11v y28 y29 y30 y31 : word),
               HM asegs R HIA hq LB LF' mx -> (forall x, CS x -> hcs asegs R HIA hq x) -> htop asegs R HIA hq = htop asegs R HIA h ->
               hstkhi asegs R HIA hq = hstkhi asegs R HIA h -> hflag asegs R HIA hq = hflag asegs R HIA h ->
               havol asegs R HIA hq = havol asegs R HIA h -> hfr asegs R HIA hq = hfr asegs R HIA h ->
               rw_cells asegs mx FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mx (Z.shiftr FB 3 + al_sb AL) FSHX ->
               rw_cells asegs mx (bv_unsigned sp + -104) SAVEL ->
               rw_cells asegs mx sp1 [CB 16 ja'; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; C8 c104; C8 c112; C8 c120; C8 c128; C8 c136;
                                      C8 c144; C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; CB 16 jb'; C8 (Z_to_bv 64 FB)] ->
               stk asegs mx (sp1 + 216) (bv_unsigned sp + -104) -> stk asegs mx lo sp1 -> mem_inv asegs mx ->
               presW asegs R HIA hq LB LF (bv_unsigned sp) (bv_unsigned sp) W m mx ->
               sshad asegs AL mx slo sp1 -> sshad asegs AL mx sp1 (bv_unsigned sp) ->
               rw_cells asegs mx PP [C8 (Z_to_bv 64 p')] -> P <= p' <= END ->
               xcells asegs CRT mx X -> xown asegs mx LB X -> xblocks X = [] -> -2^31 < r <= 0 ->
               aevtA asegs (KF asegs R HIA hq mo0) POST
                 (MS (mkR yra (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 FB) t3v (Z_to_bv 64 r) (Z_to_bv 64 FB) t6v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t8v t9v t10v t11v y28 y29 y30 y31)
                     F (Z_to_bv 64 0x0aa4f4) fc None mx (seg_rom asegs))).
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
    do 5 zstep.
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
    replace (ret_pc (Z_to_bv 64 0xa9fec)) with (Z_to_bv 64 0xa9fec : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
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
    do 19 zstep.
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
    do 20 zstep.
    idtac "HDR-B".
    do 18 zstep.
    idtac "HDR-C".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
    match goal with H : rw_cells _ ml (FB + 32) [CB 216 _] |- _ => destruct (floc_of_junk asegs ml (FB + 32) _ H) as (lenw & otg & opd & olen & op & crit & et & j1 & j2 & j3 & j4 & FLOCl); clear H end.
    assert (INV : xinv (q + len) [] ml h2 (xst_v3 tg (Z_to_bv 64 0) len q) (FLOC lenw j1 otg opd olen op j2 crit j3 et j4) FSHX w0 w1 w2 k16 ja jb).
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
                   & jloc & ja & jb & k16 & k24 & k32 & k40 & k48 & k56 & k64 & k72 & k80 & k88 & k96 & k104 & k112 & k120 & k128 & k136 & k144 & k152 & k160 & k168 & k176 & k184
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
