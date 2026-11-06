(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo
     A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_get_san_A A_crt_parse_stmt24 A_crt_free_stmt2 A_pkcs7_free A_x509_crt_free A_x509_crt_parse_area A_x509_crt_parse_A A_x509_crt_parse_B A_x509_crt_parse_C
     A_asn1_get_int_loops A_x509_get_serial A_x509_get_alg A_x509_get_sig_alg A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_dates_A A_pk_parse_stmt A_x509_get_uid
     A_x509_crt_ext_stmt A_x509_crt_ext_A A_x509_get_sig_A.
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
  Hypothesis SM3 : arl_smalloc R 3 = 0x52e24.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_crt_parse_A.STKx R STKc).
  Hypothesis SF5 : arl_setf5 R = 0x6adbc.
  Hypothesis NSH0 : 0 <= arl_need_setsh R.
  Hypothesis STKc4 : arl_need_setsh R <= STKc.

  Hypothesis AMS : arl_amemset R = 0x67ce4.
  Hypothesis AMC : arl_amemcpy R = 0x67848.
  Hypothesis ACAL : arl_calloc R = 0x68f10.
  Hypothesis ABCMP : arl_memcmp_i R = 0x58190.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis NM1 : 0 <= arl_need_malloc R.
  Hypothesis NF1 : 0 <= arl_need_free R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.   (* [comment removed for export] *)
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).   (* [comment removed for export] *)
  Variable PK : pk_class asegs.
  Variable SI : sinv L.
  (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
  Hypothesis SERIAL : x509_get_serial_stmtA asegs AL A_X509_GET_SERIAL.
  Hypothesis XALG : x509_get_alg_stmtA asegs R HIA A_X509_GET_ALG.
  Hypothesis SIGALG : x509_sig_alg_stmtA asegs R HIA A_X509_GET_SIG_ALG.
  Hypothesis DATES : x509_get_dates_stmtA asegs R HIA A_X509_GET_DATES.
  Hypothesis UID : x509_get_uid_stmtA asegs AL A_X509_GET_UID.
  Hypothesis GETSIG : x509_get_sig_stmtA asegs R HIA A_X509_GET_SIG.
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z) (STKn : Z).
  Hypothesis GETNAME : x509_get_name_stmtE asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Variables (PHIk : Z -> Z) (FFRk : Z -> Z -> Z) (CNTk : Z) (STKk : Z) (C24k : Z).
  Hypothesis PKPARSE : pk_parse_subpubkey_stmtA asegs R HIA PK SI PHIk FFRk CNTk STKk C24k 0xaefd8.
  Variables (PHIx : Z -> Z) (FFRx : Z -> Z -> Z) (CNTx : Z -> Z) (STKxx : Z).
  Hypothesis CRTEXT : x509_crt_ext_stmtA asegs R HIA PHIx FFRx CNTx STKxx (LFMAX_CRT + 3) A_X509_CRT_EXT.
  Variables (PHIcf : Z -> Z) (FFRcf : Z -> Z -> Z) (STKcf : Z).
  Hypothesis CRTFREE : x509_crt_free_stmtA2 asegs R HIA PK PHIcf FFRcf STKcf A_X509_CRT_FREE.
  (* [comment removed for export] *)
  Hypothesis STKc1 : X509_SIG_ALG_STACK_A + 128 <= STKc.
  Hypothesis STKc2 : arl_need_amem R + 480 <= STKc.
  Hypothesis STKc3 : arl_need_bcmp R + 400 <= STKc.
  Hypothesis STKc5 : arl_need_malloc R + 64 <= STKc.
  Hypothesis STKc6 : arl_need_free R + 64 <= STKc.
  Hypothesis STKcn : STKn <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKck : STKk <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKcx : STKxx <= STKc + 48 + arl_need_smalloc R.
  Hypothesis STKcfr : STKcf <= STKc + 48 + arl_need_smalloc R.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Hypothesis PHIj0 : forall a, 0 <= a -> 0 <= PHIj a.
  Hypothesis FFRj0 : forall a e, 0 <= a -> 0 <= FFRj a e.
  Hypothesis CNTj0 : forall a, 0 <= a -> 0 <= CNTj a.
  Hypothesis PHIj_mono : forall a b, 0 <= a <= b -> PHIj a <= PHIj b.
  Hypothesis FFRj_mono : forall a b e, 0 <= a <= b -> FFRj a e <= FFRj b e.
  Hypothesis CNTj_mono : forall a b, 0 <= a <= b -> CNTj a <= CNTj b.
  Hypothesis PHIj_sadd : forall a b, 0 <= a -> 0 <= b -> PHIj a + PHIj b <= PHIj (a + b).
  Hypothesis FFRj_sadd : forall a b e, 0 <= a -> 0 <= b -> FFRj a e + FFRj b e <= FFRj (a + b) e.
  Hypothesis CNTj_sadd : forall a b, 0 <= a -> 0 <= b -> CNTj a + CNTj b <= CNTj (a + b).
  Hypothesis PHIn_le : forall a, 0 <= a -> PHIn a <= PHIj a.  Hypothesis FFRn_le : forall a e, 0 <= a -> FFRn a (e + 1) <= FFRj a e.  Hypothesis CNTn_le : forall a, 0 <= a -> CNTn a <= CNTj a.
  Hypothesis PHIx_le : forall a, 0 <= a -> PHIx a <= PHIj a.  Hypothesis FFRx_le : forall a e, 0 <= a -> FFRx a (e + 1) <= FFRj a e.  Hypothesis CNTx_le : forall a, 0 <= a -> CNTx a <= CNTj a.
  Hypothesis PHIk0 : forall a, 0 <= a -> 0 <= PHIk a.
  Hypothesis FFRk0 : forall a e, 0 <= a -> 0 <= FFRk a e.
  Hypothesis CNTk0 : 0 <= CNTk.
  Hypothesis PHIk_mono : forall a b, 0 <= a <= b -> PHIk a <= PHIk b.
  Hypothesis FFRk_mono : forall a b e, 0 <= a <= b -> FFRk a e <= FFRk b e.
  Hypothesis PHIcf0 : forall k, 0 <= k -> 0 <= PHIcf k.
  Hypothesis FFRcf0 : forall k e, 0 <= k -> 0 <= FFRcf k e.
  Hypothesis PHIcf_mono : forall a b, 0 <= a <= b -> PHIcf a <= PHIcf b.
  Hypothesis FFRcf_mono : forall a b e, 0 <= a <= b -> FFRcf a e <= FFRcf b e.
  Variable C24c : Z.
  Hypothesis C24c1 : C24k + 1 <= C24c.
  Hypothesis C24k0 : 0 <= C24k.

  (* [comment removed for export] *)
  Definition CNTc (n : Z) : Z := 2 + CNTk + CNTj n.
  Definition KVc (n : Z) : Z := (2 * n + AVOL_CALL) + X509_SIG_ALG_PHI + PHIk n.
  Definition KFc (n d : Z) : Z := Z.max 0 (fr_charge (d + 1)) + Z.max 0 (X509_SIG_ALG_FFR 0) + FFRk n (d + 1).
  Definition PHIc (n : Z) : Z := KVc n + PHIj n + PHIcf (CNTc n).
  Definition FFRc (n d : Z) : Z := KFc n d + FFRj n d + FFRcf (CNTc n) 0.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (CRT Q blen BUF lo slo : Z) (bs : list byte) (WS : list ivl).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB2 : (length LF <= LFMAX_CRT + 2)%nat.
  Let LFB : (length LF < 511)%nat.
  Proof. eapply Nat.le_lt_trans; [exact LFB2|]. unfold LFMAX_CRT. apply Nat.ltb_lt. reflexivity. Qed.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= Q. Hypothesis B2 : 0 <= blen. Hypothesis B3 : Q + blen <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CRT 744.
  Hypothesis CRTLO : CRT + 744 <= lo.
  Hypothesis DXB : CRT + 744 <= BUF \/ BUF + n <= CRT.
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
    unfold A_UAR_GOT in UARG; unfold A_x509_crt_parse_A.STKx in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := ((CRT, CRT + 744) :: WS).
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  Local Notation FSHP := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.


  Variable mo0 : Model.
  Variable d : Z.
  Hypothesis NDL : List.NoDup (map fst LB).
  Hypothesis B30 : n < 2^30.
  Hypothesis BAM : blen < AMAX.
  Hypothesis DCD : CRT + 744 <= hl_data_lo L \/ hl_data_hi L <= CRT.

  Local Notation WSI := ((CRT, CRT + 744) :: si_fp SI).
  Local Notation POST := (x509_crt_parse_der_postA24 asegs R HIA PK SI PHIc FFRc CNTc h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            CRT blen lo slo d m mo0).
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis BUDV : havol asegs R HIA h + PHIc blen <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRc blen d <= FR_MAX.
  Hypothesis BUD24 : cnt24 LB + 2 * (blen / 5889) + C24c <= C24MAX.

  Section Body.
  Variables (FB sp1 : Z).
  Hypothesis SP1 : bv_unsigned sp - 272 <= sp1 <= bv_unsigned sp - 256.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 512.
  Hypothesis CFB : crange CS FB 512.
  Hypothesis APC : FB + 512 <= CRT \/ CRT + 744 <= FB.
  Local Notation LF' := ((FB, 512) :: LF).
  Hypothesis BUFLO : BUF + n <= lo.
  Let SPR : 0 <= bv_unsigned sp < 2^64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn [Z.pow Z.of_N Pos.pow] in H. exact H. Qed.
  Let ALO : alloc_ceiling <= arl_stklo R := art_lo asegs R HIA.
  Let ACV : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 := alloc_ceiling_val R.
  Let F0 : 0 < FB. Proof. exact (proj1 FRSH). Qed.
  Let F1 : FB + 512 <= alloc_ceiling. Proof. exact (proj1 (proj2 FRSH)). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L55831167499.16800001JS1R2LF2sp3CRT4blen3BUF2lo3slo2bs4LFB23LFB2B24CRT05CRTLO4SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0". (* [comment removed for export] *)
  Let FBLO : FB + 512 <= lo. Proof. pose proof F1. pose proof ALO. pose proof LOS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L66149329409.20900000YS2LF2bs4LFB23LFB2FB2r11H1q1r2H02H12q13H10". (* [comment removed for export] *)
  Let F8 : FB mod 8 = 0. Proof. pose proof F64. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Let APB : FB + 512 <= BUF \/ BUF + n <= FB. Proof. apply (proj2 (proj2 (proj2 FRSH))). apply in_app_iff. left. exact BIN. Qed.
  Let FDD : FB + 512 <= hl_data_lo L \/ hl_data_hi L <= FB. Proof. exact (proj1 (proj2 (proj2 FRSH))). Qed.
  Let SLOu : lo <= bv_unsigned sp - (272 + 48 + STKc + arl_need_smalloc R). Proof. exact SLO. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L9354819225.17800001VS1R4STKc3NA15STKc22LF2sp3CRT4blen2lo3slo2bs4LFB23LFB2B24CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4". (* [comment removed for export] *)
  Let SP1R : 0 <= sp1 < 2^64.
  Proof. pose proof SLO as S. unfold A_x509_crt_parse_A.STKx in S. pose proof SPR. pose proof SP1. pose proof LOS. pose proof ALO. pose proof ACV. pose proof NS1. pose proof STKc0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Let LFB3 : (length LF' <= LFMAX_CRT + 3)%nat. Proof. cbn [length]. pose proof LFB2 as H. unfold LFMAX_CRT in *. apply le_n_S. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L19393915969.17700001NS1R4STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23SPH2FB3sp13SPR3ACV2F02F14SP1R4LFB31H2H02H2". (* [comment removed for export] *)
  Let CRB : CRT + 744 <= 2^64. Proof. pose proof CRTLO. pose proof SLOu. pose proof SPR. pose proof NS1. pose proof STKc0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Tactic Notation "xl" hyp_list(Hs) :=
    (clear - Hs B1 B2 B3 B47 B5 B30 BAM DXB ALC CRT0 CRTLO SLO SLOS SLOL TOP SPA SPH SP1 SP1M F64 APC NS1 NA1 NB1 NM1 NF1 NSH0 STKc0 STKc1 STKc2 STKc3 STKc4 STKc5 STKc6
               STKcn STKck STKcx STKcfr BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SP1R LOS SLOu CRB DCD);
    unfold A_x509_crt_parse_A.STKx, X509_SIG_ALG_STACK_A, EXT_SIZE, SEQ_SIZE, NAME_SIZE, CRT_SIZE in *; first [lia | Z.div_mod_to_equations; lia].

  (* [comment removed for export] *)
  
  Local Notation RSLX k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ja jb :=
    [CB 24 ja; C8 k24; C8 k32; C8 k40; C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88; C8 k96; C8 k104; C8 k112; C8 k120; CB 16 jb; C8 (Z_to_bv 64 FB)].
  (* [comment removed for export] *)
  Local Notation WMU := [(CRT, CRT + 744); (FB, FB + 512); (lo, bv_unsigned sp); (Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 64)].

  (* [comment removed for export] *)
  Definition cinv (Lc : list blk) (mm : mem) (hc : HST asegs R HIA) (fsh : list cell) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 : word) : Prop :=
    HM asegs R HIA hc (Lc ++ LB) LF' mm
    /\ (forall x, CS x -> hcs asegs R HIA hc x) /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h
    /\ hflag asegs R HIA hc = hflag asegs R HIA h
    /\ rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2]
    /\ rw_cells asegs mm (FB + 32) [C8 lv] /\ rw_cells asegs mm (FB + 64) [C8 len] /\ rw_cells asegs mm (FB + 96) [C8 (Z_to_bv 64 p)]
    /\ rw_cells asegs mm (FB + 128) [C4 a1; C4 a2; C8 a3; C8 a4] /\ rw_cells asegs mm (FB + 192) [C4 b1; C4 b2; C8 b3; C8 b4]
    /\ rw_cells asegs mm (FB + 256) [C4 c1; C4 c2; C8 c3; C8 c4]
    /\ rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) fsh
    /\ rw_cells asegs mm (bv_unsigned sp + -104) SAVEL
    /\ rw_cells asegs mm sp1 (RSLX k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ja jb)
    /\ stk asegs mm (sp1 + 152) (bv_unsigned sp + -104) /\ stk asegs mm lo sp1 /\ mem_inv asegs mm
    /\ aobj asegs AL (hcs asegs R HIA hc) mm CRT 744
    /\ presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) WSI m mm
    /\ sshad asegs AL mm slo sp1 /\ sshad asegs AL mm sp1 (bv_unsigned sp)
    /\ si_P SI mm.

  (* [comment removed for export] *)
  Definition BUD (hc : HST asegs R HIA) (Lc : list blk) (kv kf kc a : Z) : Prop :=
    havol asegs R HIA hc <= havol asegs R HIA h + kv + PHIj a
    /\ hfr asegs R HIA hc <= hfr asegs R HIA h + kf + FFRj a d
    /\ Z.of_nat (length Lc) <= kc + CNTj a.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L15754108151.185L2846347945.183 L29784460291.182L32500001528.191L33826088087.191L35497642355.182L46044078932.191L8518889475.182 00001Y02D02o03a05R06=06o07\S1R2LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB23LFB2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR2F03APB4SP1R4LFB31HS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB3S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB3S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB31x1k2A2S1R2LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB23LFB2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR2F03APB4SP1R4LFB31x1k3Bce1HS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB3S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB31x1k2A3S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB3". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 DIMG STKc2 sp Q blen BUF slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CWX DXB SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma own_apart : forall (hc : HST asegs R HIA) Lc mq x k, HM asegs R HIA hc (Lc ++ LB) LF' mq -> (forall y, CS y -> hcs asegs R HIA hc y) -> In (x, k) Lc -> 0 < k ->
    (x + k <= CRT \/ CRT + 744 <= x) /\ (x + k <= FB \/ FB + 512 <= x) /\ x + k <= lo
    /\ (x + k <= Z.shiftr FB 3 + al_sb AL \/ Z.shiftr FB 3 + al_sb AL + 64 <= x)
    /\ (x + k <= hl_img_lo L \/ hl_img_hi L <= x).
  Proof.
    intros hc Lc mq x k HH HCSq HIN Hk.
    assert (A5 : x + k <= Z.shiftr FB 3 + al_sb AL \/ Z.shiftr FB 3 + al_sb AL + 64 <= x).
    { eapply apart_client_shadow with (CS := hcs asegs R HIA hc) (c := FB) (k := 64);
        [ exact (hcs_ok asegs R HIA hc) | eapply (hm_blocks_cs asegs R HIA hc _ _ _ HH); apply in_app_iff; left; apply in_app_iff; left; exact HIN
        | eapply crange_mono; [exact HCSq| exact CFB]
        | unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia | exact Hk | lia ]. }
    pose proof (obj_apart_new R HIA hc Lc LB LF LF' mq lo (htop asegs R HIA h) CRT 744 x k DIMG HH ltac:(intros fb Hfb; right; exact Hfb) CWX ltac:(pose proof ALO; pose proof LOS; lia) ltac:(lia) HIN Hk) as A2.
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [BR HAP]. rewrite Forall_forall in BR.
    ddestruct (BR (x, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HIN)) as (_ & _ & Bce & Bimg). cbn [fst snd] in Bce, Bimg.
    pose proof (blocks_apart_app_lr (Lc ++ LB) LF' x k FB 512 HAP ltac:(apply in_app_iff; left; exact HIN) ltac:(left; reflexivity)) as A3.
    pose proof ALO. pose proof LOS. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact A5| exact Bimg].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L53965678973.198L56765669119.201L61160186364.20900000a01Q02QS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB3S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB31a2HaS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp14LFB31x1k2A12A22A32A4". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 DIMG STKc2 Q blen BUF slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CWX DXB SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APC SPR ALO ACV F0 APB SLOu SP1R LFB3"] Lemma owns_mu : forall (hc : HST asegs R HIA) Lc mm mm' ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    HM asegs R HIA hc (Lc ++ LB) LF' mm -> (forall y, CS y -> hcs asegs R HIA hc y) ->
    munch WMU mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' ->
    owns asegs PK mm' (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk.
  Proof.
    intros hc Lc mm mm' ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW PERM HH HCSq MU WM MI'.
    unfold owns in *.
    eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := WMU) (SP := bv_unsigned sp) (L2 := Lc ++ LB);
      [exact OW| intros b Hb; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]
      | | exact (blocks_below_hm R HIA hc _ _ mm (Lc ++ LB) HH ltac:(intros b Hb; exact Hb)) | pose proof ACV; lia| exact MI'|].
    - intros a Ha Hc Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. exact Ho.
    - intros [x k] Hb Hk. cbn [fst snd] in Hk |- *.
      assert (XL : In (x, k) Lc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
      ddestruct (own_apart hc Lc mm x k HH HCSq XL Hk) as (A1 & A2 & A3 & A4 & _). cbn [disjoint_from]. pose proof SLOu. pose proof NS1. pose proof STKc0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L15085325610.193L59308579414.200L59310683405.196L59314873579.199L6037081027.194 00001a04405\07?08^S1R3HIA1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB34SSPc4TOPc3HSS2HT1c1HS1R4STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB23LFB2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL2FB3sp15BUFLO3SPR2F04FBLO4SP1R4LFB32G11a2Hs3Hin1H2H12H2S1R2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB3DCD2FB3sp13APC3SPR2F03APB3FDD4SP1R4LFB31a3Hd13HinS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB31a1B1j2Hr3Hin1HS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB33SPc2HS1a1H". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 Q blen BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CRTLO DXB SLOS SLOL SLO SPH LOS DCD sp1 SP1 FRSH APC BUFLO SPR ALO ACV F0 F1 FBLO APB FDD SLOu SP1R LFB3"] Lemma presA_down : forall Lq SPc SSPc TOPc Wc mA mB,
    presA asegs R (Lq ++ LB) LF' SPc SSPc TOPc Wc mA mB -> SPc <= bv_unsigned sp -> SSPc <= bv_unsigned sp -> hstkhi asegs R HIA h <= TOPc ->
    (forall x, outside WSI x -> (FB <= x < FB + 512 -> False) -> outside Wc x) ->
    presA asegs R LB LF (bv_unsigned sp) (bv_unsigned sp) (hstkhi asegs R HIA h) WSI mA mB.
  Proof.
    intros Lq SPc SSPc TOPc Wc mA mB [P S] HS HSS HT HW. dpose FRSH as (G0 & G1 & G2 & G3). split.
    - intros a Ha Hc Ho. apply P; [exact Ha| |].
      + destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
        exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; apply (fdata_cons_sub b [] FB 512 LF); exact Hb].
      + apply HW; [exact Ho|]. intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
        * pose proof ALO. pose proof LOS. pose proof SLOu. pose proof NS1. pose proof STKc0. lia.
        * lia.
        * destruct bk as [B j]. cbn [fst snd] in Hr. pose proof (G3 B j Hbk). lia.
    - intros c Hc Hs. apply S; [| exact Hs].
      destruct Hc as [H|[H|[H|H]]]; [left; lia| right; left| right; right; left| right; right; right; exact H].
      + ddestruct H as (b & Hb & Hr). exists b. split; [apply in_app_iff; right; exact Hb| exact Hr].
      + ddestruct H as (b & Hb & Hr). exists b. split; [right; exact Hb| exact Hr].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation FSHB := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation FSHV := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Ltac client_facts hc :=
    lazymatch goal with HHx : HM _ _ _ hc ?Lh _ _, HTx : htop asegs R HIA hc = htop asegs R HIA h |- _ =>
      assert (SUBh : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata LF'))
        by (intros b' Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; exact Hb'| right; apply (fdata_cons_sub b' [] FB 512 LF); exact Hb']);
      assert (CWXn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) CRT 744) by (rewrite HTx; eapply client_wrange_mono; [exact CWX| exact SUBh]);
      assert (CWXh : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA h) CRT 744) by (eapply client_wrange_mono; [exact CWX| exact SUBh]);
      assert (CRXs : client_range L (Lh ++ fdata LF') sp1 CRT 744) by (eapply (client_range_wsep L (LB ++ fdata LF) _ lo _ sp1 _ _ CWX); [exact SUBh| left; exact CRTLO]);
      lazymatch type of HHx with HM _ _ _ _ (?Lxx ++ LB) _ ?mq =>
        let FRSHc := fresh "FRSHc" in let INF := fresh "INF" in let INHc := fresh "INHc" in let INDc := fresh "INDc" in let AP := fresh "AP" in
        let SBND := fresh "SBND" in let APS := fresh "APS" in
        pose proof (fresh_apart_grow R HIA hc Lxx LB LF mq FB 512 FRSH HHx) as FRSHc;
        destruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lxx ++ LB) LF mq FB 512 lo HHx eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
          as (_ & INF & INHc & INDc & AP & _ & _ & _ & SBND & APS); change (512 / 8) with 64 in SBND, APS; change (512 - 40) with 472 in INDc end
      ;
      lazymatch goal with INDx : In (FB + 32, 472) (Lh ++ fdata LF'), INHx : In (FB, 24) (Lh ++ fdata LF') |- _ =>
        assert (CRFs : client_range L (Lh ++ fdata LF') sp1 (FB + 32) 472) by (eapply client_range_block; [exact INDx| clear; lia| clear; lia]);
        assert (CRHs : client_range L (Lh ++ fdata LF') sp1 FB 24) by (eapply client_range_block; [exact INHx| clear; lia| clear; lia]);
        assert (CWFn : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA hc) (FB + 32) 472) by (eapply client_wrange_block; [exact INDx| clear; lia| clear; lia]);
        assert (CWFh : client_wrange L (Lh ++ fdata LF') lo (htop asegs R HIA h) (FB + 32) 472) by (eapply client_wrange_block; [exact INDx| clear; lia| clear; lia]) end
    end.
  Ltac clear_client_facts :=
    repeat match goal with
    | H : client_range _ _ _ _ _ |- _ => clear H
    | H : client_wrange _ (_ ++ fdata LF') _ _ _ _ |- _ => clear H
    | H : In (FB + 32, 472) _ |- _ => clear H | H : In (FB, 24) _ |- _ => clear H | H : In (FB, 512) _ |- _ => clear H
    | H : fresh_apart R (_ ++ LB) LF FB 512 |- _ => clear H
    | H : forall b', In b' (LB ++ fdata LF) -> In b' _ |- _ => clear H
    | H : forall B j, In (B, j) LF -> _ |- _ => clear H
    end.

  (* [comment removed for export] *)
  Ltac open_cinv INV hc :=
    destruct INV as (HHc & HCSc & HTc & HSc & HFc & FHD & LV & LN & PC & LP1 & LP2 & LO2 & FSH & SAVE & RSL & SThi & STlo & MI & OCRT & PRES & SS1 & SS2 & SIP);
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
    assert (CFBc : crange (hcs asegs R HIA hc) FB 512) by (eapply crange_mono; [exact HCSc| exact CFB]);
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]);
    assert (WCX : wcover R LB LF (bv_unsigned sp) WSI CRT 744) by (apply wcover_inside; cbn [inside]; left; clear; lia);
    client_facts hc;
    pose proof (art_stk_high asegs R HIA) as STKH.

  Ltac open_cinv_mu INV hc :=
    open_cinv INV hc;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl WMU mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HHx) as AB; pose proof (conj HHx I) as HH0 end end.

  (* [comment removed for export] *)
  Ltac ch_open CH := destruct CH as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15);
    unfold wbuf, buf_cells, name_blob, ext_cells in K0, K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15.
  Ltac ch_close mx :=
    lazymatch goal with
    | K0 : rw_cells asegs mx CRT _, K1 : rw_cells asegs mx (CRT + 32) _, K2 : rw_cells asegs mx (CRT + 64) _,
      K3 : rw_cells asegs mx (CRT + 88) _, K4 : rw_cells asegs mx (CRT + 112) _, K5 : rw_cells asegs mx (CRT + 136) _,
      K6 : rw_cells asegs mx (CRT + 160) _, K7 : rw_cells asegs mx (CRT + 224) _, K8 : rw_cells asegs mx (CRT + 288) _,
      K9 : rw_cells asegs mx (CRT + 336) _, K10 : rw_cells asegs mx (CRT + 360) _, K11 : rw_cells asegs mx (CRT + 376) _,
      K12 : rw_cells asegs mx (CRT + 400) _, K13 : rw_cells asegs mx (CRT + 424) _, K14 : rw_cells asegs mx (CRT + 696) _,
      K15 : rw_cells asegs mx (CRT + 720) _ |- _ =>
    eassert (CH : chunks asegs mx CRT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      by (exact (conj K0 (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 (conj K12 (conj K13 (conj K14 K15))))))))))))))));
    clear K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15
    end.

  (* [comment removed for export] *)
  Tactic Notation "fold_cinv" ident(INVn) constr(mx) constr(hc) constr(Lc) constr(fsh) :=
    try (match goal with H : rw_cells _ mx (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end);
    eassert (INVn : cinv Lc mx hc fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      by (unfold cinv; spine; first [eassumption | match goal with |- ?g => idtac "FOLD-LEFT:" g end]).

  (* [comment removed for export] *)
  Ltac si_mu :=
    lazymatch goal with MU : munch _ ?m0 ?mx, SIPx : si_P SI ?m0 |- _ =>
      let SIPn := fresh "SIP" in
      assert (SIPn : si_P SI mx)
        by (eapply (si_munch_offdata L SI); [exact SIPx| exact MU|];
            let a := fresh "a" in let Da := fresh "Da" in let Wa := fresh "Wa" in intros a Da Wa; cbn [outside];
            pose proof (art_data_lo asegs R HIA) as DLOx;
            lazymatch goal with SB : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ _ |- _ => xl Da DLOx SB end);
      clear SIPx end.

  (* [comment removed for export] *)
  Definition BUDX (hc : HST asegs R HIA) (Lc : list blk) : Prop :=
    havol asegs R HIA hc <= havol asegs R HIA h + PHIc blen /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRc blen d /\ Z.of_nat (length Lc) <= CNTc blen.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac pres_call HP :=
    lazymatch type of HP with presA _ _ (?Lq ++ LB) _ ?SPc ?SSPc ?TOPc ?Wc ?mA ?mB =>
    lazymatch goal with PRx : presW _ _ _ ?hx LB LF _ _ _ _ mA, HSx : hstkhi asegs R HIA ?hx = hstkhi asegs R HIA h |- _ =>
      let PD := fresh "PD" in
      assert (PD : presA asegs R LB LF (bv_unsigned sp) (bv_unsigned sp) (hstkhi asegs R HIA h) WSI mA mB)
        by (eapply (presA_down Lq SPc SSPc TOPc Wc mA mB HP);
            [ xl | xl | first [rewrite HSx; clear; lia | clear; lia]
            | let x := fresh "x" in let Hx := fresh "Hx" in let NF := fresh "NF" in let Hx1 := fresh "Hx1" in let Hx2 := fresh "Hx2" in
              intros x Hx NF; cbn [outside app] in Hx |- *; destruct Hx as [Hx1 Hx2];
              repeat (split; [first [exact Hx2 | clear - Hx1 NF; lia]|]); first [exact I | exact Hx2] ]);
      let PX1 := fresh "PX" in let PX2 := fresh "PX" in
      destruct PRx as (PX1 & PX2);
      assert (PRx : presW asegs R HIA hx LB LF (bv_unsigned sp) (bv_unsigned sp) WSI m mB)
        by (split; [eapply presA_trans; [exact PX1| rewrite HSx; exact PD] | exact PX2]);
      clear PX1 PX2 PD
    end end.

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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L26892418956.1 L27734943701.75L46177494375.71L49799642497.71L56658999053.1 L6021324682.74 L62036949211.71L695790177.71  00000402403;03Q03U05[06_075S2spS1R3HIA3NS14STKc5STKc12sp3CRT3BUF2lo3slo2bs4CRT05CRTLO3DXB4SLOS4SLOL2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1R2hc1a2Ha1HS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPA2FB3sp13APC3SPR2F03APB4SP1RS2sp3CRT2bs2FB3sp13SP1S2spS1R3HIA3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1R2hc1a2HaS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT03SPH3LOS2FB3sp13SPR2F04SLOu4SP1RS2sp3CRT2bs2FB3sp13SPR". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc1 STKc2 Q blen BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CRTLO DXB SLOS SLOL SLO SPA SPH LOS UW FB SP1 FRSH APC BUFLO SPR ALO ACV F0 F1 FBLO APB SLOu SP1R"] Lemma uwc_callee : forall (hc : HST asegs R HIA) mq, presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) WSI m mq ->
    hstkhi asegs R HIA hc = hstkhi asegs R HIA h -> rw_cells asegs mq (bv_unsigned sp + -104) SAVEL ->
    uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1).
  Proof.
    intros hc mq PRES HSc SAVE. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UWa : uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { rewrite <- HSc. eapply (uwc_presA R); [exact (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES)| rewrite HSc; exact UW| clear; lia| | xl| rewrite HSc; apply hstkhi_le64; xl].
      intros a Ha. cbn [outside]. split; [xl Ha|]. apply si_outside_above. pose proof (art_data_lo asegs R HIA). xl Ha H. }
    pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| xl| xl| exact D0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition BUDE (hc : HST asegs R HIA) (Lc : list blk) : Prop :=
    havol asegs R HIA hc + PHIcf (CNTc blen) <= havol asegs R HIA h + PHIc blen
    /\ hfr asegs R HIA hc + FFRcf (CNTc blen) 0 <= hfr asegs R HIA h + FFRc blen d
    /\ Z.of_nat (length Lc) <= CNTc blen.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L30375892680.189L5436588646.186 L5436599221.188 L5442885517.187 00002\03O04B055S1R3HIA4CNTk5PHIcf5FFRcf4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB32hc2Lc2kv2kf2kc1a2V12V22V32HV2HF2HC2Ha1H2H02H1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc1a2HaS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc1a2HaS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc1a2Ha". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_mono FFRj_mono CNTj_mono LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma BUD_E : forall hc Lc kv kf kc a, BUD hc Lc kv kf kc a -> kv <= KVc blen -> kf <= KFc blen d -> kc <= 2 + CNTk -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    (intros hc Lc kv kf kc a dd_H; ddestruct dd_H as (V1 & V2 & V3); intros HV HF HC Ha). unfold BUDE, PHIc, FFRc, CNTc in *.
    pose proof (PHIj_mono a blen ltac:(lia)). pose proof (FFRj_mono a blen d ltac:(lia)). pose proof (CNTj_mono a blen ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L29426751976.17500001SS4CNTk4CNTj2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB31H2H0". (* [comment removed for export] *)
  #[using="R HIA NS1 STKc STKc0 NA1 STKc2 CNTj0 CNTk0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma CNTc0 : 0 <= CNTc blen.
  Proof. unfold CNTc. pose proof (CNTj0 blen B2). pose proof CNTk0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L41433769834.18100001nS1R3HIA5PHIcf5FFRcf1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB32hc2Lc2V12V22V31H2H0". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 CNTj0 CNTk0 PHIcf0 FFRcf0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma BUDE_X : forall hc Lc, BUDE hc Lc -> BUDX hc Lc.
  Proof.
    (intros hc Lc dd_H; ddestruct dd_H as (V1 & V2 & V3)). pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). unfold BUDX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L14322534665.18900000lS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36rawlen4rawp2RP1E". (* [comment removed for export] *)
  #[using="LF sp CRT blen bs LFB2 LFB B2 FB sp1 LFB3"] Lemma raw_in_Lc : forall Lc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts,
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) -> 0 < rawp -> In (rawp, rawlen) Lc.
  Proof.
    intros Lc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts PERM RP.
    eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite crt_blocks_f_of.
    do 5 (apply in_or_app; right). unfold oblk. destruct (Z.eqb_spec rawp 0) as [E|_]; [lia| left; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L25914671739.203000014S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36rawlen4rawp7rawjunk2BB". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 DIMG STKc2 sp Q blen BUF slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CWX DXB SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma raw_side : forall (hc : HST asegs R HIA) Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
    owns asegs PK mq (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    HM asegs R HIA hc (Lc ++ LB) LF' mq -> (forall y, CS y -> hcs asegs R HIA hc y) -> 0 < rawp -> 0 < rawlen ->
    bytes_at asegs mq rawp rawjunk /\ Z.of_nat (length rawjunk) = rawlen /\ In (rawp, Z.of_nat (length rawjunk)) (Lc ++ LB)
    /\ aobj asegs AL (hcs asegs R HIA hc) mq rawp (Z.of_nat (length rawjunk))
    /\ (rawp + rawlen <= CRT \/ CRT + 744 <= rawp) /\ (rawp + rawlen <= FB \/ FB + 512 <= rawp) /\ rawp + rawlen <= lo
    /\ rawp + rawlen <= alloc_ceiling.
  Proof.
    intros hc Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW PERM HH HCSq RP RL.
    destruct (raw_facts asegs PK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OW RP) as (RBY & RLEN & RIN & _).
    pose proof (raw_in_Lc _ _ _ _ _ _ _ _ _ _ _ _ _ PERM RP) as XL.
    ddestruct (own_apart hc Lc mq rawp rawlen HH HCSq XL RL) as (A1 & A2 & A3 & _ & _).
    pose proof (blocks_below_hm R HIA hc _ _ mq (Lc ++ LB) HH ltac:(intros b Hb; exact Hb) (rawp, rawlen) RIN) as BB. cbn [fst snd] in BB.
    split; [exact RBY|]. split; [exact RLEN|]. rewrite RLEN. split; [exact RIN|].
    split; [exact (hm_aobj_block asegs R HIA hc _ _ mq rawp rawlen HH RIN)|].
    split; [exact A1|]. split; [exact A2|]. split; [exact A3| lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Let LFB512 : (length LF' < 512)%nat.
  Proof. eapply Nat.le_lt_trans; [exact LFB3|]. unfold LFMAX_CRT. apply Nat.ltb_lt. reflexivity. Qed.
  Let LFB511 : (length LF' < 511)%nat.
  Proof. eapply Nat.le_lt_trans; [exact LFB3|]. unfold LFMAX_CRT. apply Nat.ltb_lt. reflexivity. Qed.
  Let LFB7 : (length LF' <= LFMAX_CRT + 7)%nat.
  Proof. eapply Nat.le_trans; [exact LFB3|]. unfold LFMAX_CRT. apply Nat.leb_le. reflexivity. Qed.

  (* [comment removed for export] *)
  Tactic Notation "cside" hyp_list(Hs) :=
    lazymatch goal with
    | |- (length _ < 512)%nat => exact LFB512
    | |- (length _ < 511)%nat => exact LFB511
    | |- (length _ <= LFMAX_CRT + 7)%nat => exact LFB7
    | |- (length _ <= LFMAX_CRT + 3)%nat => exact LFB3
    | |- client_range _ _ _ ?a _ =>
        first [ match goal with RINx : In (a, _) _ |- _ => eapply client_range_block; [exact RINx| clear; lia| clear; lia] end | solve_client_range ]
    | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
    | |- aobj _ _ _ _ (CRT + _) _ => match goal with H : aobj _ _ _ _ CRT 744 |- _ => eapply aobj_sub; [exact H| clear; lia| clear; lia] end
    | |- _ => xl Hs
    end.

  (* [comment removed for export] *)
  Ltac to_free := repeat (lazymatch goal with |- _ (MS _ _ (Z_to_bv 64 691912) _ _ _ _) => fail | |- _ => zstep end).

  (* [comment removed for export] *)
  Tactic Notation "refold_mu" ident(INVn) ident(OWn) constr(hcx) constr(Lcx) constr(fshx) :=
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      si_mu;
      lazymatch goal with MU : munch _ ?m0 mx, WM : wmono _ ?m0 mx, OWx : owns _ _ ?m0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, PMx : Permutation Lcx _,
                          HHz : HM _ _ _ hcx _ _ ?m0 /\ True, HCz : (forall x, CS x -> hcs asegs R HIA hcx x), MIx : mem_inv asegs mx |- _ =>
        pose proof (owns_mu hcx Lcx m0 mx _ _ _ _ _ _ _ _ _ _ _ _ _ OWx PMx (proj1 HHz) HCz MU WM MIx) as OWn end;
      fold_cinv INVn mx hcx Lcx fshx;
      ch_close mx
    end.

  (* [comment removed for export] *)
  Ltac r_zero K Hr := 
    change 18446744073709551615 with (Z.ones 64) in K; rewrite ?Z.land_ones in K by (clear; lia);
    let E := fresh "R0" in
    lazymatch type of K with
    | ?r mod _ = 0 => assert (E : r = 0) by (clear - K Hr; Z.div_mod_to_equations; lia)
    | _ => idtac
    end.

  (* [comment removed for export] *)
  
  
  (* [comment removed for export] *)
    
  (* [comment removed for export] *)
  #[using="Type"] Lemma cnt24_small_all : forall l : list blk, (forall b, In b l -> snd b < 5889) -> cnt24 l = 0.
  Proof.
    induction l as [|[A k] l IH]; intros H; [reflexivity|].
    rewrite cnt24_cons_small by (apply (H (A, k)); left; reflexivity). apply IH. intros b Hb. apply H. right. exact Hb.
  Qed.
      
  (* [comment removed for export] *)
  Ltac perm_front :=
    rewrite ?app_assoc; repeat apply Permutation_app_tail; rewrite <- ?app_assoc;
    first [ apply Permutation_refl | eapply Permutation_trans; [apply Permutation_app_comm|]; rewrite <- ?app_assoc; apply Permutation_refl ].

  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L16526487874.188L19616048289.191L2192452093.187 L22676661558.188L24188363034.188L32883993289.191L38339916114.19100002004005i07b09_0;b0=9S2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz3HB12H22H32HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12HL1i2Hi1HS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12H3S2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H22HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz3HB02H12HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12H32HL1i2Hi1HS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  #[using="R HIA NS1 STKc STKc0 NA1 STKc2 LB LF sp CRT Q blen BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma bslice : forall mX B bsx P0 Lz, bytes_at asegs mX B bsx -> B <= P0 -> 0 <= Lz -> P0 + Lz <= B + Z.of_nat (length bsx) ->
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
  Ltac bcmp_call P0z Q0z nz Hs :=
    let SPB := fresh "SPB" in
    pose proof (artA_bcmp asegs R HIA) as SPB;
    replace (Z_to_bv 64 360848) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite ABCMP; reflexivity);
    lazymatch goal with RBYx : bytes_at asegs ?mx ?rawpz ?rj, ORAWx : aobj _ _ _ ?mx ?rawpz _ |- _ (MS _ _ _ _ _ ?mx _) =>
      let PB := fresh "PB" in let PL := fresh "PL" in let QB := fresh "QB" in let QL := fresh "QL" in
      destruct (bslice mx rawpz rj P0z nz RBYx ltac:(Hs) ltac:(Hs) ltac:(Hs)) as [PB PL];
      destruct (bslice mx rawpz rj Q0z nz RBYx ltac:(Hs) ltac:(Hs) ltac:(Hs)) as [QB QL];
      lazymatch type of PB with bytes_at _ _ _ ?pps => lazymatch type of QB with bytes_at _ _ _ ?qqs =>
      lazymatch goal with HHx : HM _ _ _ ?hcx ?Lh _ mx |- _ =>
      acallxA_sp sp1
        (eapply SPB with (h := hcx) (LB := Lh) (LF := LF') (P := P0z) (Q := Q0z) (n := nz) (lo := lo) (ps := pps) (qs := qqs); clear SPB;
           rewrite ?(unsigned_lit sp1) by exact SP1R;
           first [ exact HHx | exact PB | exact QB | exact PL | exact QL | exact LOS | reflexivity | (symmetry; apply definitions.Z_to_bv_bv_unsigned)
                 | lazymatch goal with
                   | |- aobj _ _ _ _ _ _ => eapply aobj_sub; [exact ORAWx| Hs| Hs]
                   | |- stk _ _ lo _ => eassumption
                   | |- mem_inv _ _ => eassumption
                   | |- crange _ lo _ => eassumption
                   | |- _ <= htop _ _ _ _ => lazymatch goal with HTx : htop asegs R HIA hcx = _ |- _ => rewrite HTx; xl end
                   | |- _ => Hs
                   end
                 | match goal with |- ?g => idtac "BCMP-PRE-LEFT:" g end ])
      end end end;
      try clear PB PL QB QL
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Local Notation BUDK hc Lc a := (BUD hc Lc (KVc blen) (KFc blen d) (2 + CNTk) a).

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Local Notation BUD2 hc Lc a := (BUD hc Lc ((2 * blen + AVOL_CALL) + X509_SIG_ALG_PHI) (Z.max 0 (fr_charge (d + 1)) + Z.max 0 (X509_SIG_ALG_FFR 0)) 2 a).

    
  (* [comment removed for export] *)
  Ltac mu_reset hcx :=
    repeat match goal with H : munch WMU _ _ |- _ => clear H end;
    repeat match goal with H : HM _ _ _ _ _ _ _ /\ True |- _ => clear H end;
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      repeat match goal with H : wmono asegs _ _ |- _ => clear H end; repeat match goal with H : abase _ _ _ |- _ => clear H end;
      pose proof (munch_refl WMU mx) as MU; pose proof (wmono_refl asegs mx) as WM;
      lazymatch goal with HHx : HM _ _ _ hcx _ _ mx |- _ => pose proof (hm_abase asegs R HIA hcx _ _ mx HHx) as AB; pose proof (conj HHx I) as HH0 end end.

  (* [comment removed for export] *)
  Tactic Notation "owns_now" ident(OWn) constr(hcx) constr(Lcx) :=
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MU : munch _ ?m0 mx, WM : wmono _ ?m0 mx, OWx : owns _ _ ?m0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, PMx : Permutation Lcx _,
                          HHz : HM _ _ _ hcx _ _ ?m0 /\ True, HCz : (forall x, CS x -> hcs asegs R HIA hcx x), MIx : mem_inv asegs mx |- _ =>
        pose proof (owns_mu hcx Lcx m0 mx _ _ _ _ _ _ _ _ _ _ _ _ _ OWx PMx (proj1 HHz) HCz MU WM MIx) as OWn end end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac gt_call p0z e0z lenpz tagz Hs :=
    let SPT := fresh "SPT" in
    pose proof GT as SPT; unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT;
    lazymatch goal with RBYx : bytes_at asegs ?mx ?rawpz ?rj |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ ?hcx _ _ mx |- _ =>
      acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hcx) (PP := FB + 96) (LENP := lenpz) (P := p0z) (END := e0z) (BUF := rawpz) (bs := rj) (tag := tagz) (lo := lo);
                     rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                     try (exact (art_alwf asegs R HIA));
                     first [ Hs | match goal with |- ?g => idtac "GT-LEFT:" g end ]) end end;
    clear SPT.

  
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Local Notation BUD1 hc Lc a := (BUD hc Lc (2 * blen + AVOL_CALL) (Z.max 0 (fr_charge (d + 1))) 1 a).

  (* [comment removed for export] *)
  Ltac joinc H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mq ?A1 ?cs1 => lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      let Hj := fresh "J" in
      assert (Hj : rw_cells sg mq A1 (cs1 ++ cs2))
        by (apply (proj2 (rw_cells_app sg mq A1 cs1 cs2)); split; [exact H1|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with A2 by (clear; lia) end; exact H2);
      clear H1 H2; rename Hj into H1; cbn [app] in H1 end end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L12183083268.182L13529316230.182L30047538062.18200001e02n043S4FFRk2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a2Ha1HS4CNTk5CNTk02LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71H". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD1_E : forall (hc : HST asegs R HIA) Lc a, BUD1 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    intros hc Lc a B Ha. eapply BUD_E; [exact B| | | | exact Ha]; unfold KVc, KFc, X509_SIG_ALG_PHI, X509_SIG_ALG_FFR.
    - pose proof (PHIk0 blen B2). unfold AVOL_CALL. lia.
    - pose proof (FFRk0 blen (d + 1) B2). lia.
    - pose proof CNTk0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma free_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 : word) (r : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7v s9v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> -2^31 < r <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 CRT) (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) s9v (Z_to_bv 64 r) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a8ec8) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.free_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma ea0_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k56 k64 k72 k80 k88 k96 k104 k120 : word) (rg : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4v s5v s7v s9v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 (Z_to_bv 64 CRT) k56 k64 k72 k80 k88 k96 k104 (Z_to_bv 64 CRT) k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> -0x3000 < rg <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s4v s5v (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a919c) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.ea0_walk ]; eassumption.
  Qed.

  (* [comment removed for export] *)

  Hypothesis S_SERALG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k64 k72 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s10v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 END2) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 k72
         (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 END1) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 CRT) (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) s10v
               (Z_to_bv 64 (FB + 96)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a9304) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0@_0@C18971418195.426C18973515383.452C52401662583.451C60410007123.425D11891817072.426D11893914196.452D16069757090.452D16071854214.426D16899842714.452D16901939902.426D16954620509.452D32458870384.426D3953997537.376 D3953997537.402 D3953997537.426 D40775185266.377D40775185266.428D42035635047.426D42037732163.452D43629700967.426D50871073524.452D60109196847.377D60109196847.428D60109446735.426D60111543915.452D60189065437.376D60189065437.402D60189065437.426D67258947169.377D67258947169.428K11645674384.452K12901509199.426K13074033359.426K13667079759.426K1394472811.450 K1396569935.426 K15835051771.377K15835051771.428K1607432955.377 K1607432955.428 K2038874319.426 K214510830.450  K216607946.426  K21870859916.377K21870859916.428K22593309295.450K22861045682.426K22863142806.452K22945712379.377K22945712379.428K23131760207.426K23133857387.450K26480487147.450K26482584271.426K26861164523.450K26863261647.426K27299522255.426K27684414415.426K30036842987.450K30038940111.426K30417541867.450K30419638991.426K31240246991.426K33593216207.426K33595313387.450K33980871419.377K33980871419.428K3591543988.377 K3591543988.428 K37355156075.451K38544919375.426K40707548879.426K40709646059.450K40741729903.450K41088771051.450K41090868175.426K41095599355.377K41095599355.428K4151664304.450 K4427075183.450 K44468409451.450K44470506575.426K4568054095.426 K4570151275.450 K45863235535.426K46975357874.426K5000048842.426 K51793631343.452K51946654571.450K51948751695.426K52147535611.377K52147535611.428K56707495759.426K58872734415.426K58874831595.450K58907964015.450K59270213583.426K59272310763.450K60265445967.426K63645101775.426K66272560811.451K67201981903.426K67950795727.426K8906271339.450 K8908368463.426 K9344607567.426 L10742455373.1  L10840411873.2  L1107926133.439 L11183176311.1  L11650366541.3  L12136144503.1  L12408374717.1  L12531231099.1  L12877562377.17 L12878060153.15 L12880089589.17 L12880089591.17 L12888630233.2  L13077864793.2  L13662592473.2  L1408793817.2   L14105265101.1  L14301694619.2  L14400447526.415L14402536426.414L14447004729.2  L14494355149.1  L14786404065.2  L1549210296.89  L15522251732.95 L15522319221.89 L15756275669.95 L15771191613.1  L15822417165.2  L15921722588.1  L1594761485.2   L16720167331.439L1685717371.0   L168650209.2    L16916955281.2  L16950639097.1  L1751239055.3   L17661654221.1  L17929607435.95 L18050741197.1  L18302214263.1  L18605302283.95 L19700477813.89 L19912320701.1  L20068494618.95 L20105749565.1  L2034453337.2   L204253020.2    L21218032077.1  L21221417243.2  L21557199983.95 L21593730587.2  L21652984618.400L21654730866.2  L21866712442.2  L22095213153.2  L22488405914.17 L22587310557.2  L22866772043.3  L22941438733.2  L22982591434.2  L23119474137.2  L23513807686.2  L2354636449.0   L23886653674.397L24023900370.0  L2461029618.11  L24970061901.1  L25060755370.446L25060755370.447L25160623805.2  L25636326795.2  L26171659739.2  L2621559066.1   L26351168119.1  L26486612313.2  L26831527741.1  L26875616345.2  L27311746393.2  L27327577336.2  L27386516966.1  L27696769113.2  L2770202465.2   L27816216555.2  L27832536201.401L27940752054.89 L27940815383.95 L28211258445.17 L28332892109.1  L28631860810.416L28632618922.2  L28633724782.1  L28721978061.1  L29345674871.1  L30042772057.2  L30288503757.95 L30431990105.2  L3058445732.2   L30958001265.3  L31145622673.2  L31253192025.2  L3129797493.1   L32084790861.1  L32327136116.1  L32333429070.423L32454903270.1  L33424351062.415L33597048665.2  L33817424237.3  L33914883850.365L33985112333.2  L34098898304.89 L3482381758.95  L3482445087.89  L34910047158.2  L34911520566.3  L35102401974.1  L35156311117.1  L3532059019.2   L35497690475.3  L35497690475.4  L35497691765.447L35544998830.1  L35627916443.2  L35655538583.72 L3598635821.3   L36039263669.438L36307103329.2  L363258721.2    L36460502135.1  L37123035746.364L3726076129.2   L37353421273.2  L37875066173.1  L38070592189.1  L3810342902.89  L38235734261.1  L38259954321.2  L38548881625.2  L39231752993.0  L39379299611.2  L39571956557.1  L39768386075.2  L39864004961.2  L40228640085.0  L40711908697.2  L40743534045.2  L41099742989.2  L41103222873.2  L41251426164.1  L4153464066.2   L41663468825.365L42411609006.0  L42482149836.1  L42488948659.2  L43035585427.415L43226826465.2  L43571151479.1  L43683057355.3  L43810982283.2  L4416226781.2   L44466151385.2  L45057340874.365L4572017369.2   L45859267673.2  L45950822922.416L4638224781.89  L46491294669.1  L46880376525.1  L46882717723.2  L46969621579.3  L47049041130.3  L47870616696.2  L48022350876.423L48455046775.1  L48488035500.95 L48488102925.89 L48707638735.5  L49233373885.2  L49304025233.2  L4943892354.364 L50051061275.2  L5012405084.2   L5021251703.1   L50440147739.2  L50925318027.2  L5116735037.1   L51803952093.2  L51906071000.2  L51909129149.1  L51953172697.2  L52160193805.2  L52491779133.1  L53849999973.438L53888958349.1  L53997053467.2  L54174754203.2  L54408904903.95 L54676236769.2  L55182816653.89 L56389819352.446L56389819352.447L56418360977.2  L56592702936.2  L56719719641.2  L57359870875.2  L57389346444.89 L576250010.418  L57698627611.2  L57747140429.1  L57798807159.1  L58039649675.2  L58304458071.95 L58314874807.11 L58885089625.2  L58918812125.2  L59257267289.2  L59308579414.10 L59308580059.18 L59308586248.2  L59413075133.1  L6008660450.10  L60278190553.2  L6042617148.1   L60754583113.0  L60914439501.1  L60915094729.89 L60958946355.95 L61366595738.418L61366595738.439L61366595865.365L61401481953.2  L61708038753.16 L62032231842.364L62275882349.3  L62680556151.1  L63641134425.2  L639424795.2    L64418530427.89 L64418598106.95 L64696484682.365L6487220337.3   L6522106337.2   L65221205066.2  L65232207949.1  L65607387291.2  L66282753305.2  L66298372189.2  L66332265789.1  L66594121190.2  L66597103718.3  L66721351741.1  L66914912701.1  L67197556313.2  L67367021494.95 L67461776529.2  L67963146329.2  L6798276507.2   L68452440367.438L6899380056.1   L6906665613.1   L7088503905.2   L7194131617.2   L7282981857.2   L7382465640.1   L7736014575.2   L7945092351.2   L8171953640.397 L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241379468.89  L9241446957.95  L9332256473.2   N10265517050.451N16246473668.451N20278600635.451N21805675365.451N26872553873.425N30910526005.451N32818861852.451N48204456022.425N54451912735.451N55966132906.425N60733400192.425N63430872977.425N66590330291.425N7710544102.451 O10616892889.450O10618990077.426O11744306777.450O11746403965.426O11930563540.424O11932660720.450O12441062169.451O16350966909.426O16353064025.450O17215019116.450O17217116232.425O17431956130.426O17494624509.426O17496721625.450O18624662873.450O18626760061.426O18999724541.426O19357757918.423O19359855098.449O19768328665.450O19770425853.426O19929130442.450O19931227630.426O20160692861.426O20935596669.426O20937693785.450O21709205984.452O21849335257.451O22221714158.426O22223811274.450O23600095229.426O24544806105.450O25875371261.426O26870824124.449O27837070672.450O29968654986.450O30010457231.426O30245212782.426O30247309898.450O32096263534.426O32098360650.450O32342533629.426O32535777404.452O32537874520.426O33239929326.426O33242026442.450O34029051225.450O34031148413.426O34618340093.426O35590701227.450O35592798351.426O35781932925.426O366419438.426  O36680917870.426O36683014986.450O368516554.450  O37628183242.450O37630280430.426O382206333.426  O39094383154.426O40463046306.426O40465143430.450O41843596285.426O41845693401.450O42194997450.450O42197094638.426O42430790013.426O424351700.424  O43813356810.451O44938202843.424O44940300031.450O45120147859.450O45122245047.426O4531152601.452 O45421758794.450O45423855982.426O45967443052.450O45969540168.426O47886884318.423O48860633802.450O48862730990.426O49701823576.426O50815441625.450O50817538813.426O5310697817.450 O5312795005.426 O53279408345.450O54023336829.426O54025433945.450O54381021294.426O54383118410.450O55209884805.424O55211981985.450O55666839717.450O55757313405.426O57199369324.450O57201466440.426O57836210557.426O59278274632.426O59280371820.450O60130887293.426O60687394173.426O60689491289.450O61464066679.426O61466163795.452O62206064366.426O62208161482.450O62226578045.426O63121348170.450O63123445358.426O63353470717.426O63902264854.452O63904362034.426O64128366333.426O64130463449.450O64471909102.450O64474006218.426O64512383193.450O65963309676.452O66560762826.450O66562860014.426O66601778393.450O66743393030.452O66792327293.426O7588621913.450 O7590719101.426 P10851408966.426P10853506146.450P14304577628.376P14304577628.402P14304577628.426P14461423358.377P14461423358.428P14791101538.450P14793198662.426P16923509334.376P16923509334.402P16923509334.426P1755912972.449 P180729698.450  P182826822.426  P21207000028.376P21207000028.402P21207000028.426P21608672476.376P21608672476.402P21608672476.426P21647862485.424P21649959665.450P22080053446.426P22082150626.450P22971318541.376P22971318541.402P22971318541.426P25154843674.426P25156940862.452P25648406280.450P25650503468.426P27803063656.452P2782215650.450 P2784312774.426 P28627113325.376P28627113325.402P28627113325.426P3062169383.450 P3064266499.426 P30967942870.423P31146933846.376P31146933846.402P31146933846.426P31289833292.429P31289833292.430P31289833292.452P31289833292.453P31289833292.454P324046647.404  P324046647.429  P324046647.452  P324046647.453  P33641443928.404P33641443928.429P33641443928.452P33641443928.453P33810555850.424P33812653038.450P3528336136.450 P3530433324.426 P35626081884.376P35626081884.402P35626081884.426P357446086.426  P3591543988.376 P3591543988.402 P3591543988.426 P359543266.450  P36320230626.450P36322327750.426P3739204194.450 P3741301318.426 P38261788758.376P38261788758.402P38261788758.426P39390572508.376P39390572508.402P39390572508.426P39554440246.404P39554440246.429P39554440246.452P39554440246.453P39771269340.376P39771269340.402P39771269340.426P39877125090.450P39879222214.426P42484919333.426P43223209058.450P43225306182.426P43679374408.450P43815688968.450P43817786156.426P46884029148.376P46884029148.402P46884029148.426P47045409591.452P47047506707.426P47874275067.450P47876372191.424P49230739482.426P49296947798.376P49296947798.402P49296947798.426P50057614556.376P50057614556.402P50057614556.426P50442506716.376P50442506716.402P50442506716.426P50930023688.452P53998888156.376P53998888156.402P53998888156.426P54190221148.376P54190221148.402P54190221148.426P54662134598.426P54664231778.450P56407612502.376P56407612502.402P56407612502.426P57344928092.376P57344928092.402P57344928092.426P57713046236.376P57713046236.402P57713046236.426P58041177900.425P58043275016.450P61389443170.450P61391540294.426P62260666314.424P6480458454.423 P6482555634.449 P6515303238.426 P6517400418.450 P653319132.376  P653319132.402  P653319132.426  P65606077020.376P65606077020.402P65606077020.426P66292560634.426P66294657758.450P67476194902.376P67476194902.402P67476194902.426P6809023836.376 P6809023836.402 P6809023836.426 P7084781282.450 P7086878406.426 P7181004322.451 P7295052130.450 P7297149254.426 P7750690063.377 P7750690063.428 P7903954312.404 P7903954312.429 P7903954312.452 P7903954312.453 P7941177179.450 P8754630693.426 P8756727809.450 Q10048084224.372Q10371637966.404Q10371637966.405Q10371637966.430Q10371637966.431Q10371637966.453Q10371637966.454Q10371637966.455Q10592533181.426Q1100286102.425 Q11133374175.426Q1114360721.374 Q11891817072.426Q11893914196.452Q11937307997.389Q12228163960.374Q12945255387.385Q13305674448.424Q13318131160.452Q13676950806.384Q13968043979.378Q14021759145.374Q14360074768.401Q14360074768.425Q15752730517.397Q15815455344.427Q16069757090.452Q16071854214.426Q16439912048.427Q16472810971.426Q16474908159.452Q1683845592.373 Q16950496597.424Q16952477917.425Q16954620509.452Q17460489310.380Q17722859966.373Q18087201584.424Q18087207268.448Q18087208808.447Q18089299771.424Q18107911000.452Q18112461904.424Q1831049680.424 Q1843752664.452 Q18567054366.373Q1899481166.398 Q1909840144.447 Q1911943491.424 Q19327708656.427Q19561449552.400Q19561563123.401Q19790690407.426Q19792787523.452Q19953245935.426Q19955343051.452Q20032613673.374Q20464211551.391Q20956599408.373Q21136610900.452Q21138708080.426Q21472160980.386Q21765573510.452Q21767670690.426Q21832736479.426Q21834833659.452Q21928300228.452Q21930397408.426Q22799085684.452Q22961297377.373Q22963397981.374Q23928209109.377Q23957120639.376Q23957120639.402Q23957120639.426Q2408599006.390 Q24913533424.427Q25389680632.425Q25473514713.426Q25475611901.452Q25952160488.375Q26062420905.425Q26258368918.422Q26425303288.374Q26481470270.373Q26500407375.373Q26614256344.452Q26618340816.424Q26920001690.388Q26989065181.379Q27665131153.397Q2803826605.426 Q2805923721.452 Q28234306710.398Q28465177121.373Q28465177121.399Q28465177121.423Q28987294049.373Q28989404125.374Q29516740158.373Q2953304272.424 Q2965450712.452 Q29719672728.426Q29775522890.405Q29775522890.431Q29775522890.454Q29775522890.455Q29775981542.426Q29778078658.452Q30357303536.427Q30439524718.394Q30602209460.373Q30995755540.382Q32010102255.422Q32120916336.427Q32458870384.426Q3260556108.376 Q3260556108.402 Q3260556108.426 Q33447398408.404Q33447398408.430Q33447398408.453Q33447398408.454Q33640236611.452Q33642333799.426Q34615476081.426Q34667111065.399Q34671586469.373Q35010390169.377Q35067538392.452Q35080559824.424Q36585933458.380Q37036722651.426Q37134077776.424Q37138200664.452Q3731598672.424 Q3735902808.452 Q37546564045.376Q37546564045.402Q37546564045.426Q37664897648.427Q3799283926.401 Q38511566552.392Q39041068050.390Q39180574961.376Q39180574961.402Q39180574961.426Q39439682456.426Q39441779644.452Q39850762830.404Q39850762830.430Q39850762830.453Q39850762830.454Q39857052210.374Q40772909426.376Q40775185266.377Q40775185266.428Q42035624149.387Q42340228588.424Q42439168719.426Q42439443119.376Q42439443119.377Q42439443119.402Q42439443119.426Q42439443119.428Q42441265899.452Q42441548847.404Q42441548847.429Q42441548847.452Q42441548847.453Q42580734868.396Q43010690198.425Q43024701279.381Q43106127567.424Q43997683113.427Q44032164083.423Q44032164083.447Q44034350992.447Q44298944140.374Q44301027056.404Q44301027056.430Q44301027056.453Q44301027056.454Q44359965849.387Q44366841361.379Q45741809296.376Q45741809296.402Q45741809296.426Q46294542448.427Q47388118176.372Q47651296856.452Q47663800656.424Q47799523355.448Q47799524887.447Q47799530063.373Q47799530063.424Q47801628228.424Q47957748593.426Q47959845717.452Q48016974168.373Q48118064779.426Q48119910507.404Q48119910507.430Q48119910507.453Q48119910507.454Q48120161967.452Q48466957116.452Q48469054232.426Q48782272621.374Q48782272621.425Q49245538982.402Q49245538982.426Q49245538982.428Q49245821638.426Q49247644710.404Q49247644710.429Q49247644710.452Q49247644710.453Q49247918818.452Q49698585326.375Q49698585326.426Q49746198710.426Q49746415830.376Q49746415830.377Q49746415830.402Q49746415830.426Q49746415830.428Q49748295826.452Q49748522582.404Q49748522582.429Q49748522582.452Q49748522582.453Q50871073524.452Q51568379993.383Q519278494.373  Q51961662993.394Q52067830340.424Q52136395990.426Q52138493170.452Q52332670360.386Q52464623068.393Q5265442331.374 Q5265442331.400 Q5265442331.424 Q53213300373.383Q53315247896.426Q53332914930.427Q54994205552.427Q55415036769.376Q55415036769.402Q55415036769.426Q55613122833.425Q55660191.395   Q55705303732.373Q55942117014.422Q5596578838.404 Q5596578838.430 Q5596578838.453 Q5596578838.454 Q56530976407.426Q57146098416.373Q57618602681.376Q57618602681.377Q57618602681.402Q57618602681.426Q57618602681.428Q57620708409.404Q57620708409.429Q57620708409.452Q57620708409.453Q57828105177.426Q57830202365.452Q57893485213.399Q57985426136.452Q57998153168.424Q58447922544.427Q58741773977.452Q58742053010.398Q58743871165.426Q58746001061.373Q58845820120.452Q58850083792.424Q5920133699.452 Q5922230887.426 Q5956758249.447 Q5959038346.423 Q5959038346.447 Q59615272911.424Q59615277975.447Q59615278491.448Q59617369028.424Q59769434900.392Q60047576656.424Q60060055896.452Q60133690903.385Q60138834195.381Q60191312605.375Q60356678983.424Q60703360670.373Q61097091032.382Q6190817072.452 Q6191098356.404 Q6191098356.429 Q6191098356.452 Q6191098356.453 Q6192914196.426 Q6193188724.402 Q6193188724.426 Q6193188724.428 Q62190329447.426Q62586361046.388Q62967769840.427Q63119234008.452Q63132001488.424Q63588016986.384Q64228675114.403Q64228675114.429Q64228675114.452Q64228675114.453Q64597824751.422Q64635759216.427Q65213305286.393Q65509695635.391Q66043421264.424Q66047202648.452Q66063833015.452Q66484855892.452Q66486953072.426Q67028497104.378Q67038703949.426Q67038978349.376Q67038978349.377Q67038978349.402Q67038978349.426Q67038978349.428Q67040801129.452Q67041068973.404Q67041068973.429Q67041068973.452Q67041068973.453Q67256769633.376Q67256769633.427Q67258947169.377Q67258947169.428Q67618839536.427Q67781688024.452Q67794406864.424Q68075412041.424Q68077510210.424Q68077515290.447Q68077515798.448Q6909946600.401 Q6998050362.424 Q7000157801.447 Q7010778935.398 Q7093291664.396 Q7264918896.427 Q7740170440.401 Q7740170440.425 Q7970333713.374 Q8142890667.452 Q8360723123.452 Q8362820247.426 Q8551574768.427 Q8699115497.376 Q8699115497.377 Q8699115497.402 Q8699115497.426 Q8699115497.428 Q8699324297.426 Q8701202793.404 Q8701202793.429 Q8701202793.452 Q8701202793.453 Q8701421485.452 Q9356559653.429 Q9356559674.403 Q9598096785.389 Q9633964463.400 Q9634015756.401 Q9644583048.426 Q9646680236.452 Q9890590619.395 00000400800=00A01Q02d04m07308n0:f0<90=I0?K0AM0CT0E20FQ0Ga0I40JD0KW0M>0Nf0P?0Q[0Sk0V;0XP0Yn0[M0]T0^a0_n0a;0bH0cU0e00fL0gg0iC0jP0k]0lj0nE0oa10n12i15016K17g1941:A1;N1<[1=h1?51@B1AO1B\1Ci1E61FC1GP1H]1Ij1KE1La1NO1PL1QY1Rf1T31U@1VM1WZ1Xg1ZB1[^1\k1^81_E1`R1a_1bl1d91f41gA1hN1i[1jh1lC1m_1nl20921F22S23`24m26:27G28T29a2:n2<;2=H2>U2>Z2>[2A=2AA2AB2AF2AK2AP2AQ2AR2AS2AT2AU2AV2AW2AX2A]2A^2A_2A`2Aa2Af2Ag2C`2E82FP2H<2HA2HB2HK2HL2Jj2Jk2Jl2Jm2K22K32K82Ke2Kj2Kk2LS2Mk2N02OI2ON2OO2OP2OU2OV2P?2P@2QP2QQ2QR2QS2R:2R;2R<2R=2R>2R?2RJ2RK2T32T42TG2TH2V?2X62X72X82XA2XF2XJ2XK2XP2XQ2XR2XS2XW2XX2XY2XZ2Yj2[<2\N2\k2]02^@2^A2^F2^K2^O2^P2_<2_=2_>2_?2_@2_A2_F2_K2_O2aB2aF2bU2bV2bW2c]2c^2dB2e\2g62g>2g?2g@2gE2gF2gG2gH2h[2h`2ha2j92j:2j;2j<2j=2jA2kP2kQ2kR2kW2k\2lI2lM2lN2lO2lP2lQ2lV2lW2lX2lY2lZ2l[2l\2l]2la2lb2mh2mi2mn2mo2n02n12n52n62n72n82n92o?2o@2oA30Q32W32\32a32b32c32d32e32f32j34:35J35^35_35`37k37l37m37n37o38038538638>38C38D38E38J38K38P38Q38R39@39A3;G3;H3;I3;J3;R3;S3;T3<;3=N3=O3=T3=X3=Y3??3?[3?\3?]3?^3?o3@I3@O3@T3@e3@f3@k3@l3A13Bd3Da3F43GG3HM3HN3Hh3Hi3Hj3Hn3Ho3I03Ja3LR3MX3MY3MZ3M[3M`3Ma3Mb3Mc3Mh3N03N13N63N;3N<3P=3P>3P?3P@3PA3PE3PJ3PK3PL3PM3PQ3PR3PS3PT3PU3RU3RV3RW3S03SW3T>3T?3UU3Vd3X33Y>3ZI3ZJ3\=3]S3_S3`^3bQ3bR3dR3e]3e^3e_3e`3ea3eb3ec3ed3ee3ef3eg3eh3ei3ej3ek3el3em3en3eo3f03f13f23f33f43f53f63f73f83f93f:3f;3f<3f=3f>3f?3f@3fA3fB3fC3fD3fE3fF3fG3fH3fI3fJ3fK3fL3fM3fN3fO3fP3fQ3fR3fS3fT3fU3fV3fW3fX3fY3fZ3f[3f\3f]3f^3f_3f`3fa3fb3fc3fd3fe3ff3fg3fh3fi3fj3fk3fl3fm3fn3fo3g03g13g23g33g43g53g63g73g83g93g:3g;3g<3g=3g>3g?3g@3gA3gB3gC3gD3gE3gF3gG3gH3gI3gJ3gK3gL3gM3gN3gO3gP3gQ3gR3gS3gT3gU3gV3gW3gX3gY3gZ3g[3iR3kI3mJ3oK41Q43V45\47S49J4;L4=H4?S4AJ4CA4E84G94I:4K@4MA4OB4QH4QI4QJ4SA4U84W94Y:4[@4]24^d4`V4bH4d?4f64gm4ii4ke4mj4oa51X53P55L57H59M5:i5:j5<F5=b5=c5?I5A95Bi5DY5F35GW5I;5J_5L05MA5O95Q15S25U35W95Y05[D5]X5`55al5cc5eZ5gQ5iH5kD5m@5oE61F63G65M67E69U6;W6=j6?k6Al6D26Ei6G`6IJ6KA6M86NN6P@6R26T36V46X:6ZD6\F6^86_j6a\6cX6eT6gY6iZ6k[6ma6ob71c73i75[77\79]7;c7=d7?e7Ak7Cb7EY7GU7IQ7KV7MW7OX7Q^7S87TR7V57Wg7YY7[P7]G7^X7`P7bH7d?7f67h77j87l>7n?80@82F83V84f86b88^8:c8<d8>e8@k8Bb8DY8FP8HG8J>8L;8N98P<8RI8TV8Vc8XR8Z<8[f8]M8^d8`G8ah8cU8e68fc8hP8iU8iV8j[8kZ8l_8md8o490O91_91`91a93194X94Y95l97H98T98U9:F9<79<89<99<:9=99>B9?K9@T9Ad9C<9DA9EF9FK9GP9GQ9GR9GS9GT9I;9J:9KC9LL9LM9Mg9OA9OB9OC9OD9OE9OF9PV9QU9RZ9S_9To9Vd9XY9Y^9Zc9Zd9Ze9Zf9[e9\d9^49^59^69^79_G9_H9`m9`n9`o9b[9b\9ce9e@9fX9gS9gT9gU9he9j59kA9lJ9mS9n_9of:0m:2>:3=:4<:5T:5U:5V:6[:8>:9k:;X:=E:>U:?e:?f:AT:BO:C_:Dh:Di:En:Eo:F0:F1:GH:Hi:JJ:Kk:M0:N5:N6:OB:P=:QM:QN:QO:R_:R`:Ra:Rb:Rc:Rd:Te:Vf:Xl:Xm:Z9:[I:\Y:^X:`W:b_:cd:di:f;:gW:i3:jO:kO:lf:n=:oU;0e;0f;26;3T;56;6T;8;;9^;:n;<I;=n;?S;A8;BD;BE;CU;D^;F6;G?;HH;IQ;JQ;Kc;M?;N[;P7;QG;RW;RX;RY;RZ;R[;T3;T4;T5;U:;V?;W:;X?;YD;YE;YF;ZE;\2;]j;_l;an;d0;e];e^;e_;ff;h7;h8;h9;h:;h;;h<;h=;h>;h?;h@;iL;jb;l@;mh;oX<1@<31<4b<6@<7i<9\<;O<=B<>K<?[<AB<Ba<Bb<DY<FP<G`<I0<J8<K@<LR<Mb<Mc<Md<Me<O?<PY<R<<SE<TQ<UL<VU<VV<VW<VX<VY<VZ<WY<Yo<[N<]d<`?<a_<c;<da<fG<gm<iO<k1<l=<mF<nO<nP<oU=0a=1f=2a=2b=2c=2d=2e=3n=57=6@=6A=6B=6C=6D=7T=7U=7V=8f=:6=<1==:=>a=@1=A:=BP=D0=EP=G0=H9=IL=Jh=LD=MI=NY=NZ=N[=N\=Ol=Q]=SX=UV=WT=X]=Z5=[E=\U=\V=\W=]`=^e=_j=a`=cQ=eL=gO=iJ=kN=mR=oC>1?>3E>5K>7Q>8h>:@>;W><o>=0>=1>=2>>7>?<>@A>AF>BR>C[>Dd>Ec>Fo>G0>HC>I_>J^>Kg>Kh>Ki>Kj>MZ>OR>QB>S;>U4>VZ>XK>ZF>\A>^<>_b>a0>b>>cN>dV>e^>ff>gn>i:S2FBS2FBS3CRTS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END12rgS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc4END27rawjunk3HTc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x444END14RLEN3RA12p12Lv3x323x453x463x475POST0S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x264END14RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x444END14RLEN3RA22p12Lv3x323x453x463x475POST0S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp3tbq7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA12rg3Hrg2Kt3K982HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x264END14RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S3CRTFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv2p24Hp2rS2FBFS2FBS3CRTS3CRTFFFFFFFFS3CRTFFFFS3CRTFS1R3NS14STKc5STKc12sp3CRT2lo3slo2bs4CRT04SLOS4SLOL2FB3sp13SP13SPR3ALO2F04SLOu4SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2Lw1p7rawjunk4END1S3CRTFS7rawjunkFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv3LVRSFFS3CRTFS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp12Lw1p7rawjunk4END1S3CRTFS2sp3CRT2bs2FB3sp13APC2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S3CRTFFS3CRTFS2sp3CRT2bs4CRT02FB3sp12Lw1p7rawjunk4END1FS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS2Lw1p4rawp3Hp14END12p12Lv4Hp1a2p24Hp2rFFFFFS6rawlen2RSSS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS2Lw1p4END12p14Hp1rFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEst5CM8st3x322HxS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEst5CM8st3x322HxFFS4blen2B2S3sp1S2FBFS3CRTFFSS2FBFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R2Lw1p7rawjunk4END1S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R2Lw1p7rawjunk4END1S2Lw1p4END12p12Lv3HLv2p24Hp2rS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS3CRTS3CRTS2FBFS2sp3CRT2lo2bs2FB3sp14FBLO2Lw1p7rawjunk4END1FFFFFS3CRTS3CRTS2FBS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEst5CM8st2x32HxS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2sp3CRT2bs2FB3sp12Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S2ri3HriFFS3CRTFSSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS3CRTFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFFS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFS3CRTS3CRTS2sp3CRT2bs2FB3sp12Lw1p4END27rawjunk4END13HE1S2loFFSFS3CRTFFSFFFFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkSS3CRTFFFS2FBFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R2Lw1p7rawjunk4END1S3CRTS3CRTFFFFFS2FBS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S2Lw1p4END24Hp3'3LWRFFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB72Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14Hp3'3Hp33RA43LWRFFFFFS3CRTFS2rg3HrgS3CRTFFS3CRTFS3CRTFFS2sp3CRT2bs2FB3sp12Lw1p7rawjunk4END12p12Lv3LVRFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R2Lw1p7rawjunk4END1FFFS2sp3sp1FFS2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgFS3CRTS2FBFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4rawp7rawjunk3Hp14END12p14Hp1aS2Lw1p4rawp3Hp14END12p14Hp1rFFFS2ri3Hri1r2Ks1q1HS2rg3Hrg2r02Kt1r2Ks1q1H2H5S1i2HiS3CRTS2rg3Hrg1r2Kt1q1HFS3CRTSS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4END26rawlen4rawp7rawjunk4END13Hp34RLEN3HE1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4END26rawlen4rawp7rawjunk4END13Hp34RLEN3HE12p12Lv3HLvS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2ri3Hri1q1r2r01H2H02q02H4FFS2FBFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA2S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA2S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFSS3CRTFFFS3CRTS2rg3HrgFS3CRTS3CRTFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4FFFFS2FBS3CRTFFFS2FBFFFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1S2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1FS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND3x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND3x341CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB74END26rawlen4rawp7rawjunk4RLEN3RA42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4RLEN3RA42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk2RL4RLEN3RA13RA22HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22rg3Hrg2Kt3K982HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22HB5Ha_st5Hl_st5SAEst2p12Lv2p24Hp2r2KeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp7rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk5HTOPc2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp7rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HBFFFFFFFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB74END27rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk4SBND2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4SBND2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT GINT STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_SERALG"] Lemma S_VER : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv : word) (Lw : word) (p END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k64 k120 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl : word) (tbq : Z) (ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v s7v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv Lw p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 (Z_to_bv 64 (FB + 32))
         (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl (Z_to_bv 64 tbq) ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p + bv_unsigned Lw <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr (CRT + 48) 3 + al_sb AL)) s5v (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 END2)
               (Z_to_bv 64 (FB + 96)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a9200) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp3' Hp3 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    pose proof (bv_unsigned_in_range 64 Lw) as LWR. unfold bv_modulus in LWR. cbn [Z.pow Z.of_N Pos.pow] in LWR.
    (* [comment removed for export] *)
    do 24 zstep.
    idtac "VER-PRE".
    set (END1 := p + bv_unsigned Lw) in *.
    assert (HE1 : p <= END1 /\ END1 <= END2) by (subst END1; clear - LWR Hp3'; lia).
    lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 FSHx; frame_aobj FSHx (FB + 96) 1%nat as OPP; frame_aobj FSHx (FB + 32) 1%nat as OLV end.
    idtac "VER-GT".
    gt_call p END1 (FB + 32) 160 ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 HE1 Hp3).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "VER-GT-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into rg; rename H0 into Hrg end.
    match goal with H : p <= ?q <= END1 |- _ => rename q into p1; rename H into Hp1r end.
    match goal with H : rw_cells _ _ (FB + 32) [C8 ?w] |- _ => rename w into Lv end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HOK end.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Kt; zify_cond Kt.
    2:{ (* [comment removed for export] *)
        zstep. zstep. if_cases K98; zify_cond K98.
        { idtac "VER-TAGERR".
          (* [comment removed for export] *)
          do 3 zstep.
          rewrite (swrap32_land_errsum rg 18446744073709543040) by (clear - Hrg; lia).
          do 3 zstep.
          zstep. if_cases Ks; zify_cond Ks.
          2:{ exfalso. clear - Ks Hrg Kt. r_zero Kt Hrg. change 18446744073709551615 with (Z.ones 64) in Ks. rewrite ?Z.land_ones in Ks by lia. Z.div_mod_to_equations. lia. }
          refold_mu INV2 OW2 hc Lc FSHB.
          eapply free_walk with (Lc := Lc) (r := rg + (18446744073709543040 - 2 ^ 64)); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrg; lia)
                | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-TAGERR-LEFT:" g end ]. }
        idtac "VER-ABSENT".
        (* [comment removed for export] *)
        do 10 zstep.
        refold_mu INV2 OW2 hc Lc FSHB.
        eapply S_SERALG with (Lc := Lc) (END1 := END1) (END2 := END2) (p := p1);
          first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
                | (clear - Hp1r Hp1 HE1 Hp3; lia) | match goal with |- ?g => idtac "VER-ABSENT-LEFT:" g end ]. }
    idtac "VER-TAGOK".
    r_zero Kt Hrg. destruct (HOK R0) as [Hp1a HLv]. clear HOK.
    pose proof (bv_unsigned_in_range 64 Lv) as LVR. unfold bv_modulus in LVR. cbn [Z.pow Z.of_N Pos.pow] in LVR.
    (* [comment removed for export] *)
    do 7 zstep.
    chunk_split K1 4%nat K1a K1b. chunk_split K1b 1%nat KV KVp.
    replace (CRT + 32 + 24) with (CRT + 56) in KV by (clear; lia). replace (CRT + 32 + 24 + 4) with (CRT + 60) in KVp by (clear; lia).
    pose proof GINT as SPI. unfold asn1_get_int_stmtA, A_ASN1_GET_INT in SPI.
    idtac "VER-INT".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPI with (CS := hcs asegs R HIA hc) (PP := FB + 96) (VALP := CRT + 56) (P := p1) (END := p1 + bv_unsigned Lv) (BUF := rawp) (bs := rawjunk) (lo := lo);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact KV | exact CSOKc | exact AB | exact (art_alwf asegs R HIA) | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 HE1 Hp3 Hp1r Hp1a HLv LVR
               | match goal with |- ?g => idtac "VER-INT-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "VER-INT-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into ri; rename H0 into Hri end.
    match goal with H : p1 <= ?q <= p1 + bv_unsigned Lv |- _ => rename q into p2; rename H into Hp2r end.
    match goal with H : ri = 0 -> _ |- _ => clear H end.
    lazymatch goal with KVx : rw_cells _ ?mx (CRT + 56) [C4 _], K1x : rw_cells _ ?mx (CRT + 32) _, KVpx : rw_cells _ ?mx (CRT + 60) _ |- _ => joinc K1x KVx; joinc K1x KVpx end.
    (* [comment removed for export] *)
    zstep. if_cases Ki; zify_cond Ki.
    2:{ idtac "VER-INTERR".
        (* [comment removed for export] *)
        do 4 zstep.
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (bv_swrap 32 e) with (ri - 8704)
            by (try (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia);
                unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648;
                clear - Hri; Z.div_mod_to_equations; lia) end.
        do 5 zstep.
        zstep. if_cases Ks; zify_cond Ks.
        2:{ exfalso. clear - Ks Hri. change 18446744073709551615 with (Z.ones 64) in Ks. rewrite ?Z.land_ones in Ks by lia. Z.div_mod_to_equations. lia. }
        refold_mu INV2 OW2 hc Lc FSHB.
        eapply free_walk with (Lc := Lc) (r := ri - 8704); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hri; lia)
              | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-INTERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    { idtac "VER-OK".
      (* [comment removed for export] *)
      do 4 zstep.
      refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_SERALG with (Lc := Lc) (END1 := END1) (END2 := END2) (p := p2);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
              | (clear - Hp2r HLv Hp1r Hp1a Hp1 HE1 Hp3 LVR; lia) | match goal with |- ?g => idtac "VER-OK-LEFT:" g end ]. }
    idtac "VER-MISMATCH".
    (* [comment removed for export] *)
    do 6 zstep.
    refold_mu INV2 OW2 hc Lc FSHB.
    eapply free_walk with (Lc := Lc) (r := -8806); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear; lia)
          | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-MM-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05]0@C18971418195.397C23922862675.396D11891817072.397D16071854214.397D16901939902.397D40775185266.374D42035635047.397D43665348967.397D56536395888.397D60109196847.374D60109446735.397D67258947169.374K10114639055.397K10499531215.397K10674151503.397K13096823887.397K1396569935.397 K15835051771.374K1607432955.374 K16827801039.397K17610693583.397K21302816458.397K216607946.397  K21870859916.374K22861045682.397K22945712379.374K23131760207.397K26482584271.397K26863261647.397K28281397455.397K30038940111.397K30419638991.397K3179121999.397 K33593216207.397K33980871419.374K3591543988.374 K39316523727.397K40707548879.397K41090868175.397K41095599355.374K42696720207.397K44470506575.397K4568054095.397 K46427712719.397K50191716943.397K50368437455.397K51948751695.397K52147535611.374K57689895247.397K58872734415.397K59270213583.397K63420573106.397K64991401423.397K8908368463.397 L10102288217.2  L10487310937.2  L10687032281.2  L10840411873.2  L10912730231.1  L11183176311.1  L12408374717.1  L12877562377.17 L12880089589.17 L13092792281.2  L1408793817.2   L14402536426.385L14447004729.2  L14786404065.2  L1548849343.87  L15522417010.87 L15771191613.1  L15822417165.2  L1594761485.2   L16023460231.87 L16840545881.2  L1685717371.0   L168650209.2    L17606135897.2  L17611635570.87 L18023395959.1  L18302214263.1  L19912320701.1  L20105749565.1  L204253020.2    L21298324828.2  L21644325741.3  L21654730866.2  L21655103786.371L21866712442.2  L22095213153.2  L22866772043.3  L22941438733.2  L23119474137.2  L23513807686.2  L25160623805.2  L25636326795.2  L26171659739.2  L2621559066.1   L26486612313.2  L26831527741.1  L26875616345.2  L27386516966.1  L2770202465.2   L27940391089.87 L28277369689.2  L29066840183.1  L29345674871.1  L30042772057.2  L30431990105.2  L3058445732.2   L3182954201.2   L32327136116.1  L32454903270.1  L33314616971.87 L33597048665.2  L33817424237.3  L33985112333.2  L3482806040.87  L3532059019.2   L35655538583.72 L3598635821.3   L36307103329.2  L363258721.2    L36460502135.1  L3726076129.2   L37875066173.1  L38070592189.1  L38235734261.1  L39321010521.2  L39864004961.2  L39925292426.362L40228640085.0  L40692963805.87 L40711908697.2  L41060391514.361L41099742989.2  L41103222873.2  L42683970777.2  L43226826465.2  L43571151479.1  L43810982283.2  L44466151385.2  L45057340874.362L4572017369.2   L46354690673.3  L4638061450.87  L46431676249.2  L47049041130.3  L47242118263.1  L47443067297.0  L47870616696.2  L48068055434.87 L48487939594.87 L50187819481.2  L50283706766.12 L50381248345.2  L50925318027.2  L5116735037.1   L51906071000.2  L51908265048.3  L51909129149.1  L51953172697.2  L52160193805.2  L52491779133.1  L53527181501.2  L54676236769.2  L56592702936.2  L57685342937.2  L57798807159.1  L58304389180.12 L58885089625.2  L59257267289.2  L59308586248.2  L59413075133.1  L6008660450.10  L6042617148.1   L60448817524.1  L60754583113.0  L61366595865.362L61401481953.2  L63422184011.3  L64418367100.87 L64526681523.2  L6487220337.3   L64979181145.2  L6522106337.2   L65404616823.1  L66298372189.2  L66332265789.1  L66721351741.1  L66914912701.1  L66925224585.372L6899380056.1   L6906665613.1   L7088503905.2   L7282981857.2   L7382465640.1   L7736014575.2   L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.87  N16755563228.396N19743104207.396N3093475936.396 N40008901739.396N5010012853.396 N53586258358.396O1001933565.397 O10618990077.397O11746403965.397O11930563540.395O14542167037.397O15460105085.397O16350966909.397O17494624509.397O17750585469.397O18155437218.397O18626760061.397O19357757918.394O19770425853.397O19931227630.397O20935596669.397O22221714158.397O30245212782.397O3078286936.397 O32096263534.397O32537874520.397O33239929326.397O33990841394.397O34031148413.397O35592798351.397O366419438.397  O36680917870.397O37630280430.397O39838419581.397O40463046306.397O41843596285.397O42197094638.397O43277289469.397O44195227517.397O4440802429.397 O44425156733.397O44938202843.395O45122245047.397O45423855982.397O45969540168.397O48862730990.397O50473853.397   O50817538813.397O52020260349.397O5312795005.397 O54023336829.397O54381021294.397O55209884805.395O55518239188.395O5585524989.397 O56848487390.394O57201466440.397O57537483645.397O59278274632.397O60687394173.397O60978474237.397O61464066679.397O62206064366.397O63123445358.397O63904362034.397O64128366333.397O64204162429.397O64474006218.397O65961212488.395O66562860014.397O67171060367.397O7590719101.397 P10851408966.397P14461423358.374P14793198662.397P182826822.397  P21647862485.395P21658526154.395P22080053446.397P25154843674.397P25650503468.397P2784312774.397 P3064266499.397 P33810555850.395P3530433324.397 P357446086.397  P36322327750.397P3741301318.397 P39879222214.397P43225306182.397P43817786156.397P46340546774.394P47047506707.397P47876372191.395P50927926572.395P53529750042.397P54662134598.397P61391540294.397P64538971685.397P6480458454.394 P6515303238.397 P66292560634.397P7086878406.397 P7297149254.397 P7750690063.374 P8754630693.397 Q1114360721.371 Q12228163960.371Q16071854214.397Q16472810971.397Q1683847904.370 Q19559412304.371Q19561563123.372Q20032613673.371Q20956602184.370Q21294101882.372Q21767670690.397Q21832736479.397Q21930397408.397Q22961298649.370Q22963397981.371Q25473514713.397Q2803826605.397 Q29775981542.397Q30602208140.370Q32437204119.397Q34669522109.397Q34671242809.372Q39439682456.397Q40550330331.397Q40772909426.373Q40775185266.374Q41414298335.397Q42439168719.397Q42439443119.374Q47957748593.397Q48118064779.397Q48782272621.371Q49698585326.372Q49746198710.397Q49746415830.374Q50231978713.371Q51722040728.397Q52136395990.397Q54624410993.397Q57618602681.374Q57828105177.397Q58743871165.397Q58746002845.370Q58748478874.371Q67038703949.397Q67038978349.374Q67256769633.373Q67258947169.374Q8362820247.397 Q8699115497.374 Q8699324297.397 Q9356559674.374 Q9631849391.371 Q9634015756.372 Q9644583048.397 00000400801>03:04h06?07E08K09Q0;10<@0=W0>Z0?]0@`0Ac0Bf0D:0EN0FQ0GT0HW0IZ0Jn0Lf0N:0O=0P@0QC0RF0SI0TL0UO0VR0Wf0YM0ZP0[S0\V0]j0^m0`00a30b60c90d<0e?0fS0gV0hY0i\0kT0lW0mZ0m[0m\0m]0m^0m_0mc0mh0mi0mj0mk0ml0mm0mn0mo0o^10l11111211311M11N11O11P11Q12_12c12d12i12n12o13013113214814914:14;14<14=14H14I14J14S14X14Y14^14_14c14d15l15m16116516616716816916=16A16^16_16`16a18118219J19K19L19M19Q19R19W19\19`19a19b1:h1:i1<N1<O1=^1=_1=`1=a1=b1=f1=g1=h1>n1>o1?01@l1@m1@n1A21A31A41C01D61D71DG1DH1DI1DN1DV1DW1D\1D]1D^1Dc1Dd1De1Dm1Dn1E21EF1EG1EH1EN1ES1Ed1Ei1Em1En1G41G51G61H]1H^1H_1H`1Ha1He1Hf1Hk1I01I51J;1J?1JD1JE1JF1JJ1JK1JL1LL1LM1LN1Lg1MD1NE1OF1PR1PS1RI1T21T31T41T51T61T71T81T91T:1T;1T<1T=1T>1T?1T@1TA1TB1TC1TD1TE1TF1TG1TH1TI1TJ1TK1TL1TM1TN1TO1TP1TQ1TR1TS1TT1TU1TV1TW1TX1TY1TZ1T[1T\1T]1T^1T_1T`1Ta1Tb1Tc1Td1Te1Tf1Tg1Th1Ti1Tj1Tk1Tl1Tm1Tn1To1U01U11U21U31U41Va1X_1ZL1\91\:1]A1^n1`V1b>1ck1eX1f_1hM1j:1kg1mT1oA20n22V24D26<27d29L2;42<a2>N2?n2A\2CI2DO2F<2Gi2I_2K?2L>2MY2O@2OA2P@2QP2R`2Ra2S`2T[2VF2WA2WB2XA2Y@2YA2Z@2[F2\A2\B2]=2^82_32_42`D2aT2bO2cU2e02e12fT2g[2hg2j;2kd2l_2mZ2oG2oH30`32833333n34i36P38L39\3:l3:m3<^3>:3?>3@<3A:3B8S2FBS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk3x244RLEN3RA22x33x253x263x274POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB71p6rawlen4rawp7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk3x244RLEN3RA22x33x253x263x274POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFFFFS2FBS3CRTFFFFFFFS1R3NS14STKc5STKc12sp3CRT2lo3slo2bs4CRT04SLOS4SLOL2FB3sp13SP13SPR3ALO2F04SLOu4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTFFS2sp3CRT2bs2FB3sp17rawjunkFSFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2FBFS3CRTS3CRTFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFFFS6rawlen2RSFFS4blen2B2S3sp1FS3CRTFS2FBFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFS2FBS2FBFFFFS2FBS2FBS2sp3CRT2bs2FB3sp12F07rawjunkFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFS2FBFS3CRTS3CRTS2loFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END26rawlen4rawp7rawjunk3Hp34RLENFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFFFS2FBFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkFFS2FBSFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FS4END22p12Lw3HLwFFS3CRTS2rg3HrgFS3CRTFFS3CRTFFS2sp3sp1FS2FBS1p4rawp3Hp12p14Hp1aFFS1i2HiS3CRTS2rg3Hrg1r2Kt1q1HS3CRTS2FBSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FFFFS2FBFS3CRTS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2FBS3CRTFFS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x321CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x321CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x321CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x321CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x321CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT GINT STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_SERALG"] Lemma S_TBS : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k64 k120 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x13 x15 x16 x17 s5v s7v s10v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 (Z_to_bv 64 (FB + 32))
         (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 (Z_to_bv 64 (FB + 64)) x13 (Z_to_bv 64 END2) x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) s5v (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) s10v
               (Z_to_bv 64 (FB + 96)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a9168) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp3 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 12 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP. frame_aobj FSH (FB + 64) 1%nat as OLN.
    idtac "TBS-GT".
    gt_call p END2 (FB + 64) 48 ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp3).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "TBS-GT-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into rg; rename H0 into Hrg end.
    match goal with H : p <= ?q <= END2 |- _ => rename q into p1; rename H into Hp1r end.
    match goal with H : rw_cells _ _ (FB + 64) [C8 ?w] |- _ => rename w into Lw end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HOK end.
    (* [comment removed for export] *)
    zstep. if_cases Kt; zify_cond Kt.
    2:{ idtac "TBS-TAG". refold_mu INV2 OW2 hc Lc FSHB.
        eapply ea0_walk with (Lc := Lc) (rg := rg); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrg; lia)
              | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "TBS-TAG-LEFT:" g end ]. }
    r_zero Kt Hrg. destruct (HOK R0) as [Hp1a HLw]. clear HOK.
    idtac "TBS-OK". refold_mu INV2 OW2 hc Lc FSHB.
    eapply S_VER with (Lc := Lc) (END2 := END2) (p := p1) (Lw := Lw) (tbq := p);
      first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
            | (clear - Hp1r Hp1a HLw Hp1 Hp2 Hp3; lia) | match goal with |- ?g => idtac "TBS-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.
  End Call.
End Walk.
