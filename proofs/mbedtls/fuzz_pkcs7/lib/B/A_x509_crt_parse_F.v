(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_get_san_A A_crt_parse_stmt24 A_crt_free_stmt2 A_pkcs7_free A_x509_crt_free A_x509_crt_parse_area A_x509_crt_parse_A A_x509_crt_parse_B A_x509_crt_parse_C A_asn1_get_int_loops A_x509_get_serial A_x509_get_alg A_x509_get_sig_alg A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_dates_A A_pk_parse_stmt A_x509_get_uid A_x509_crt_ext_stmt A_x509_crt_ext_A A_x509_get_sig_A.
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
  Hypothesis SM3 : arl_smalloc R 3 = 0x53398.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_crt_parse_A.STKx R STKc).
  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH0 : 0 <= arl_need_setsh R.
  Hypothesis STKc4 : arl_need_setsh R <= STKc.

  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis ACAL : arl_calloc R = 0x69484.
  Hypothesis ABCMP : arl_memcmp_i R = 0x58704.
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
  Hypothesis PKPARSE : pk_parse_subpubkey_stmtA asegs R HIA PK SI PHIk FFRk CNTk STKk C24k 0xb0158.
  Variables (PHIx : Z -> Z) (FFRx : Z -> Z -> Z) (CNTx : Z -> Z) (STKxx : Z).
  Hypothesis CRTEXT : x509_crt_ext_stmtA asegs R HIA PHIx FFRx CNTx STKxx (LFMAX_CRT + 3) A_X509_CRT_EXT.
  Variables (PHIcf : Z -> Z) (FFRcf : Z -> Z -> Z) (STKcf : Z).
  Hypothesis CRTFREE : x509_crt_free_stmtA2 asegs R HIA PK PHIcf FFRcf STKcf A_X509_CRT_FREE.
  (* [comment removed for export] *)
  Hypothesis STKc1 : X509_SIG_ALG_STACK_A + 128 <= STKc.
  Hypothesis STKc2 : arl_need_amem R + 496 <= STKc.
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
  Ltac slot_aobj :=
    lazymatch goal with |- aobj ?sg ?al ?CSx ?mx ?Aslot 8 =>
      let OSL := fresh "OSL" in
      assert (OSL : aobj sg al CSx mx Aslot (8 * Z.of_nat 1));
      [ match goal with SSx : sshad sg al mx _ _ |- _ =>
          let SSg := fresh "SSg" in
          pose proof SSx as SSg; destruct SSg as (_ & _ & SSg);
          eapply aobj_of_zero_shadow with (B := Aslot) (A := Aslot) (g0 := 0%nat) (n := 1%nat) (cs := [C1 (Z_to_bv 8 0)]);
          [ assumption
          | match goal with SCx : crange CSx _ _ |- _ => eapply crange_sub; [exact SCx| xl LFB2| xl LFB2] end
          | xl LFB2 | xl LFB2
          | apply SSg; xl LFB2
          | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; destruct i as [|i]; [reflexivity| lia] ]
        end
      | exact OSL ]
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19084332856.75L19088626119.72L19088626119.73L3488822390.1  00001R02702Q02VS1R2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR3ALO2F02F13APB4SP1R1B1k2HR3Bce3FB'2n'3HR'S1R3HIA1h2sp3CRT2lo2bs5CRTLO2FB3sp11XS1R2sp3CRT2bs3DCD2FB3sp11XS3CRT". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 h sp Q blen BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CWX CRTLO DXB SLOS SLOL SLO SPH LOS DCD sp1 SP1 FRSH APC SPR ALO ACV F0 F1 APB SP1R"] Lemma cstk : forall (hc : HST asegs R HIA) Lh mq, HM asegs R HIA hc Lh LF' mq -> (forall b, In b LB -> In b Lh) -> CRT + 744 <= arl_stklo R.
  Proof.
    intros hc Lh mq HH SUB. destruct (hm_apart asegs R HIA hc _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
    pose proof (art_data_lo asegs R HIA) as DLO.
    destruct (CWX (CRT + 743) ltac:(clear; lia)) as [X|[X|X]]; [xl X| xl X DLO|].
    ddestruct X as ([B k] & HB & HR). cbn [fst snd] in HR. apply in_app_iff in HB. destruct HB as [HB|HB].
    - ddestruct (BR (B, k) ltac:(apply in_app_iff; left; apply SUB; exact HB)) as (_ & _ & Bce & _). cbn [fst snd] in Bce. xl Bce HR.
    - ddestruct (in_fdata_hull LF (B, k) (CRT + 743) HB ltac:(cbn [fst snd]; exact HR)) as ([FB' n'] & HF & HR').
      ddestruct (BR (FB', n') ltac:(apply in_app_iff; right; right; exact HF)) as (_ & _ & Bce & _). cbn [fst snd] in Bce, HR'. xl Bce HR'.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L48789554681.1  L53965678973.20300000500fS3SPcS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB3". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 DIMG STKc2 sp Q blen BUF slo bs LFB2 LFB BIN B1 B2 B3 CRT0 CWX DXB SLOS SLOL SLO SPH LOS sp1 SP1 FRSH CFB APC SPR ALO ACV F0 APB SP1R LFB3"] Lemma owns_pres : forall (hc : HST asegs R HIA) Lc mm mm' LFc SPc SSPc TOPc Wc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    HM asegs R HIA hc (Lc ++ LB) LF' mm -> (forall y, CS y -> hcs asegs R HIA hc y) ->
    presA asegs R (Lc ++ LB) LFc SPc SSPc TOPc Wc mm mm' -> mem_inv asegs mm' ->
    (forall x k, (x + k <= CRT \/ CRT + 744 <= x) -> (x + k <= FB \/ FB + 512 <= x) -> x + k <= lo -> (x + k <= hl_img_lo L \/ hl_img_hi L <= x) -> disjoint_from Wc x k) ->
    owns asegs PK mm' (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk.
  Proof.
    intros hc Lc mm mm' LFc SPc SSPc TOPc Wc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW PERM HH HCSq HP MI' HW.
    unfold owns in *.
    eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := Wc) (SP := SPc) (L2 := Lc ++ LB);
      [exact OW| intros b Hb; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]
      | | exact (blocks_below_hm R HIA hc _ _ mm (Lc ++ LB) HH ltac:(intros b Hb; exact Hb)) | pose proof ACV; lia| exact MI'|].
    - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP)| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
    - intros [x k] Hb Hk. cbn [fst snd] in Hk |- *.
      assert (XL : In (x, k) Lc) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
      ddestruct (own_apart hc Lc mm x k HH HCSq XL Hk) as (A1 & A2 & A3 & A4 & A5).
      apply HW; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Ltac to_free := repeat (lazymatch goal with |- _ (MS _ _ (Z_to_bv 64 693608) _ _ _ _) => fail | |- _ => zstep end).

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L53965678973.198000014S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  #[using="sp blen bs LFB2 LFB B2 sp1 ACV LFB3 LFB512 LFB511 LFB7"] Lemma owns_grow : forall (hq : HST asegs R HIA) Lq Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
    owns asegs PK mq (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    HM asegs R HIA hq ((Lq ++ Lc) ++ LB) LF' mq -> mem_inv asegs mq ->
    owns asegs PK mq ((Lq ++ Lc) ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk.
  Proof.
    intros hq Lq Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW PERM HH MIq. unfold owns in *.
    eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := @nil ivl) (SP := bv_unsigned sp) (L2 := (Lq ++ Lc) ++ LB);
      [exact OW| intros b Hb; apply in_app_iff; left; apply in_app_iff; right; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]
      | apply heap_presx_refl | exact (blocks_below_hm R HIA hq _ _ mq _ HH ltac:(intros b Hb; exact Hb)) | pose proof ACV; lia| exact MIq| intros b Hb Hk; exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="HMND"] Lemma nodup_of_perm : forall (hq : HST asegs R HIA) Lx mq (l : list blk),
    HM asegs R HIA hq (Lx ++ LB) LF' mq -> Permutation Lx l -> List.NoDup (map fst l).
  Proof.
    intros hq Lx mq l HH P. pose proof (HMND _ _ _ _ HH) as N. rewrite map_app in N. apply NoDup_app_inv_l in N.
    eapply Permutation_NoDup; [apply Permutation_map; exact P| exact N].
  Qed.

  (* [comment removed for export] *)
    
  (* [comment removed for export] *)
  #[using="Type"] Lemma cnt24_small_all : forall l : list blk, (forall b, In b l -> snd b < 5889) -> cnt24 l = 0.
  Proof.
    induction l as [|[A k] l IH]; intros H; [reflexivity|].
    rewrite cnt24_cons_small by (apply (H (A, k)); left; reflexivity). apply IH. intros b Hb. apply H. right. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L60281290533.179000011S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lx". (* [comment removed for export] *)
  #[using="LF sp CRT blen bs LFB2 LFB B2 FB sp1 LFB3 LFB512 LFB511 LFB7"] Lemma cnt24_small_app : forall (Lq Lx : list blk), (forall b, In b Lq -> snd b < 5889) -> cnt24 (Lq ++ Lx) = cnt24 Lx.
  Proof. intros Lq Lx H. rewrite cnt24_app, (cnt24_small_all Lq H). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    
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
    replace (Z_to_bv 64 362244) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite ABCMP; reflexivity);
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L22573296152.182L31489692490.182L55718059222.18200001702<03ES4FFRk2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71HS4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71HS4CNTk5CNTk02LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD2_E : forall (hc : HST asegs R HIA) Lc a, BUD2 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    intros hc Lc a B Ha. eapply BUD_E; [exact B| | | | exact Ha]; unfold KVc, KFc.
    - pose proof (PHIk0 blen B2). lia.
    - pose proof (FFRk0 blen (d + 1) B2). lia.
    - pose proof CNTk0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma free_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k104 k112 k120 : word) (r : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (s6v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7v s9v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> -2^31 < r <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 r) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9568) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.free_walk ]; first [ eassumption | (clear - STKc2; lia) ].
  Qed.

  
  (* [comment removed for export] *)

  Hypothesis S_ISSUER : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (rawjunk : list byte)
      (k24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUD2 hc Lc a -> 0 <= a <= p - rawp -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (CRT + 88)) (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 (CRT + 56))
               (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9ad8) fc None mm (seg_rom asegs)).

  Local Notation BUD1 hc Lc a := (BUD hc Lc (2 * blen + AVOL_CALL) (Z.max 0 (fr_charge (d + 1))) 1 a).

  (* [comment removed for export] *)
  Ltac joinc H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mq ?A1 ?cs1 => lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      let Hj := fresh "J" in
      assert (Hj : rw_cells sg mq A1 (cs1 ++ cs2))
        by (apply (proj2 (rw_cells_app sg mq A1 cs1 cs2)); split; [exact H1|]; cbn [cells_size csize Nat.add];
            match goal with |- rw_cells _ _ ?a _ => replace a with A2 by (clear; lia) end; exact H2);
      clear H1 H2; rename Hj into H1; cbn [app] in H1 end end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L12183083268.183L13529316230.183L30047538062.18300001e02n043S4FFRk2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a2Ha1HS4CNTk5CNTk02LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71H". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD1_E : forall (hc : HST asegs R HIA) Lc a, BUD1 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    intros hc Lc a B Ha. eapply BUD_E; [exact B| | | | exact Ha]; unfold KVc, KFc, X509_SIG_ALG_PHI, X509_SIG_ALG_FFR.
    - pose proof (PHIk0 blen B2). unfold AVOL_CALL. lia.
    - pose proof (FFRk0 blen (d + 1) B2). lia.
    - pose proof CNTk0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05?0AD20225638161.418 D20225638161.FileD20955089374.390 D26983003230.390 D30821883090.390 D36735676505.390 D40775185266.368 D49506809303.390 D49848874002.390 D52045925387.416 D53340075670.418 D55494011410.390 D58328744606.390 D60109196847.368 D6203698357.416  D64348882538.392 D64348882538.418 D67258947169.368 K15835051771.368 K1607432955.368  K21870859916.368 K22945712379.368 K33980871419.368 K41095599355.368 K52147535611.368 L10370335306.1   L10709417473.1   L10728809071.1   L11680507981.1   L12408374717.1   L12742609677.1   L12852162731.94  L12877562377.17  L12878060153.15  L13435377522.94  L13459846764.94  L13970712861.2   L14447004729.2   L14601052031.2   L15236898125.1   L1540615640.71   L15733126029.1   L15771191613.1   L15822417165.2   L1594761485.2    L16301095949.1   L16415873118.2   L1685717371.0    L17421091449.94  L17493132150.74  L18456039436.1   L18795368013.1   L18822296706.2   L19095598701.94  L19300970603.2   L19678281629.2   L19857465613.1   L19912320701.1   L19979998541.94  L20105749565.1   L20126440077.1   L20327116736.94  L20451630073.1   L20515527053.1   L20711180045.1   L20843058127.3   L20955186169.1   L21081411357.2   L21866712442.2   L22339500125.2   L22518963564.94  L22740844109.1   L22941438733.2   L23287303292.94  L2340478349.1    L23426722737.94  L23513807686.2   L23766154372.389 L24265606429.2   L24657553080.2   L24871496179.94  L25102488557.94  L25954996165.94  L26171659739.2   L26285623930.78  L26292270060.94  L26744172860.94  L26793125277.2   L26831527741.1   L26982776441.1   L27165754509.1   L27386516966.1   L28288529690.94  L28573826556.5   L28631860810.357 L2927301405.2    L29393059789.1   L29964706882.2   L30032352717.1   L30724229517.1   L30822045429.1   L30917670669.1   L31225530667.94  L31439037308.94  L31559069581.1   L31863041268.94  L32454903270.1   L32482732850.94  L33399721565.2   L33434441852.356 L33450796305.2   L33484763755.94  L33905920925.2   L33985112333.2   L34745243021.1   L34809337279.2   L3482806040.94   L34847234354.94  L35117551757.1   L35330472652.0   L35655538583.72  L36774890701.1   L37622627047.5   L37875066173.1   L38070592189.1   L38106467394.2   L38235734261.1   L38673925517.1   L38706474815.2   L39280637297.0   L40281191306.3   L40514581597.2   L40790539855.3   L41099742989.2   L4185193565.2    L41998759114.6   L42036873485.1   L4324009324.94   L43583719247.0   L44186774511.18  L44190493227.18  L44688625423.3   L44949332381.2   L45074463283.94  L45147374349.1   L4548976171.94   L45519687181.1   L45950822922.357 L46369452317.2   L46909490475.2   L47351156018.94  L48207532493.1   L49076073229.1   L49848974901.1   L50550928513.1   L50680883883.2   L5116735037.1    L51181258317.1   L51557960285.2   L51580144688.381 L51766002381.1   L51909129149.1   L52059965341.2   L52160193805.2   L52405564193.0   L52491779133.1   L53516897302.94  L5480224889.0    L54979092812.1   L55224207780.3   L55225352820.2   L55493845045.1   L55626040626.94  L56384362125.1   L56409795185.3   L56655544333.1   L57206844985.94  L5823287949.1    L58257939116.94  L58328713401.1   L58677014621.2   L5898948237.1    L59308586248.2   L59308668946.3   L59413075133.1   L59711097721.94  L60027173995.94  L60159204715.94  L6042617148.1    L60733421580.1   L60754583113.0   L611762222.1     L6124910643.94   L62302669100.94  L62613891917.1   L62765686937.398 L62779075777.1   L63463873746.3   L63692769805.1   L636961357.1     L63768307213.1   L64418367100.94  L64531950877.2   L65505504565.1   L65543385342.94  L65734936269.435 L65976852173.1   L66293912477.2   L66332265789.1   L6670556782.1    L66721351741.1   L66914912701.1   L66946921596.94  L67367117072.94  L68088190221.1   L6899380056.1    L6906665613.1    L7382465640.1    L7736014575.2    L8124131149.1    L813745101.1     L8707788877.1    L8793638983.75   L9080482849.71   L9261773325.1    L9379661709.1    P13968675114.416 P14461423358.368 P14832643384.416 P18820123829.416 P19676235690.416 P21083584298.416 P22141042872.416 P22341517418.416 P24267652394.416 P26027233478.416 P26791091626.416 P2925144874.416  P29449380920.416 P29966736501.416 P30285664973.416 P33007855928.416 P33142142662.416 P33380168760.416 P33401763434.416 P33903768490.416 P34494424905.416 P38108640373.416 P3982673080.416  P40516602986.416 P4183147626.416  P426308536.416   P43042636636.416 P44185672902.416 P44947298730.416 P46371473706.416 P46849745705.416 P47607750712.416 P47803277752.416 P51300512454.416 P51359658680.416 P51560133226.416 P52062142378.416 P54467803334.416 P58668062264.416 P58674972778.416 P62226537272.416 P62792329144.416 P64529782058.416 P65782836280.416 P66291887018.416 P7750690063.368  P7852086470.416  Q13195385376.364 Q13968675114.416 Q14601039710.416 Q15985628819.418 Q16952477917.365 Q16956656255.364 Q17724805761.365 Q18564560673.365 Q18820123829.416 Q19300159853.416 Q19561509194.381 Q19561624278.416 Q19676235690.416 Q20843311817.416 Q21083584298.416 Q22341517418.416 Q24267652394.416 Q24980047854.364 Q25389680632.365 Q2676383091.418  Q26791091626.416 Q27284027462.364 Q27652675712.381 Q2925144874.416  Q29966736501.416 Q33401763434.416 Q33903768490.416 Q34517156803.381 Q34809324958.416 Q38108640373.416 Q38706454302.416 Q40516602986.416 Q40772909426.367 Q40775185266.368 Q40789761865.416 Q4183147626.416  Q42439443119.368 Q44688879113.416 Q44947298730.416 Q46371473706.416 Q46909776941.416 Q48656960384.364 Q48782272621.365 Q49698585326.366 Q49746415830.368 Q50681645997.416 Q51560133226.416 Q52062142378.416 Q53577458638.416 Q55613122833.365 Q57618602681.368 Q58674972778.416 Q6203698357.416  Q64529782058.416 Q66291887018.416 Q67038978349.368 Q67256769633.367 Q67258947169.368 Q68266720225.416 Q8699115497.368  Q9633798953.416  Q9633945781.381  00001H01I02\03o05B06U07f0990:L0;c0=;0>N0?a0A;0BN0BO0Cg0E80FF0GT0Hb0J00K>0LL0MZ0M`0Me0Mj0Mo0N40N90NS0NT0NU0Oc0PF0PG0PH0PI0PN0Pd0Pi0Pn0Po0Q00Q50Q?0Q@0Q^0R=0RB0RG0RH0Sc0Sd0Se0Sj0So0UJ0UO0UT0WW0W\0Wa0Wf0Wg0Wl0Wm0Wn0Wo0Yb0Yg0Yh0[70[<0\d0\o0]00]10]20]U0^80_>0_G0a00aS0bb0bc0bh0bm0c20c60cj0d;0e90e:0e?0e@0eE0eJ0eO0eT0en0g=0gB0hP0hT0jB0jC0kJ0kX0l20l30l40l90l:0mJ0nN0nS0nT0ol10110<10A10F10G10K10P10Q10R10[10\10]10^10_10m11211U11V11W11X11Y11Z12=12B12\12a13_13`13a15I15N15S15X15]15^15c15h15i17<17A17F17G17H17I17N17h17i17n17o18718<19d19i1:51::1:X1:]1;@1;E1;F1;K1;Q1;Z1;_1<=1<_1=91=>1=C1=D1=I1=l1?_1?d1C81C=1CI1CN1CS1CX1E;1E<1EA1FO1IV1I[1I\1Ia1If1Ik1J01K?1M61M;1M?1MD1MH1MI1MN1MS1MX1OX1P11P61P;1QK1SC1U@1VP1W`1Y01Zm1\=1]M1_B1`R1ab1c_1do1fH1hE1j:1l71mG1nW20L21\23V24f26628329m2;b2=22>B2@?2B<2D92En2Gk2I;2JK2LF2NC2OS2QP2SJ2TZ2VW2Wg2YW2[L2\\2\]2^O2^P2_G2`>2aN2bm2bn2dh2fE2gb2gc2i`2ia2ib2ic2jZ2km2m:2m;2n22o:2o;2o<2o=2o>30F32832933k33l35636@38=38>39S3;P3;Q3;R3=L3>k3?j3@n3BQ3DK3DL3DM3EY3FP3Gb3Gc3Ho3I03I13Jg3L13M;3N_3PJ3QU3R`S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk1x2HxFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS4rawpS3CRTS3CRTS3CRTS3CRTS3CRTS2sp3CRT2bs2FB3sp17rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkFFFS3CRTS2sp3CRT2bs2FB3sp13SP1S3CRTS3CRTFFS3CRTS3so34SO3RSS2sp3CRT2bs2FB3sp13APC7rawjunkS2sp3CRT2bs2FB3sp14rawp3ap13HA1S3CRTS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4rawp3ap17rawjunk2RP3HA1FFS3CRTS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkS3CRTS3CRTS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk4HA1'3RA33RA4S3CRTS3CRTS3CRTFS3CRTFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk2RL3HA14HA1'3RA13RA2S3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS3CRTS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS6rawlen2RSFFSS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S4blen2B2S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk4HA1'4RLENS2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS3CRTS3CRTS2FBS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F02F14SP1R7rawjunkS1R3CRT3DCD2xx2DxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FS3CRTFS3CRTS3CRTS3CRTS3CRTS2sp3CRT2bs2FB3sp17rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS2FBS1R3NS14STKc5STKc52sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunk5STKc6FS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7S4rawp7rawjunkS2sp3CRT2bs2FB3sp17rawjunkFFS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS1R4STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkS3CRTSS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS3CRTS3CRT1x3Hx1S3CRTS3CRTFS2loS3CRTFSS1R3HIA1hFFFFS3CRT2xx2kk2Y1S3CRTS2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkSFFFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS3CRTS2sp3CRT2bs2FB3sp17rawjunkS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FFS1R3NS14STKc5STKc22sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS3CRTS3CRTS3CRTS3CRTFS3CRTS3CRTFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS3CRTS3CRTFFSS3CRTS2sp3CRT2bs2FB3sp17rawjunkSS3CRTFS2rc3Hr3S3CRTS1R3NS14STKc5STKc32sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS3CRTS1p4rawp3Hp1S3CRTS2sp3CRT2bs2FB3sp13APC7rawjunkS3CRTS2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkS3CRTFS3CRTS1i2HiS1o2O02EoS3CRTS2sp3CRT2bs2FB3sp13APC7rawjunkS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkS2sp3CRT2bs2FB3sp17rawjunkS3CRTS3CRTSS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk2RL3HA14HA1'3RA13RA2S3CRTS1R3HIA4PHIk4FFRk5PHIcf5FFRcf4PHIj4FFRj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc6rawlen4rawp3so33ap17rawjunk2RL3RBL2V12V22BV2BF1H2H02H52H62H72H8S3CRTS1R3CRT4CSTKS3CRTS3CRTS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA1FS3CRTS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp3so33ap17rawjunk4HA1'3RA4S1R3HIA4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2Lc6rawlen4rawp3so33ap17rawjunk2RL3RBL2V12V22V33hq31o3HV34HFR32LO2D0S3CRTFS3CRTS3CRTS3CRTS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S3CRTS2FBS3CRTS2FBFS3CRTS3CRTS3CRTS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaS2sp3CRT2lo2bs2FB3sp13SP1S3CRTS3CRTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7FS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk1c2HcFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKFS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk4CSTKFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72HB5Ha_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB73ver5HTOPc2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB73ver2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc4rawp3so33ap17rawjunk3HSc5HTOPcS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB73ver5HTOPc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74rawp3so33ap17rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 NB1 NM1 NF1 DIMG HMND SIGALG STKcf CRTFREE STKc1 STKc2 STKc3 STKc5 STKc6 STKcfr PHIj0 FFRj0 CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD UW BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_ISSUER"] Lemma S_SIGALG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (k24 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128))
         (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (CRT + 88)) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (CRT + 56))
               (Z_to_bv 64 END1) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9a7c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    pose proof (bv_unsigned_in_range 64 so3) as SO3R. unfold bv_modulus in SO3R. cbn [Z.pow Z.of_N Pos.pow] in SO3R.
    (* [comment removed for export] *)
    do 8 zstep.
    zstep. if_cases Kv; zify_cond Kv.
    2:{ idtac "SA-VERSION". refold_mu INV2 OW2 hc Lc FSHB. to_free.
        eapply free_walk with (Lc := Lc) (r := -9600); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear; lia)
              | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "SA-VER-LEFT:" g end ]. }
    clear Kv.
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "SA-PRE".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    owns_now OWm hc Lc. si_mu.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => rename HHx into HHg end.
    destruct (raw_side hc Lc mg _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    assert (RINc : In (rawp, Z.of_nat (length rawjunk)) ((Lc ++ LB) ++ fdata LF')) by (apply in_app_iff; left; exact RIN).
    destruct (bslice mg rawp rawjunk ap1 (bv_unsigned so3) RBY HA1 ltac:(clear - SO3R; lia) ltac:(rewrite RLEN; exact HA1')) as [OXB OXL].
    assert (K3' : rw_cells asegs mg (CRT + 88) (buf_cells so1 so2 (bv_unsigned so3) ap1)) by (unfold buf_cells; rewrite definitions.Z_to_bv_bv_unsigned; exact K3).
    chunk_split K15 3%nat K15a K15z. chunk_split K15a 2%nat K15b KOPT. chunk_split K15b 1%nat KMD KPK.
    replace (CRT + 720 + 4) with (CRT + 724) in KPK by (clear; lia). replace (CRT + 720 + 8) with (CRT + 728) in KOPT by (clear; lia).
    lazymatch goal with FSHx : rw_cells _ mg (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 128) 3%nat as OPARg end.
    pose proof (cstk hc _ _ HHg ltac:(intros b Hb; apply in_app_iff; right; exact Hb)) as CSTK.
    assert (UWS : uwc asegs mg (arl_stklo R) (hstkhi asegs R HIA h) (CRT + 728) sp1 0) by (apply uwc_data; [clear; lia| clear - CSTK; lia]).
    assert (BPS : havol asegs R HIA hc + X509_SIG_ALG_PHI <= AVOL_MAX /\ hfr asegs R HIA hc + X509_SIG_ALG_FFR 0 <= FR_MAX).
    { ddestruct B1' as (V1 & V2 & _). pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc, KVc, KFc in BV, BF.
      pose proof (PHIk0 blen B2). pose proof (FFRk0 blen (d + 1) B2). pose proof (PHIj0 blen B2). pose proof (FFRj0 blen d B2). pose proof (PHIj0 0 ltac:(clear; lia)). pose proof (FFRj0 0 d ltac:(clear; lia)).
      pose proof (PHIj_mono 0 blen ltac:(clear - B2; lia)). pose proof (FFRj_mono 0 blen d ltac:(clear - B2; lia)).
      pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). lia. }
    destruct BPS as [BPV BPF].
    pose proof SIGALG as SPS. unfold x509_sig_alg_stmtA, A_X509_GET_SIG_ALG in SPS.
    idtac "SA-CALL".
    lazymatch type of OXB with bytes_at _ _ _ ?oxsz =>
    eapply aevtA_call;
    [ intros mo1 [HK1 MF1];
      eapply SPS with (h := hc) (LB := Lc ++ LB) (LF := LF') (OID := CRT + 88) (OP := ap1) (OLEN := bv_unsigned so3) (PAR := FB + 128) (MD := CRT + 720) (PK := CRT + 724) (OPTS := CRT + 728)
                      (BUF := rawp) (pp := pp1) (o0 := 0) (lo := lo) (slo := slo) (d := 0) (oxs := oxsz) (bs := rawjunk)
                      (plen := a3) (ptag := a1) (ppad := a2) (otg := so1) (opd := so2) (v1 := sigmd) (v2 := sigpk);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold X509_SIG_ALG_STACK_A;
        first [ exact HHg | exact HK1 | exact K3' | exact OXB | exact OXL | exact RBY | exact KMD | exact KPK | exact KOPT | exact UWS | exact BPV | exact BPF | exact ORAW | exact OPARg | exact TPV
              | exact HPP1 | (rewrite RLEN; exact HPP1) | exact LFB511 | eassumption | reflexivity
              | lazymatch goal with
                | |- aobj _ _ _ _ ap1 _ => eapply aobj_sub; [exact ORAW| xl HA1| xl HA1' RLEN]
                | |- _ => cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3 HA1 HA1' SO3R
                end
              | match goal with |- ?g => idtac "SA-LEFT:" g end ]
    | ] end.
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold x509_sig_alg_postA in PO.
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & rc & LBn & o & nv1 & nv2
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & KMD4 & KPK4 & KOPT4 & HH4 & HALT).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xa9ad4)) with (Z_to_bv 64 0xa9ad4 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
    idtac "SA-BACK".
    (* [comment removed for export] *)
    assert (ELB : LBn = oblk o 8 ++ (Lc ++ LB) /\ (o = 0 \/ (0 < o /\ In (o, 8) LBn))).
    { destruct HALT as [[E1 E2]|(_ & E1 & _ & FRo & _)].
      - subst LBn o. split; [reflexivity| left; reflexivity].
      - destruct FRo as (O0 & _). subst LBn. unfold oblk. destruct (Z.eqb_spec o 0) as [Eo|_]; [exfalso; clear - Eo O0; lia|].
        split; [reflexivity| right; split; [exact O0| left; reflexivity]]. }
    destruct ELB as [ELB HO]. subst LBn. clear HALT.
    pose proof (owns_pres hc Lc mg m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc HP4 MI4
                  ltac:(intros xx kk Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OWt.
    assert (SIP4 : si_P SI m4).
    { lazymatch goal with SIx : si_P SI mg |- _ => eapply (si_heap_presx asegs L SI); [exact SIx| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|] end.
      intros xx Hxx. ddestruct (si_data SI xx Hxx) as (Dx & _ & _). cbn [outside]. clear - Dx DCD. lia. }
    pres_call HP4.
    assert (B23 : BUD2 hq3 (oblk o 8 ++ Lc) 0).
    { ddestruct B1' as (V1 & V2 & V3). unfold BUD. rewrite length_app.
      assert (LO : Z.of_nat (length (oblk o 8)) <= 1) by (unfold oblk; destruct (o =? 0); cbn; clear; lia).
      pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. unfold X509_SIG_ALG_FFR, fr_charge in *. lia. }
    lazymatch goal with STx : stk _ mg lo sp1, SSx : sshad _ _ mg slo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ => clear STx SSx MIx SIx end.
    clear OW OWm HHg RBY ORAW OPARg KMD KPK KOPT K3' OXB UWS.
    presA_transport HP4.
    clear HP4 SPS.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4.
    assert (PERM1 : Permutation (oblk o 8 ++ Lc) (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero o))).
    { rewrite crt_blocks_f_of. rewrite crt_blocks_f_of in PERM. change (oblk 0 8) with (@nil blk) in PERM. cbn [app] in PERM |- *. apply Permutation_app_head. exact PERM. }
    assert (OW1 : owns asegs PK m4 ((oblk o 8 ++ Lc) ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero o rawjunk).
    { pose proof (owns_grow hq3 (oblk o 8) Lc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ OWt PERM HH4 MI4) as OWg.
      unfold owns, crt_own_ok in OWg |- *. ddestruct OWg as (C1 & C2 & C3 & C4 & C5 & C6 & _ & C8 & C9 & _).
      cbn [f_of co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen co_pkinfo co_pkctx co_pkowned cj_raw jraw] in C1, C2, C3, C4, C5, C6, C8, C9 |- *.
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj _ (conj C8 (conj C9 _))))))))).
      - destruct HO as [HO|[HO1 HO2]]; [left; exact HO| right; split; [rewrite <- app_assoc; exact HO2| exact HO1]].
      - exact (nodup_of_perm hq3 (oblk o 8 ++ Lc) m4 _ HH4 PERM1). }
    assert (C241 : cnt24 ((oblk o 8 ++ Lc) ++ LB) <= cnt24 LB + blen / 5889).
    { rewrite <- app_assoc. rewrite cnt24_small_app; [exact C24|]. intros b Hb. unfold oblk in Hb. destruct (o =? 0); [destruct Hb| destruct Hb as [<-|[]]; cbn; clear; lia]. }
    idtac "SA-SWITCHED".
    joinc KMD4 KPK4. joinc KMD4 KOPT4. joinc KMD4 K15z. rename KMD4 into K15.
    fold_cinv INV2 m4 hq3 (oblk o 8 ++ Lc) FSHB. ch_close m4.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    1:{ idtac "SA-ERR". to_free.
        eapply free_walk with (Lc := oblk o 8 ++ Lc) (r := rc); first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | (clear - RS; lia) | (clear - Hr3; lia)
              | (eapply BUD2_E; [exact B23| clear - B2; lia]) | match goal with |- ?g => idtac "SA-ERR-LEFT:" g end ]. }
    idtac "SA-OK".
    eapply S_ISSUER with (Lc := oblk o 8 ++ Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := 0) (p := p);
      first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | exact C241 | exact B23 | eassumption
            | (clear - Hp1; lia) | match goal with |- ?g => idtac "SA-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "09U0@C17025492443.422C18971418195.396C18971418195.425C29926442323.397C35574046291.424C51712377427.423D11891798349.395D11891817072.397D11891817072.425D20466570052.395D20466620537.425D20844746087.425D24582091142.397D27847976046.425D28376451664.397D36733350595.395D38509154553.397D42035635047.397D42035635047.425D42935257027.395D45107520720.425D49496094541.395D49496112240.425D55184611262.397D60109446735.397D60109446735.425D60109460850.395D65507337608.395K13547664719.424K1396569935.397 K1396569935.424 K14687183538.425K16897964495.425K17106139215.424K17512444683.396K19686647503.424K20454862031.424K216607946.396  K216607946.423  K22861045682.397K22861045682.425K23131760207.397K23131760207.424K24009118671.424K26482584271.396K26482584271.423K26863261647.397K26863261647.424K28564342027.395K29188109707.422K30038940111.397K30038940111.424K30419638991.397K30419638991.424K33593216207.397K33593216207.425K35254543439.424K35658759947.395K36298239883.422K37323046346.423K40530704084.422K40707548879.397K40707548879.424K41090868175.397K41090868175.424K44470506575.397K44470506575.424K45612960084.395K4568054095.397 K4568054095.424 K47333372299.423K49686115023.424K49886333707.396K51948751695.397K51948751695.424K52287600975.424K54973417588.425K56590166607.424K5846030287.424 K58872734415.397K58872734415.424K59270213583.397K59270213583.424K60337920975.423K64279710671.424K65498561931.423K67835576015.424K68048910091.396K7066966411.423 K8775721716.397 K8908368463.397 K8908368463.424 L10195936580.3  L10390414532.3  L10544667366.73 L10756207399.4  L10762723780.3  L11177798140.89 L11183176311.1  L11375752077.1  L11691551439.3  L11764842125.1  L11807245377.91 L11958402061.1  L12877562377.17 L12880089585.17 L13176305223.2  L13210332941.1  L13299672782.10 L13334634337.2  L13424471988.91 L13543767769.2  L1358020999.73  L13971728653.1  L1408793817.2   L14522211007.91 L14636542328.2  L14680341835.3  L14843011723.2  L14932124813.1  L15522417010.89 L15529485129.89 L15532814772.91 L15756043635.89 L16768815117.1  L16910905945.2  L17102238681.2  L17500158109.2  L18018172279.1  L1820800555.2   L18302214263.1  L18686846321.3  L18689686129.3  L19039111101.2  L19405001137.89 L19691203929.2  L19964898699.91 L20254488545.2  L204253020.2    L20451630073.1  L20467279705.2  L20643575009.2  L20697497613.1  L20821275233.2  L21218866939.2  L21652623661.369L22046988941.1  L22436075917.1  L22488405914.91 L22540039658.3  L22866772043.3  L23119474137.2  L23228218977.2  L23302419642.91 L23513807686.2  L23723668098.3  L23887513868.1  L24021538905.2  L24619077828.3  L25113340715.91 L25160623805.2  L25185999684.3  L2539095053.1   L26171659739.2  L26188105741.1  L26240581967.3  L26486612313.2  L26864420208.73 L26875616345.2  L26979598561.2  L27386516966.1  L27616704653.1  L27721745707.91 L27757775585.2  L28005787533.1  L28211258445.91 L28394873485.1  L28560379549.2  L29183622685.2  L29345674871.1  L29665765952.20 L29875567739.73 L30042772057.2  L30288275819.89 L30294725037.91 L30431990105.2  L30603190416.73 L31675618311.73 L32327136116.1  L32454903270.1  L32516831197.3  L3276082884.3   L33297154818.20 L33597048665.2  L33817424237.3  L34451277227.2  L3480346590.91  L3482806040.89  L35258380249.2  L35455319922.2  L35655538583.72 L35662656669.2  L36294272029.2  L36460502135.1  L36946886283.2  L37319210588.2  L3790516599.1   L38235734261.1  L38412235745.2  L38515757945.1  L39220054468.3  L40122001783.1  L40147631220.1  L40222164621.1  L40228640085.0  L4037478596.3   L40518352194.2  L40594474381.1  L40711908697.2  L40821209995.3  L4086362840.2   L41103222873.2  L41409160545.3  L42428936461.1  L43166046660.3  L43571151479.1  L44061217931.2  L44266527584.93 L44268624679.128L44466151385.2  L4454456077.1   L44899958847.2  L45157747173.73 L45157874130.108L4560340619.2   L45608534722.2  L4572017369.2   L46106660189.2  L46164190093.1  L46541938681.73 L46542057422.108L47232700279.1  L47337732637.2  L47513680397.1  L47986069697.20 L48487939594.89 L48502769356.91 L48615660178.20 L49026834164.91 L49681561945.2  L49890230429.2  L49997672612.2  L50161695423.2  L50280382404.3  L51580223113.370L51953172697.2  L52283110105.2  L52835511649.2  L52941874306.3  L53083396109.1  L53873652301.91 L54649464481.0  L54793161284.3  L54974961549.3  L55017627405.1  L55085943702.3  L55105288843.2  L5565789826.3   L5606731916.1   L56587419617.2  L56602976729.2  L56847218714.1  L57200105028.3  L57442143775.108L57442270760.73 L57682466925.89 L57798807159.1  L58276111735.1  L5850455129.2   L58885089625.2  L59240339979.3  L59257267289.2  L59308586248.2  L59765243573.1  L60012315821.91 L60056205954.3  L60198256141.1  L60338798689.2  L60342276185.2  L60516634593.2  L60587343117.1  L60754583113.0  L60904615432.91 L60915193550.89 L61323929028.3  L6175900190.73  L62772417203.2  L6291011213.1   L63199674356.386L63199674356.415L6414907617.2   L64283672665.2  L64412253882.91 L64418367100.89 L64584198252.2  L64586655724.3  L64686745924.3  L6487220337.3   L64951446305.0  L65289245065.398L65505504565.1  L65510913565.2  L66187173903.91 L67367117072.89 L67369048534.91 L67506541965.1  L67825443681.2  L67840062809.2  L68061133981.2  L6899380056.1   L6906665613.1   L7079776797.2   L7382465640.1   L7480812975.73  L7640613133.1   L7834046093.1   L7887530605.3   L8206355853.1   L8742280115.2   L8782511373.3   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9230907469.91  L9241280651.89  L9544134509.89  N10874977461.423N17420443258.423N24512369680.396N28651100500.396N30832690335.423N3227350510.396 N43889450811.423N45416640229.423N51315798340.423N56438215324.423N58594013575.396N60073314662.423N63363009604.396N66545377319.396N68022546405.396N6820435427.396 O1051051773.423 O10618990077.397O10618990077.424O11202189437.424O11746403965.397O11746403965.424O11930563540.395O11930563540.422O1261297262.397 O12665829342.421O13403304061.396O13663753544.396O14361883389.423O14664926154.396O1478916974.423 O15264779972.424O16212369554.423O16350966909.397O16350966909.424O17025492443.422O17144234034.425O17494624509.397O17494624509.424O18626760061.397O18626760061.424O19357757918.394O19357757918.421O19770425853.397O19770425853.424O20362071330.423O20458779460.424O20681827268.424O20935596669.397O20935596669.424O2137307261.396 O23018807876.397O23695873954.396O2425934574.397 O24478127342.397O24929774920.396O26714123389.396O27010744648.395O27708878589.423O28210256034.423O2882719044.424 O30013201006.397O30870739931.395O31855893893.395O32537874520.396O32537874520.423O33486960509.424O33655933768.395O337230152.396  O34031148413.396O34031148413.423O34897012705.423O35068890308.425O35592798351.396O35592798351.423O3580528580.424 O39003153661.424O39920534653.424O4013719057.425 O4028702351.423 O40463046306.396O40463046306.423O40784651972.423O41362955959.396O41843596285.397O41843596285.424O42444125821.424O44305896961.396O45345472452.424O45652012797.424O46762886126.396O46796727165.424O4700187630.397 O47718489880.394O48233649620.422O48956366638.395O49761591549.422O50702732434.422O50817538813.397O50817538813.424O51187063933.424O52100284413.424O52246202948.424O52337842036.422O5312795005.397 O5312795005.424 O53955549892.424O54023336829.397O54023336829.425O54362166638.397O55959105092.424O56414299794.422O56427227901.422O56496609880.423O56514360494.422O58080662168.421O58944732014.397O59625529265.422O59806459332.424O60110421998.397O60143181693.423O60687394173.397O60687394173.424O60862671348.395O61237833838.397O62113813117.395O62187197422.397O63904362034.397O63904362034.425O64128366333.397O64128366333.424O64462498030.397O65333132151.397O66180450116.424O66543996142.397O66805662077.425O67704963438.397O67738280189.424O6812381053.424 O7499981970.423 O7590719101.397 O7590719101.424 O76743805.395   O779725764.425  O7960765437.424 O862033604.424  O8719851137.423 P10189109219.424P10397283939.424P10761204579.424P10761940190.425P11680495720.394P13323636166.397P14639119327.395P14837264428.396P1819272332.396 P18674428118.423P18676873174.421P19029103898.423P20261250374.397P20646143558.397P20835442886.397P21212095580.422P22533188115.397P23226657990.397P23737835557.423P24620663395.424P25154843674.396P25154843674.423P25196956131.424P26254726120.421P26993807942.397P27759401030.397P3282951267.424 P33810555850.395P33810555850.422P34453853964.423P35461131733.395P36957875244.395P38409658694.397P39214275427.424P4031765091.424 P40832264492.395P41419110342.422P43151870819.423P44067980844.395P44910232511.423P4550399020.396 P46116577274.396P50012824067.396P50150930751.396P50266205539.425P52845428678.397P52940256805.422P54777977059.424P55088519473.423P55103662124.396P5559018533.423 P56576421190.396P57202738403.424P59225082028.422P60050384933.422P60340425414.397P60531825990.397P61334894435.424P62767929637.423P6420654662.397 P64680999907.424P6480458454.394 P6480458454.421 P67819729350.397P7898593482.422 P8754630693.396 P8754630693.423 Q10281206095.397Q15766564435.425Q16018831318.397Q16472810971.397Q16472810971.425Q17729049152.394Q18560350176.394Q19561351767.369Q19561563123.370Q19965418459.425Q20466620537.425Q21832736479.397Q21832736479.425Q22996294223.425Q24582091142.397Q27652745785.370Q27663313085.425Q28376451664.397Q34517234042.370Q34964382778.425Q38509154553.397Q39439682456.397Q39439682456.425Q39460178071.425Q42439168719.397Q42439168719.425Q44587234302.425Q45107520720.425Q47957748593.397Q47957748593.425Q48099058160.425Q48118064779.397Q48118064779.425Q48360113622.425Q49746198710.397Q49746198710.425Q50052725144.425Q50233692894.369Q54386358946.397Q54938960857.397Q55408699622.397Q57139159520.397Q57390211327.425Q57426677977.397Q58743871165.397Q58743871165.425Q58746002845.369Q62563604959.425Q65188245677.397Q67038703949.397Q67038703949.425Q67933129073.425Q8362820247.397 Q8362820247.425 Q8699324297.397 Q8699324297.425 Q9350267911.372 Q9350270087.395 Q9634015756.370 Q9634063272.369 Q9644583048.397 Q9644583048.425 00000100500900>00C00G01M02S03Y04_05e06k08g0:X0;^0<d0=j0?00@60A<0BB0CH0DN0F<0GK0HZ0Ii0Jo0L20M50N80OJ0PM0QP0RS0SV0TY0U\0V_0Xg0Z90[<0\?0]B0^E0_H0`K0aN0bQ0cT0dW0eZ0f]0g`0hc0if0ji0kl0lo0n20o510811;12>13A14D15G16J17M18P19S1:V1;Y1<\1=_1>b1@81A;1B>1CA1DD1EG1FJ1GM1HP1IS1JV1KY1L\1Nd1Og1Pj1Pk1Pl1QF1QG1QH1RW1R[1R`1Ra1Rf1S@1SE1SF1SG1SO1ST1Se1Sf1U41U51V=1VB1VC1Va1Vb1Vc1Vd1Ve1X31XR1Y`1[B1[G1[H1[I1[J1[N1[O1[P1[Q1[R1[S1\[1\\1^71^81^91^>1^?1^@1^E1^F1^G1_M1_R1_W1a:1a;1a<1a=1a>1bM1bX1bY1b^1b_1b`1cC1cD1cE1cJ1cS1cX1cY1cZ1d41d51d61d:1d;1dY1dZ1d_1eH1eM1eN1eO1eS1f41fQ1fR1g41gV1gW1hc1j41j81j<1jG1jH1k@1kA1kB1kC1lS1mc1md1me1o=1o>1o?1oC1oD1oE1oI1oM1oN1oS1oT1oX1o\1oa1ob1oc1od1oi1oj1ok20320420520:20;20?20@20A20B20C20H20I20J20K20L20M20N20O20T20U20V20Z20[20`21122723=24525]25^25_25`25a25b26h26i26j26k26l27127N27O27P27Q27V27W27X27Y27^27_27`27e27f27g27h28K28O28P28Q28R28S28T28Z28_29A29B29G29H29I29J29O29P2;?2<n2<o2>k2>l2?12?22?32?42?52@\2BC2BK2BL2BM2BN2BO2CZ2C_2C`2D?2F62Gm2H22H32H42H52H92H>2H?2HC2JF2JK2JP2JQ2JV2JW2JX2LX2LY2LZ2M32MP2Mm2NK2NL2O[2P`2RV2Sm2Tn2V32W42X92YA2Zj2[k2[l2\m2^22_>2_?2_@2_A2_B2_C2_D2_E2_F2_G2_H2_I2_J2_K2_L2_M2_N2_O2_P2_Q2_R2_S2_T2_U2_V2_W2_X2_Y2_Z2_[2_\2_]2_^2__2_`2_a2_b2_c2_d2_e2_f2_g2_h2_i2_j2_k2_l2_m2_n2_o2`02`12`22`32`42`52`62`72`82`92`:2`;2`<2`=2`>2`?2`@2`A2`B2`C2`D2`E2`F2`G2`H2`I2`J2`K2`L2`M2`N2`O2`P2`Q2`R2`S2`T2`U2`V2`W2`X2`Y2`Z2`[2`\2`]2`^2`_2``2`a2`b2`c2`d2`e2`f2`g2`h2`i2`j2`k2`l2`m2`n2`o2a02a12a22a32a42a52a62a72a82a92a:2a;2a<2a=2a>2a?2a@2aA2bM2cY2de2fF2h32i`2kH2m62nc2oo31]33E35236_38L38M3:M3<:3=A3>M3@53A]3Bi3DV3FC3H03I<3JC3KJ3M73M83N`3PM3QY3Re3T13U83VD3Wl3YQ3[?3\E3^23_W3`c3bP3cW3dc3el3gT3h[3jH3kT3l`3mg3oT41A42M43m45Z46f48T4:B4;o4=64>V4@64A54B=4Cj4Ck4Cl4ED4Fk4H;4IK4IL4JK4KF4LA4M@4Ng4Ob4P]4Q\4RW4T:4U94V44Vo4W04X64Y<4Y=4Z<4Z=4Z>4Z?4[b4]E4^N4_b4a64b14bl4dW4dX4e^4e_4fg4h?4i:4j54k04kk4lj4nQ50850950:50;51W53354755;569577585593FS2FBS2FBS3CRTS3CRTS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp3spd7rawjunk3x254RLEN3RA22x33x263x273x323x333x344POSTS2LF4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp3spd7rawjunk3x254RLEN3RA12x33x263x273x323x333x344POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF2sp3CRT2bs4LFB22FB3sp1FFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS2FBS3CRTFS3CRTS2sp3CRT2bs2FB3sp17rawjunkS3CRTFFS2lo3sp1S3CRTS2rk3Hrk1r2Kr1q1HFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB24CRT02FB3sp13SP13SPR2F04SLOu4SP1RS3CRTFS2sp3CRT2bs2FB3sp13APC7rawjunkFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2sp3CRT2bs4CRT02FB3sp17rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R7rawjunkS3CRTFFFS2FBFFFFFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFFS3CRTFFS3CRTFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS3CRTS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R1p4END14rawp7rawjunk3Hp12p24Hp2rFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS6rawlen2RSFS3CRTFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkFFS3CRTS4blen2B2S3CRTFFS2LF2sp3CRT2bs4LFB22FB3sp1FFS2FBFS2sp3CRT2bs2FB3sp13APC7rawjunkFS3CRTS2sp3CRT2bs2FB3sp11p4END17rawjunk2p24Hp2rS3CRTFFS2FBS1p4END14rawp3Hp12p24Hp2r2p34Hp3rS2LF2sp3CRT2lo2bs4LFB22FB3sp1FS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS1R3NS14STKc5STKc12LF2sp3CRT2lo3slo2bs4LFB24CRT04SLOL2FB3sp13SP13SPR2F04SLOu4SP1RS2FBS2FBS2sp2lo3sp1FS4END14END26rawlen4rawp4Hp2'3Hp32p22p33x563pp14Hp3r4HPP1FFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFS2FBFFS2FBS2loFS3CRTFS2FBS2FBS3CRTSFFS3CRTFFS2sp3sp1FFS3CRTFS2FBFFFFS3CRTFFFFFFFS3CRTFFS2FBFS3CRTS4END12p22p34Hp3rS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S4END14END26rawlen4rawp4Hp2'3Hp32p22p33x523ap14Hp3r4HA1'S1R3NS14STKc5STKc22sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFFS3CRTS2sp3CRT2bs2FB3sp12F07rawjunkSFFS3CRTFFFS3CRTFFS3sp1FFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS2FBFFFFFS1i2HiS3CRTS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS3CRTFFFS3CRTSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFS3CRTFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2rk3HrkFFFSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1i2HiS3CRTFS2sp3CRT2bs4CRT02FB3sp17rawjunkS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S3CRTFFFS2FBS3CRTFS2FBS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13SP14SP1M3APC3SPR3ALO3ACV2F03APB4SLOu4SP1RS3CRTS3CRTFS3CRTFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT2bs2FB3sp13APC7rawjunkFS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x581CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x351CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x351CS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x581CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x351CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x581CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x581CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x581CS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3x581CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x351CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x581CFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x351CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x351CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x351CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 NB1 NM1 NF1 DIMG HMND SERIAL XALG SIGALG STKcf CRTFREE STKc1 STKc2 STKc3 STKc5 STKc6 STKcfr PHIj0 FFRj0 CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD UW BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_ISSUER"] Lemma S_SERALG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (k24 s11v s7v x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128))
         (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 (Z_to_bv 64 (FB + 96)) x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 (CRT + 56))
               s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9a18) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 6 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP. frame_aobj FSH (FB + 128) 3%nat as OPAR.
    pose proof SERIAL as SPR'. unfold x509_get_serial_stmtA, A_X509_GET_SERIAL in SPR'.
    idtac "SER-CALL".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPR' with (CS := hcs asegs R HIA hc) (PP := FB + 96) (SER := CRT + 64) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (lo := lo);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact K2 | exact RBY | exact ORAW | exact OPP | exact CSOKc | exact AB | exact (art_alwf asegs R HIA) | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
               | match goal with |- ?g => idtac "SER-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "SER-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -12288 < ?r <= 0 |- _ => subst x; rename r into rk; rename H0 into Hrk end.
    match goal with H : p <= ?q <= END1 |- _ => rename q into p2; rename H into Hp2r end.
    match goal with H : rk = 0 -> _ |- _ => clear H end.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "SER-ERR". refold_mu INV2 OW2 hc Lc FSHB. to_free.
      eapply free_walk with (Lc := Lc) (r := rk); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrk; lia)
            | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "SER-ERR-LEFT:" g end ]. }
    rename rk into rk0. rename Hrk into Hrk0. clear Kr.
    (* [comment removed for export] *)
    do 6 zstep.
    pose proof XALG as SPA'. unfold x509_get_alg_stmtA, A_X509_GET_ALG in SPA'.
    idtac "ALG-CALL".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPA' with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (ALG := CRT + 88) (PAR := FB + 128) (P := p2) (END := END1) (BUF := rawp) (bs := rawjunk) (lo := lo);
         rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc;
         first [ exact HHx | exact LOS | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3 Hp2r
               | slot_aobj
               | match goal with |- ?g => idtac "ALG-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "ALG-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -12288 < ?r <= 0 |- _ => subst x; rename r into rk; rename H0 into Hrk end.
    match goal with H : p2 <= ?q <= END1 |- _ => rename q into p3; rename H into Hp3r end.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    2:{ idtac "ALG-ERR". refold_mu INV2 OW2 hc Lc FSHB. to_free.
        eapply free_walk with (Lc := Lc) (r := rk); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrk; lia)
              | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "ALG-ERR-LEFT:" g end ]. }
    r_zero Kr Hrk. ddestruct (POST R0) as (ap1 & pp1 & -> & -> & HA1 & HA1' & HPP1). clear POST.
    idtac "ALG-OK". refold_mu INV2 OW2 hc Lc FSHB.
    eapply S_SIGALG with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (p := p3);
      first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
            | (clear - Hp2r Hp3r Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1; lia) | match goal with |- ?g => idtac "ALG-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.
  End Call.
End Walk.
