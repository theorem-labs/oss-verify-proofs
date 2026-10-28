(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_get_san_A A_crt_parse_stmt24 A_crt_free_stmt2 A_pkcs7_free A_x509_crt_free A_x509_crt_parse_area A_x509_crt_parse_A A_x509_crt_parse_B A_asn1_get_int_loops A_x509_get_serial A_x509_get_alg A_x509_get_sig_alg A_x509_get_name_stmt A_x509_get_name_stmtE A_x509_get_dates_A A_pk_parse_stmt A_x509_get_uid A_x509_crt_ext_stmt A_x509_crt_ext_A A_x509_get_sig_A.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "02k0@L1685717371.0   L23886653674.402L23886653674.403L24023900370.0  L25054448960.396L27386516966.1  L32454903270.1  L35655538583.72 L38235734261.1  L42411609006.0  L59308634497.2  L60754583113.0  L6899380056.1   L6906665613.1   L7382465640.1   L8171953640.402 L8171953640.403 L8793638983.75  L9080482849.71  P324046647.406  P324046647.407  P33641443928.406P33641443928.407P7903954312.406 P7903954312.407 Q10594415770.402Q10693994654.402Q11939405141.389Q12945255385.385Q13002548137.401Q13676950804.384Q13963846262.395Q15752730517.399Q16027744916.401Q17008039385.401Q17425018425.401Q17454195172.380Q18089490443.401Q18102023734.401Q18798454873.401Q18872097273.401Q20459834793.401Q20464211549.391Q21472160986.386Q2154666025.401 Q2159599449.401 Q22190969305.401Q23928089235.393Q2410696150.390 Q24316579417.401Q2605123161.401 Q26074198841.401Q26502553036.375Q26920001688.388Q26987112345.379Q27665131153.399Q27875065177.401Q28234306710.400Q28776606169.401Q29123745940.401Q29499247193.401Q29648483289.401Q29732373684.401Q30439524718.396Q30995755538.382Q3181278517.402 Q32756490293.402Q33055635801.401Q34416871179.401Q34420984118.401Q34667111065.401Q35010575583.393Q36084925017.401Q36579641128.380Q36940995257.401Q3799283926.403 Q38511566558.392Q39043165210.390Q39850762830.406Q39850762830.407Q39857052210.376Q39976042025.401Q40513117017.401Q40599399476.401Q40989915786.401Q42035624155.387Q42441548847.406Q42441548847.407Q42580734868.398Q4278042260.401 Q43024701277.381Q43580975259.402Q44155788684.375Q44172294453.402Q44298944140.376Q44298944140.402Q44301027056.406Q44301027056.407Q44359965847.387Q44364894805.379Q45526347419.402Q45742289428.401Q45822091830.401Q45834628107.401Q46408772363.401Q46421304630.401Q48119910507.406Q48119910507.407Q49164414041.401Q49247644710.406Q49247644710.407Q49283981588.401Q49748522582.406Q49748522582.407Q49768135673.401Q497883065.401  Q5011256373.402 Q50842763689.401Q51107054235.402Q51283953300.401Q51449427892.401Q51568379999.383Q51691149979.402Q51789435193.401Q51961662993.396Q52332670358.386Q52464623069.394Q52567362035.401Q53213300371.383Q55660191.397   Q5596578838.406 Q5596578838.407 Q56592237972.401Q56970272057.401Q57223845531.402Q57225610745.401Q57620708409.406Q57620708409.407Q57893485213.401Q58040652597.402Q58668296436.401Q58742053010.400Q59617553652.401Q59621696201.401Q59698924043.401Q59703034934.401Q59769434898.392Q60012279769.401Q60133690901.385Q60138834193.381Q60482870325.402Q61097091038.382Q6191098356.406 Q6191098356.407 Q62586361044.388Q62639683769.401Q63435846322.402Q63558047033.401Q63588016984.384Q64228675114.405Q64228675114.406Q64427786041.401Q65213305287.394Q65509695633.391Q65654860420.401Q65674501161.401Q6575031993.401 Q6667361590.401 Q6671471371.401 Q66901779611.402Q67041068973.406Q67041068973.407Q67041083245.395Q67477298324.401Q67837027513.401Q6909946600.403 Q7093291664.398 Q7785411076.401 Q7821780905.401 Q8701202793.406 Q8701202793.407 Q8740343849.401 Q9458709140.401 Q9600193945.389 Q9611917865.401 Q9890590619.397 Q9967504441.401 00000101A02Q02R03L03P03T04l05005105905:05>05C05G05H05I07I07b0900:>0;@0<B0=m0?]0@Q0AE0B=0C50CX0DP0E_0FS0G60GY0H<0I40I50I60IY0J<0J_0KW0LO0M20MU0N80O00Oh0PK0Pn0QQ0R40Rl0Sd0TX0U;0Uo0VR0W50WX0X;0X^0Z40Zl0Zm0[U0\80\[0\\0]P0^H0^k0_c0`F0a:0b20bj0cd0d^0eF0ei0fL0fo0gV0hN0iQ0jT0kH0kk0lc0mK0mn0mo0nW0o?10911311k12c13K13n13o14R15515X17818X19;19<19=19`1;11<B1<e1=H1>01>S1?;1?^1@A1A91Aa1BD1CK1DC1E;1Eb1FZ1GN1GO1GP1H31HV1I>1Ia1Je1Ki1L]1L^1MA1N51N61N71NZ1N[1OS1P61Pn1Qf1RN1SF1TD1UB1V:1V]1V^1WA1X91YR1Zk1[N1\F1]>1]a1^D1^g1^h1_K1`31aW1c;1dY1e<1e_1fS1gG1gj1hM1if1k?1kb1lE1m=1m`1nT1o7SS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB2Lc2KbS2FBS2FBS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2loSS3CRT2KbSS2FBS3CRTS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaS2sp3CRT2lo2bs2FB3sp13SP1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEst4FBLOS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB4SLOu4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKc2 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH LOS DCD SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma exit_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    BUDX hc Lc -> rawlen < 2^40 -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) -> -2^31 < r <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 r) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa957c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. (intros INV CH OW PERM dd_H; ddestruct dd_H as (BV & BF & BC); intros RAWS C24 RR).
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 12 zstep.
    idtac "T-EXIT-1".
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; first [lia | congruence | (apply Kb; reflexivity)]].
    clear Kb.
    idtac "T-EXIT-2".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    lazymatch goal with MIx : mem_inv asegs me |- _ => pose proof (owns_mu hc Lc _ me _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM (proj1 HH0) HCSc MU WM MIx) as OW2 end.
    si_mu.
    ch_close me.
    eapply c_fin with (STKc := STKc) (h := h) (blen := blen) (lo := lo) (slo := slo) (d := d) (mo0 := mo0) (PHIc := PHIc) (FFRc := FFRc) (CNTc := CNTc)
                      (hq := hc) (Lc := Lc) (FB := FB) (sp1 := sp1) (PK := PK) (SI := SI);
      first [ exact CH | exact OW2 | exact PERM | exact RAWS | exact C24 | exact RR | exact BV | exact BF | exact BC | exact HMND | exact CWX
            | eassumption | reflexivity | match goal with |- ?g => idtac "EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0170@D20225638161.406D52056405590.404D6193190632.404 D64348882538.406L11851041672.25 L12821070989.2  L1540615640.71  L15612769108.5  L16048387771.5  L16164988626.27 L19979755003.71 L24621529478.2  L2519780742.2   L27386516966.1  L27805724550.2  L30285685498.71 L32454903270.1  L3482529710.71  L35655538583.72 L38235734261.1  L38849168774.2  L39280637297.0  L39572761278.2  L40281191306.3  L45968223110.2  L47441854301.71 L50790846049.71 L53132297741.26 L57011601798.2  L60754583113.0  L64520705286.2  L66623553236.3  L6899380056.1   L6906665613.1   L7382465640.1   L896703213.26   L9080482849.71  P12833736423.404P24617417708.404P2532413420.404 P26033547931.404P27809869292.404P30296172688.404P33144212635.404P34509118740.404P38844893164.404P44179367579.404P45955557868.404P51294226587.404P54465708699.404P57024267244.404P7866756763.404 Q12833736423.404Q13118096298.404Q19546949771.404Q24617417708.404Q2532413420.404 Q2676383091.406 Q27809869292.404Q38844893164.404Q39566209509.404Q42439449395.404Q45955557868.404Q53579569555.404Q56843884402.406Q57024267244.404Q64514416506.404Q66639013263.404Q67038984369.404Q68281369020.404Q9644302708.404 00002404706608:09f09g0:=0:J0:U0<G0=Z0=[0=\0=`0=a0><0>@0?H0@`0@d0@e0@f0@g0A00A10BT0CT0EB0EC0ED0EE0EF0EJ0EO0ES0GB0G[0IT0KM0MF0Od0Q]0S_0V=0X[0ZT0]20^k0aI0cm0ef0hD0hE0jZ0lg0lh0li0n_0n`0na11D13@13A15615715817S1:61<S1>`1@TS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32RA2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLEN1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB32RA2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32RA2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32RA2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLEN1x2HxS1R3HIA5PHIcf1h4blen4BUDV2hc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3BE12PMFS2sp3CRT2bs2FB3sp13SP1S4blen2Lc3BE3S3CRT1x3Hx1S1R3HIA5FFRcf1h4blen1d2hc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3hq33BE22FM4HFR3S1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1RFFS2FBFS2sp3CRT2lo2bs5CRTLO2FB3sp1S2FBS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1RS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2loFSFS1R3HIA1hFS1R4STKc5STKcf6STKcfr2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1RS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT03LOS2FB3sp13SPR2F04SLOu4SP1RS1R3HIA5FFRcf1h4blen1d4BUDF2hc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3BE22FMFSFFS2FBS3CRTS2FBS1R3HIA5PHIcf1h4blen2hc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3hq33BE12PM3HV3S2sp3CRT2lo2bs2FB3sp13SP1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32hc2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3HSc5HTOPc4PLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB32RA2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3HRA4PLENFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLEN1c2HcFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLENS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB32hc2Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned3HSc5HTOPc4PLENS2LF4blen2bs4LFB23LFB2B22FB2F04LFB32Lc2ob6rawlen4rawp5inext5snext6pkinfo5pkctx2eo7sigopts6inodes6snodes7pkowned4PLEN". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 NA1 HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma free_call : forall (RA : Z) (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (hq : HST asegs R HIA) (mq : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       cinv [] mq hq FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ->
       crt_zero asegs mq CRT -> BUDX hq [] ->
       aevtA asegs (KF asegs R HIA hq mo0) POST
         (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 y12 y13 y14 y15 y16 y17
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v y28 y29 y30 y31)
             F (Z_to_bv 64 RA) fc None mq (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 CRT) x11 x12 x13 x14 x15 x16 x17
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 A_X509_CRT_FREE) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB BE RAWS HRA HRA2 KONT. unfold A_X509_CRT_FREE.
    destruct (crt_at_build asegs PK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CH OW ALC CRT0 CRB) as [jx CAx].
    clear CH OW.
    open_cinv INV hc.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    pose proof (HMND _ _ _ _ HHc) as NDLc.
    pose proof (cstk hc _ _ HHc ltac:(intros b Hb; apply in_app_iff; right; exact Hb)) as CSTK.
    pose proof (Permutation_length PERM) as PLEN.
    ddestruct BE as (BE1 & BE2 & BE3).
    assert (LENK : 0 <= Z.of_nat (length (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts))) <= CNTc blen) by (rewrite <- PLEN; clear - BE3; lia).
    pose proof (PHIcf_mono _ _ LENK) as PM. pose proof (FFRcf_mono _ _ 0 LENK) as FM.
    assert (CWF : client_wrange L (LB ++ fdata LF') lo (htop asegs R HIA hc) CRT CRT_SIZE).
    { rewrite HTc. unfold CRT_SIZE. eapply client_wrange_mono; [exact CWX|]. intros b' Hb'. apply in_app_iff in Hb'. apply in_app_iff.
      destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; apply (fdata_cons_sub b' [] FB 512 LF); exact Hb']. }
    idtac "FREE-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CRTFREE with (h := hc) (LBo := Lc) (LB := LB) (LF := LF') (A := CRT) (lo := lo) (d := 0)
                          (f := f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts) (j := jx);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold CRT_SIZE in *;
        first [ exact HHc | exact HK1 | exact CAx | exact NDLc | exact OCRT | exact CWF | exact STlo | exact LOS | exact MI | exact TPV | exact ALC | exact CRT0 | reflexivity
              | lazymatch goal with
                | |- forall b, In b (crt_blocks _) -> In b Lc => let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]
                | |- co_rawlen _ < _ => cbn [co_rawlen f_of]; exact RAWS
                | |- uw_obj _ _ _ _ => left; split; [exact CSTK| clear; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - PM BE1 BUDV; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - FM BE2 BUDF; lia
                | |- _ <= htop _ _ _ _ => rewrite HTc; xl
                | |- _ => xl
                end
              | match goal with |- ?g => idtac "FREE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & Lo'
                    & E4 & MI4 & ST4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH4 & SUB4 & KEEP4 & CZ4 & REL4).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA : word) by (symmetry; apply ret_pc_even; [exact HRA| exact HRA2]).
    rewrite (unsigned_lit sp1) in ST4, HP4 by exact SP1R. unfold CRT_SIZE in HP4, CZ4.
    idtac "FREE-BACK".
    (* [comment removed for export] *)
    assert (LNIL : Lo' = []).
    { destruct Lo' as [|b0 Lr]; [reflexivity|]. exfalso. apply (REL4 HOB b0 (or_introl eq_refl)).
      apply in_map. eapply Permutation_in; [exact PERM|]. apply SUB4. left. reflexivity. }
    subst Lo'. cbn [app] in HH4, HP4.
    assert (SIP4 : si_P SI m4).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|]. intros a Ha. exact (si_outside1 L SI CRT 744 a DCD Ha). }
    change LB with ([] ++ LB) in HP4, HH4.
    pres_call HP4.
    clear HHc STlo MI SIP jx CAx.
    assert (HTq : htop asegs R HIA hq3 = htop asegs R HIA h) by (rewrite HT3; exact HTc).
    clear_client_facts. client_facts hq3.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    idtac "FREE-SWITCHED".
    fold_cinv INV2 m4 hq3 (@nil blk) FSHB.
    eapply KONT; [exact INV2| exact CZ4|].
    split; [clear - HV3 PM BE1; lia| split; [clear - HFR3 FM BE2; lia| cbn [length]; exact CNTc0]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac zero_exit LEM INVq CZq BXq :=
    lazymatch type of CZq with crt_zero _ ?mq _ =>
      let CH0 := fresh "CH0" in let OW0 := fresh "OW0" in
      pose proof (chunks_of_zero asegs CRT mq CZq) as CH0;
      pose proof (owns_zero asegs PK CRT mq ([] ++ LB) (Z_to_bv 64 0) (Z_to_bv 64 0)) as OW0;
      eapply LEM with (Lc := @nil blk) (rawlen := 0);
        first [ exact INVq | exact CH0 | exact OW0 | exact BXq | reflexivity
              | lazymatch goal with
                | |- Permutation _ _ => cbn; apply Permutation_refl
                | |- cnt24 _ <= _ => cbn [app]; pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP; clear - DP; lia
                | |- _ => idtac
                end ]
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19627675622.79L26466616993.0 L51508673957.0 L67301973408.3 00000100200300?FSSS2LB4blen2DP". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma free_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    intros until x31. intros INV CH OW PERM HOB BE RAWS RR.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    (* [comment removed for export] *)
    do 2 zstep.
    eapply free_call with (RA := 0xa9570) (Lc := Lc); first [ exact INV | exact CH | exact OW | exact PERM | exact HOB | exact BE | exact RAWS | reflexivity | (clear; lia) | idtac ].
    clear LAWS KINV INV CH OW PERM.
    intros hq mq y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INVq CZq BXq.
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    (* [comment removed for export] *)
    zstep.
    zero_exit exit_walk INVq CZq BXq; first [ exact RR | (clear; lia) | match goal with |- ?g => idtac "FREE-EXIT-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02l0@L1685717371.0   L23886653674.402L23886653674.403L24023900370.0  L25054448960.397L27386516966.1  L29010574176.396L32454903270.1  L35655538583.72 L38235734261.1  L42411609006.0  L59308634497.2  L60754583113.0  L6899380056.1   L6906665613.1   L7382465640.1   L8171953640.402 L8171953640.403 L8793638983.75  L9080482849.71  P324046647.406  P324046647.407  P33641443928.406P33641443928.407P7903954312.406 P7903954312.407 Q10594415770.402Q10693994654.402Q11939405141.389Q12945255385.385Q13002548137.401Q13676950804.384Q13963846262.395Q15752730517.399Q16027744916.401Q17008039385.401Q17425018425.401Q17454195172.380Q18089490443.401Q18102023734.401Q18798454873.401Q18872097273.401Q20459834793.401Q20464211549.391Q21472160986.386Q2154666025.401 Q2159599449.401 Q22190969305.401Q23928089235.393Q2410696150.390 Q24316579417.401Q2605123161.401 Q26074198841.401Q26502553036.375Q26920001688.388Q26987112345.379Q27665131153.399Q27875065177.401Q28234306710.400Q28776606169.401Q29123745940.401Q29499247193.401Q29648483289.401Q29732373684.401Q30439524718.396Q30995755538.382Q3181278517.402 Q32756490293.402Q33055635801.401Q34416871179.401Q34420984118.401Q34667111065.401Q35010575583.393Q36084925017.401Q36579641128.380Q36940995257.401Q3799283926.403 Q38511566558.392Q39043165210.390Q39850762830.406Q39850762830.407Q39857052210.376Q39976042025.401Q40513117017.401Q40599399476.401Q40987994480.402Q42035624155.387Q42441548847.406Q42441548847.407Q42580734868.398Q4278042260.401 Q43024701277.381Q43580975259.402Q44155788684.375Q44172294453.402Q44298944140.376Q44298944140.402Q44301027056.406Q44301027056.407Q44359965847.387Q44364894805.379Q45526347419.402Q45742289428.401Q45822091830.401Q45834628107.401Q46408772363.401Q46421304630.401Q48119910507.406Q48119910507.407Q49164414041.401Q49247644710.406Q49247644710.407Q49283981588.401Q49748522582.406Q49748522582.407Q49768135673.401Q497883065.401  Q5011256373.402 Q50842763689.401Q51107054235.402Q51283953300.401Q51449427892.401Q51568379999.383Q51691149979.402Q51789435193.401Q51961662993.396Q52332670358.386Q52464623069.394Q52569381385.402Q53213300371.383Q55660191.397   Q5596578838.406 Q5596578838.407 Q56592237972.401Q56970272057.401Q57223845531.402Q57225610745.401Q57620708409.406Q57620708409.407Q57893485213.401Q58040652597.402Q58668296436.401Q58742053010.400Q59617553652.401Q59621696201.401Q59698924043.401Q59703034934.401Q59769434898.392Q60012279769.401Q60133690901.385Q60138834193.381Q60482870325.402Q61097091038.382Q6191098356.406 Q6191098356.407 Q62586361044.388Q62639683769.401Q63435846322.402Q63558047033.401Q63588016984.384Q64228675114.405Q64228675114.406Q64427786041.401Q65213305287.394Q65509695633.391Q65654860420.401Q65674501161.401Q6575031993.401 Q6667361590.401 Q6671471371.401 Q66901779611.402Q67041068973.406Q67041068973.407Q67041083245.395Q67477298324.401Q67837027513.401Q6909946600.403 Q7093291664.398 Q7785411076.401 Q7821780905.401 Q8701202793.406 Q8701202793.407 Q8740343849.401 Q9458709140.401 Q9600193945.389 Q9611917865.401 Q9890590619.397 Q9967504441.401 00000101A02Q02R03L03P03Q03U04m05105205:05;05?05D05H05I05J07J07c0910:?0;A0<C0=n0?^0@R0AF0B>0C60CY0DQ0E`0FT0G70GZ0H=0I50I60I70IZ0J=0J`0KX0LP0M30MV0N90O10Oi0PL0Po0QR0R50Rm0Se0TY0U<0V00VS0W60WY0X<0X_0Z50Zm0Zn0[V0\90\\0\]0]Q0^I0^l0_d0`G0a;0b30bk0ce0d_0eG0ej0fM0g00gW0hO0iR0jU0kI0kl0ld0mL0mo0n00nX0o@10:11411l12d13L13o14014S15615Y17918Y19<19=19>19a1;21<C1<f1=I1>11>T1?<1?_1@B1A:1Ab1BE1CL1DD1E<1Ec1F[1GO1GP1GQ1H41HW1I?1Ib1Jf1Kj1L^1L_1MB1N61N71N81N[1N\1OT1P71Po1Qg1RO1SG1TE1UC1V;1V^1V_1WB1X:1YS1Zl1[O1\G1]?1]b1^E1^h1^i1_L1`41aX1c<1dZ1e=1e`1fT1gH1gk1hN1ig1k@1kc1lF1m>1ma1nU1o8SS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB2Lc2KbS2FBFS2FBS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2loSS3CRT2KbSS2FBS3CRTS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaS2sp3CRT2lo2bs2FB3sp13SP1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEst4FBLOS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB4SLOu4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKc2 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH LOS DCD SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma exit2_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k56 k64 k72 k80 k88 k104 k120 : word) (r : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k112 k48 s6v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7v s9v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    BUDX hc Lc -> rawlen < 2^40 -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) -> -2^31 < r <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 r) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa98b0) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. (intros INV CH OW PERM dd_H; ddestruct dd_H as (BV & BF & BC); intros RAWS C24 RR).
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 12 zstep.
    idtac "T-EXIT-1".
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr; [zstep; zstep; zstep; if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; first [lia | congruence | (apply Kb; reflexivity)]]; clear Kb| zstep]; clear Kr.
    all: idtac "T-EXIT2-2".
    all: (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      match goal with H : rw_cells _ mx (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end;
      lazymatch goal with MIx : mem_inv asegs mx |- _ => pose proof (owns_mu hc Lc _ mx _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM (proj1 HH0) HCSc MU WM MIx) as OW2 end;
      si_mu;
      ch_close mx;
      eapply c_fin with (STKc := STKc) (h := h) (blen := blen) (lo := lo) (slo := slo) (d := d) (mo0 := mo0) (PHIc := PHIc) (FFRc := FFRc) (CNTc := CNTc)
                      (hq := hc) (Lc := Lc) (FB := FB) (sp1 := sp1) (PK := PK) (SI := SI);
      first [ exact PERM | exact RAWS | exact C24 | exact RR | exact BV | exact BF | exact BC | exact HMND | exact CWX
            | eassumption | reflexivity | match goal with |- ?g => idtac "EXIT2-LEFT:" g end ] end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14406737544.313L16958996712.2  L27386516966.1  L32454903270.1  L35655538583.72 L37196404897.0  L38235734261.1  L42658947381.3  L51508673957.0  L51907744824.2  L59308634630.3  L60754583113.0  L62371643437.3  L65218937258.2  L67301973408.3  L6899380056.1   L6906665613.1   L7382465640.1   L9080482849.71  00000100800<00@01X01Y01]01d01e01l02302402;02<02H02L02Q02U02nFS2rg2RGS2FBS2FBS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcSS2loS2rg2RGSS2rg2RGS2rg2KcSS2rg2RGSS2LB4blen2DPS2FBS3CRTS2FBS2sp3CRT2lo2bs2FB3sp13SP1". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma ea0_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k56 k64 k72 k80 k88 k104 k120 : word) (rg : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k112 k48 s6v x10 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s7v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> -0x3000 < rg <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) (Z_to_bv 64 rg) s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9898) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB BE RAWS RG.
    assert (KONT : forall (hq : HST asegs R HIA) (mq : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       cinv [] mq hq FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
       crt_zero asegs mq CRT -> BUDX hq [] ->
       aevtA asegs (KF asegs R HIA hq mo0) POST
         (MS (mkR (Z_to_bv 64 0xa98a0) (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) (Z_to_bv 64 rg) s10v s11v y28 y29 y30 y31)
             F (Z_to_bv 64 0xa98a0) fc None mq (seg_rom asegs))).
    { clear INV CH OW PERM. intros hq mq y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INVq CZq BXq.
      pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
      (* [comment removed for export] *)
      do 3 zstep.
     rewrite (swrap32_land_errsum rg 18446744073709543040) by (clear - RG; lia).
     zstep. if_cases Kc; zify_cond Kc;
       [ exfalso; clear - Kc RG; rewrite ?signed_lit64 in Kc by lia; first [ lia | (Z.div_mod_to_equations; lia) | (match type of Kc with ?T => idtac "EA0-CHK-LEFT:" T end; fail) ] | ].
     clear Kc.
      zero_exit exit2_walk INVq CZq BXq; first [ (clear - RG; lia) | match goal with |- ?g => idtac "EA0-EXIT-LEFT:" g end ]. }
    clear RG.
    pose proof INV as INV0. open_cinv INV hc.
    (* [comment removed for export] *)
   do 2 zstep.
    eapply free_call with (RA := 0xa98a0) (Lc := Lc); first [ exact INV0 | exact CH | exact OW | exact PERM | exact HOB | exact BE | exact RAWS | exact KONT | reflexivity | (clear; lia) | match goal with |- ?g => idtac "EA0-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L1358641953.0   L22930433984.2  L27386516966.1  L32454903270.1  L35655538583.72 L38235734261.1  L51508673957.0  L60754583113.0  L67301973408.3  L6899380056.1   L6906665613.1   L7382465640.1   L9080482849.71  Q26483582778.355Q60713831066.35500000100800<00@01X01\01]01^01j01n02302702P03M04YSS2rg2RGS2FBS2FBS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2loSSS2LB4blen2DPS2FBS3CRTS2FBS2sp3CRT2lo2bs2FB3sp13SP1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB35HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB3". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB"] Lemma f2f4_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k56 k64 k72 k80 k88 k104 k120 : word) (rg : Z)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k112 s6v x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s5v s7v s9v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 (Z_to_bv 64 CRT) k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    BUDE hc Lc -> rawlen < 2^40 -> -0x3000 < rg <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rg) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) s5v s6v s7v (Z_to_bv 64 FB) s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9d4c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB BE RAWS RG.
    assert (KONT : forall (hq : HST asegs R HIA) (mq : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       cinv [] mq hq FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 (Z_to_bv 64 CRT) k56 k64 k72 k80 k88 (Z_to_bv 64 CRT) k104 k112 k120 ->
       crt_zero asegs mq CRT -> BUDX hq [] ->
       aevtA asegs (KF asegs R HIA hq mo0) POST
         (MS (mkR (Z_to_bv 64 0xa9d5c) (Z_to_bv 64 sp1) gp tp y5 y6 y7 sp (Z_to_bv 64 sp1) y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) s6v s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 rg) s11v y28 y29 y30 y31)
             F (Z_to_bv 64 0xa9d5c) fc None mq (seg_rom asegs))).
    { clear INV CH OW PERM. intros hq mq y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INVq CZq BXq.
      pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
      (* [comment removed for export] *)
      zstep.
      zero_exit exit2_walk INVq CZq BXq; first [ (clear - RG; lia) | match goal with |- ?g => idtac "F2F4-EXIT-LEFT:" g end ]. }
    clear RG.
    pose proof INV as INV0. open_cinv INV hc.
    (* [comment removed for export] *)
   do 4 zstep.
    eapply free_call with (RA := 0xa9d5c) (Lc := Lc); first [ exact INV0 | exact CH | exact OW | exact PERM | exact HOB | exact BE | exact RAWS | exact KONT | reflexivity | (clear; lia) | match goal with |- ?g => idtac "F2F4-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03M0@L14736116594.11 L15595230333.4  L15663367277.4  L16739881842.1  L1685717371.0   L17014059071.8  L19007505646.1  L19613119379.2  L23844837737.1  L23886653674.404L23886653674.405L2397676628.0   L24023900370.0  L24522544651.4  L26761725871.3  L27386516966.1  L28484160677.15 L29004524015.10 L31033929043.4  L32429087767.4  L32454903270.1  L33593681326.1  L35655538583.72 L37028251040.3  L37784689561.1  L38235734261.1  L39143458733.4  L39462426482.2  L42411609006.0  L42437611050.2  L42950214838.1  L44798256124.2  L4893033428.4   L52789871639.2  L5307035316.7   L54189535695.4  L56541488260.1  L57515392432.4  L59243279969.1  L59881546906.0  L60754583113.0  L61435167900.1  L61624266266.1  L62994014310.3  L6591994253.10  L66090992137.3  L66708381941.2  L6899380056.1   L6906665613.1   L7040221599.1   L7382465640.1   L8171953640.404 L8171953640.405 L8793638983.75  L9080482849.71  P324046647.408  P324046647.409  P33641443928.408P33641443928.409P7903954312.408 P7903954312.409 Q10594415770.404Q10693994654.404Q11939405141.391Q12945255385.387Q13002548137.403Q13676950804.386Q13963846262.397Q15752730517.401Q16027744916.403Q17008039385.403Q17425018425.403Q17454195172.382Q18089490443.403Q18102023734.403Q18798454873.403Q18872097273.403Q20459834793.403Q20464211549.393Q21472160986.388Q2154666025.403 Q2159599449.403 Q22190969305.403Q23928089235.395Q2410696150.392 Q24316579417.403Q2605123161.403 Q26074198841.403Q26502553036.377Q26920001688.390Q26987112345.381Q27665131153.401Q27875065177.403Q28234306710.402Q28776606169.403Q29123745940.403Q29499247193.403Q29648483289.403Q29732373684.403Q30439524718.398Q30995755538.384Q3181278517.404 Q32756490293.404Q33055635801.403Q34416871179.403Q34420984118.403Q34667111065.403Q35010575583.395Q36084925017.403Q36579641128.382Q36940995257.403Q3799283926.405 Q38511566558.394Q39043165210.392Q39850762830.408Q39850762830.409Q39857052210.378Q39976042025.403Q40513117017.403Q40599399476.403Q42035624155.389Q42441548847.408Q42441548847.409Q42580734868.400Q4278042260.403 Q43024701277.383Q43580975259.404Q44155788684.377Q44172294453.404Q44298944140.378Q44298944140.404Q44301027056.408Q44301027056.409Q44359965847.389Q44364894805.381Q45526347419.404Q45742289428.403Q45822091830.403Q45834628107.403Q46408772363.403Q46421304630.403Q48119910507.408Q48119910507.409Q49164414041.403Q49247644710.408Q49247644710.409Q49283981588.403Q49748522582.408Q49748522582.409Q49768135673.403Q497883065.403  Q5011256373.404 Q50842763689.403Q51107054235.404Q51283953300.403Q51449427892.403Q51568379999.385Q51691149979.404Q51789435193.403Q51961662993.398Q52332670358.388Q52464623069.396Q53213300371.385Q55660191.399   Q5596578838.408 Q5596578838.409 Q56592237972.403Q56970272057.403Q57223845531.404Q57225610745.403Q57620708409.408Q57620708409.409Q57893485213.403Q58040652597.404Q58668296436.403Q58742053010.402Q59617553652.403Q59621696201.403Q59698924043.403Q59703034934.403Q59769434898.394Q60012279769.403Q60133690901.387Q60138834193.383Q60482870325.404Q61097091038.384Q6191098356.408 Q6191098356.409 Q62586361044.390Q62639683769.403Q63435846322.404Q63558047033.403Q63588016984.386Q64228675114.407Q64228675114.408Q64427786041.403Q65213305287.396Q65509695633.393Q65654860420.403Q65674501161.403Q6575031993.403 Q6667361590.403 Q6671471371.403 Q66901779611.404Q67041068973.408Q67041068973.409Q67041083245.397Q67477298324.403Q67837027513.403Q6909946600.405 Q7093291664.400 Q7785411076.403 Q7821780905.403 Q8701202793.408 Q8701202793.409 Q8740343849.403 Q9458709140.403 Q9600193945.391 Q9611917865.403 Q9890590619.399 Q9967504441.403 00000100200300400500600700800901I02Y02Z02[02\02]02a02b02c02d02e02i02j04B04C04D04H04I04J04K04L04M04N04O04P04Q04R04S04T04U04V04W04X04Y04Z04[04\04]04a04f04g04k04l04m06m07F08T09b0:d0;f0=Q0?A0@50@i0Aa0BY0C<0D40EC0F70FZ0G=0G`0HX0HY0HZ0I=0I`0JC0K;0L30LV0M90M\0NT0OL0Oo0PR0Q50QX0RP0SH0T<0T_0US0V60VY0W<0W_0XB0YX0ZP0ZQ0[90[\0\?0\@0]40]l0^O0_G0_j0`^0aV0bN0cH0dB0dj0eM0f00fS0gK0hN0iQ0jE0jh0k`0lH0lk0ll0mT0n<0o610010h11`12H12k12l13O14214U16517U18818918:18]19n1;?1;b1<E1<m1=P1>81>[1?>1@61@^1AA1BH1C@1D81E01Ed1Ee1Ef1FI1Fl1GT1H71I;1J?1K31K41KW1LK1LL1LM1M01M11Mi1NL1OD1P<1Pd1Q\1RZ1SX1TP1U31U41UW1VO1Wh1YA1Yd1Z\1[T1\71\Z1]=1]>1]a1^I1_m1aQ1bo1cR1d51di1e]1f@1fc1h<1iU1j81j[1kS1l61lj1mMFFFFSFFFFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSSFFS2FBFFFFS2FBFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFS2loFFSFFFFFFFFFFFSFFFFFFS2FBS3CRTFS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaS2sp3CRT2lo2bs2FB3sp13SP1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEst4FBLOS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB4SLOu4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB32Lc5HTOPc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB32Lc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcFS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HBS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB32Lc5HTOPc2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32LcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB32Lc". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKc2 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH LOS DCD SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3"] Lemma exit3_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (s6v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s4v s5v s7v s9v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    BUDX hc Lc -> rawlen < 2^40 -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s4v s5v s6v s7v (Z_to_bv 64 FB) s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9ee4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. (intros INV CH OW PERM dd_H; ddestruct dd_H as (BV & BF & BC); intros RAWS C24).
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 14 zstep.
    idtac "T-EXIT-2".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    lazymatch goal with MIx : mem_inv asegs me |- _ => pose proof (owns_mu hc Lc _ me _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM (proj1 HH0) HCSc MU WM MIx) as OW2 end.
    si_mu.
    ch_close me.
    eapply c_fin with (STKc := STKc) (h := h) (blen := blen) (lo := lo) (slo := slo) (d := d) (mo0 := mo0) (PHIc := PHIc) (FFRc := FFRc) (CNTc := CNTc)
                      (hq := hc) (Lc := Lc) (FB := FB) (sp1 := sp1) (PK := PK) (SI := SI) (r := 0);
      first [ exact CH | exact OW2 | exact PERM | exact RAWS | exact C24 | (clear; lia) | exact BV | exact BF | exact BC | exact HMND | exact CWX
            | eassumption | reflexivity | match goal with |- ?g => idtac "EXIT3-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.
  End Call.
End Walk.
