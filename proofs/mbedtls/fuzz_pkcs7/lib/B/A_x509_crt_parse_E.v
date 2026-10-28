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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0xa9ca4%Z]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
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
  Ltac ja_join :=
    lazymatch goal with H : rw_cells asegs ?mx sp1 (CB 16 ?x :: C8 ?w :: ?rest) |- _ =>
      let WF := fresh "WF" in let L8 := fresh "L8" in
      pose proof H as WF; destruct WF as [[WF _] _];
      pose proof (cbytes_length (C8 w) I) as L8; cbn [cbytes csize] in L8;
      apply (rw_cells_reshape asegs mx sp1 _ (CB 24 (x ++ le8 w) :: rest)) in H;
      [ clear WF L8
      | cbn [cells_wf cell_wf] in WF |- *; destruct WF as (WF1 & _ & WF3); split; [rewrite length_app, WF1, L8; reflexivity | exact WF3]
      | cbn [cells_bytes cbytes]; rewrite <- ?app_assoc; reflexivity ]
    end.
  Ltac ja_split :=
    lazymatch goal with H : rw_cells asegs ?mx sp1 (CB 24 (?x ++ le8 ?w) :: ?rest) |- _ =>
      let WF := fresh "WF" in let L8 := fresh "L8" in
      pose proof H as WF; destruct WF as [[WF _] _];
      pose proof (cbytes_length (C8 w) I) as L8; cbn [cbytes csize] in L8;
      apply (rw_cells_reshape asegs mx sp1 _ (CB 16 x :: C8 w :: rest)) in H;
      [ clear WF L8
      | cbn [cells_wf cell_wf] in WF |- *; destruct WF as (WF1 & WF3); rewrite length_app, L8 in WF1; split; [lia | split; [exact I | exact WF3]]
      | cbn [cells_bytes cbytes]; rewrite <- ?app_assoc; reflexivity ]
    end.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L45217030384.199L45217031031.198L52460146199.20500001e03Z06YS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a1w2Ha2Hw3HawS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a1w2Ha2Hw3HawS1R3HIA5PHIcf5FFRcf4PHIj4FFRj1h2LF2sp3CRT4blen3BUF2bs4LFB23LFB2B24CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2kv2kf1a1w4PHIq4FFRq2V12V22HV2HF1H2H02H12H22H32H42BV2BF2H52H6". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 CNTk PHIcf FFRcf STKc2 CNTj0 PHIj_mono FFRj_mono PHIj_sadd FFRj_sadd CNTk0 PHIcf0 FFRcf0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS BUDV BUDF FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD_pre : forall (hc : HST asegs R HIA) Lc kv kf kc a w (PHIq : Z -> Z) (FFRq : Z -> Z -> Z),
    BUD hc Lc kv kf kc a -> 0 <= a -> 0 <= w -> a + w <= blen -> kv <= KVc blen -> kf <= KFc blen d ->
    (forall x, 0 <= x -> PHIq x <= PHIj x) -> (forall x e, 0 <= x -> FFRq x (e + 1) <= FFRj x e) ->
    havol asegs R HIA hc + PHIq w <= AVOL_MAX /\ hfr asegs R HIA hc + FFRq w (d + 1) <= FR_MAX.
  Proof.
    (intros hc Lc kv kf kc a w PHIq FFRq dd_H; ddestruct dd_H as (V1 & V2 & _); intros Ha Hw Haw HV HF LP LF0).
    pose proof (LP w Hw). pose proof (LF0 w d Hw).
    pose proof (PHIj_sadd a w Ha Hw). pose proof (FFRj_sadd a w d Ha Hw).
    pose proof (PHIj_mono (a + w) blen ltac:(lia)). pose proof (FFRj_mono (a + w) blen d ltac:(lia)).
    pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc in BV, BF.
    pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L56925402997.20500003;S1R3HIA4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2h'2Lc2Lq2kv2kf2kc1a1w4PHIq4FFRq4CNTq2V12V22V32HV2HF2HN1H2H02H12H22H32H4". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_sadd FFRj_sadd CNTj_sadd LB LF sp CRT Q blen BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD_post : forall (hc h' : HST asegs R HIA) Lc (Lq : list blk) kv kf kc a w (PHIq : Z -> Z) (FFRq : Z -> Z -> Z) (CNTq : Z -> Z),
    BUD hc Lc kv kf kc a -> 0 <= a -> 0 <= w ->
    (forall x, 0 <= x -> PHIq x <= PHIj x) -> (forall x e, 0 <= x -> FFRq x (e + 1) <= FFRj x e) -> (forall x, 0 <= x -> CNTq x <= CNTj x) ->
    havol asegs R HIA h' <= havol asegs R HIA hc + PHIq w -> hfr asegs R HIA h' <= hfr asegs R HIA hc + FFRq w (d + 1) ->
    Z.of_nat (length Lq) <= CNTq w ->
    BUD h' (Lq ++ Lc) kv kf kc (a + w).
  Proof.
    (intros hc h' Lc Lq kv kf kc a w PHIq FFRq CNTq dd_H; ddestruct dd_H as (V1 & V2 & V3); intros Ha Hw LP LF0 LC HV HF HN). unfold BUD.
    pose proof (LP w Hw). pose proof (LF0 w d Hw). pose proof (LC w Hw).
    pose proof (PHIj_sadd a w Ha Hw). pose proof (FFRj_sadd a w d Ha Hw). pose proof (CNTj_sadd a w Ha Hw).
    rewrite length_app. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L53680648178.17800000nS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
    #[using="LF sp CRT blen bs LFB2 LFB B2 FB sp1 LFB3 LFB512 LFB511 LFB7"] Lemma SNAME_small : forall l b, In b (SNAME l) -> snd b < 5889.
  Proof. intros l b Hb. unfold SNAME in Hb. apply in_map_iff in Hb. ddestruct Hb as (x & <- & _). cbn [snd]. unfold NAME_SIZE. lia. Qed.
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
    intros. first [ eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.free_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.free_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma ea0_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    intros. first [ eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.ea0_walk ]; eassumption.
  Qed.

  (* [comment removed for export] *)

  Hypothesis S_UID1 : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 (CRT + 128)) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned ext_own_zero sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned ext_own_zero sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUDK hc Lc a -> 0 <= a <= p - rawp -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (CRT + 152) 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (CRT + 352)) (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr (CRT + 352) 3 + al_sb AL)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9cdc) fc None mm (seg_rom asegs)).

  Local Notation BUD2 hc Lc a := (BUD hc Lc ((2 * blen + AVOL_CALL) + X509_SIG_ALG_PHI) (Z.max 0 (fr_charge (d + 1)) + Z.max 0 (X509_SIG_ALG_FFR 0)) 2 a).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L27206181164.185L27212478941.186L5436598838.188 L5436599221.187 L5919078973.194 00001502:03?04D071S2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71a2HaS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71a2HaS1R3HIA4PHIk4FFRk5PHIcf5FFRcf4PHIj4FFRj1h2LF2sp3CRT4blen3BUF2bs4LFB23LFB2B24CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc1a1w2V12V21H2H02H12H22BV2BF2H32H4". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 CNTk PHIcf FFRcf STKc2 CNTj0 PHIj_mono FFRj_mono CNTk0 PHIk_mono FFRk_mono PHIcf0 FFRcf0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS BUDV BUDF FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD_pk_pre : forall (hc : HST asegs R HIA) Lc a w, BUD2 hc Lc a -> 0 <= a <= blen -> 0 <= w <= blen ->
    havol asegs R HIA hc + PHIk w <= AVOL_MAX /\ hfr asegs R HIA hc + FFRk w (d + 1) <= FR_MAX.
  Proof.
    (intros hc Lc a w dd_H; ddestruct dd_H as (V1 & V2 & _); intros Ha Hw).
    pose proof (PHIk_mono w blen ltac:(lia)). pose proof (FFRk_mono w blen (d + 1) ltac:(lia)).
    pose proof (PHIj_mono a blen ltac:(lia)). pose proof (FFRj_mono a blen d ltac:(lia)).
    pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc, KVc, KFc in BV, BF.
    pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L27206187739.190L27212478941.191L56925402481.19200001>02L05HS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lc5owned1w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lc5owned1w2HwS1R3HIA4PHIk4FFRk4CNTk4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2h'2Lc5owned1a1w2V12V22V32Hw2HV2HF2HN1H2H0". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIk_mono FFRk_mono LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD_pk_post : forall (hc h' : HST asegs R HIA) Lc (owned : list blk) a w, BUD2 hc Lc a -> 0 <= w <= blen ->
    havol asegs R HIA h' <= havol asegs R HIA hc + PHIk w -> hfr asegs R HIA h' <= hfr asegs R HIA hc + FFRk w (d + 1) ->
    Z.of_nat (length owned) <= CNTk -> BUDK h' (owned ++ Lc) a.
  Proof.
    (intros hc h' Lc owned a w dd_H; ddestruct dd_H as (V1 & V2 & V3); intros Hw HV HF HN). unfold BUD, KVc, KFc.
    pose proof (PHIk_mono w blen ltac:(lia)). pose proof (FFRk_mono w blen (d + 1) ltac:(lia)). rewrite length_app. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "06[0@D11881018327.388D13687468690.388D20225638161.428D32046015329.374D32046015329.432D40775185266.373D40775185266.374D40775185266.432D42945709401.388D52056325516.426D53340075670.428D60109196847.373D60109196847.374D60109196847.432D60633465569.373D6193241394.426 D63598732510.388D64348882538.428K15835051771.373K15835051771.374K15835051771.432K1607432955.373 K1607432955.374 K1607432955.432 K21870859916.373K21870859916.374K21870859916.432K22945712379.373K22945712379.374K22945712379.432K33980871419.373K33980871419.374K33980871419.432K41095599355.373K41095599355.374K41095599355.432K52147535611.373K52147535611.374K52147535611.432L10821660490.418L11183176311.1  L12408374717.1  L12848087436.1  L13687437493.1  L13723336115.89 L13841005130.362L14447004729.2  L1540615640.71  L15522417010.89 L15766891572.9  L15771191613.1  L15822417165.2  L1594761485.2   L1685717371.0   L17080415141.2  L17157913229.1  L17428696050.13 L17570011486.89 L17570732653.89 L18285482667.89 L18314582654.13 L18943432533.2  L19221663423.2  L19912320701.1  L19979998541.89 L20105749565.1  L204253020.2    L21564861869.89 L21652623661.379L21866712442.2  L22089326749.2  L22306249429.2  L22941438733.2  L23119474137.2  L23513807686.2  L23615739305.3  L23766154372.417L24373605877.6  L24661729165.1  L25160623805.2  L26056183125.2  L26486612313.2  L26831527741.1  L26875616345.2  L26950445815.3  L27386516966.1  L28203417741.1  L2853021605.2   L29345674871.1  L29808099285.2  L29997480714.362L30003756373.2  L30042772057.2  L30431990105.2  L31163742194.361L31165786800.417L31388357250.2  L31863041268.89 L31953367821.1  L32327136116.1  L32454903270.1  L32698878355.1  L33564650027.2  L33597048665.2  L33946383677.1  L33985112333.2  L34359762549.89 L3482806040.89  L35243110309.2  L35316180621.1  L35655538583.72 L36111251402.363L36111251402.418L36314819741.2  L36449969418.89 L36460502135.1  L37622627047.5  L37875066173.1  L38070592189.1  L38235734261.1  L38958417276.89 L39425639108.2  L39457313805.1  L40281191306.3  L40284782961.15 L40711908697.2  L41099742989.2  L41103222873.2  L41865302029.1  L42238884836.89 L4271516572.417 L43139882429.13 L43571151479.1  L44466151385.2  L44591292382.361L44603552853.2  L45622478594.2  L4572017369.2   L47375303325.2  L48832781706.363L50429758186.9  L5116735037.1   L51508673957.0  L51522874581.2  L51909129149.1  L51953172697.2  L52160193805.2  L52491779133.1  L53297931533.1  L53434615722.89 L53491360397.1  L53863670157.1  L5436592646.13  L54490163357.2  L55224207780.3  L55225352820.2  L5725268365.1   L57346988965.2  L57420059277.1  L57737295984.18 L57740949025.18 L57798807159.1  L58444170581.2  L58833256533.2  L58885089625.2  L59026817493.2  L59059691215.3  L5907370946.2   L59257267289.2  L59308586248.2  L59413075133.1  L6042617148.1   L60754583113.0  L60799649293.1  L60915193550.89 L61070726323.9  L61366595865.362L61366595865.418L61434809813.2  L61522160417.0  L6203936179.1   L62589838554.13 L63484531678.361L63598505721.1  L6487220337.3   L65042673680.417L65186724949.2  L65749720177.2  L65946019413.2  L66332265789.1  L66721351741.1  L66891044106.418L66914912701.1  L67701510089.89 L68093394317.1  L6899380056.1   L6906665613.1   L7382465640.1   L7733720611.2   L7736014575.2   L7874303133.2   L7899873621.2   L8113154630.89  L8401410506.362 L8742280115.2   L8793638983.75  L8896078297.2   L9080482849.71  L9241280651.89  L9887797032.3   L9967652261.2   P14461423358.373P14461423358.374P14461423358.432P14847417535.426P17093032469.426P18957997811.426P216805100.426  P22085167405.426P22304234355.426P23132087401.426P26033627457.426P26070748403.426P26482387177.426P26863064553.426P2865573397.426 P29455570367.426P29801758323.426P30010064115.426P30038612969.426P30296187722.426P30419441897.426P33009850559.426P33144260417.426P33378092479.426P33592889065.426P34509067982.426P35238946325.426P36310656301.426P39410877282.426P3984815423.426 P40707745001.426P41090671081.426P428425791.426  P44179287361.426P44470310505.426P44601570803.426P45626642098.426P4567858025.426 P46851936942.426P47362689837.426P47601488319.426P47809663039.426P51366036287.426P51537603955.426P51948947817.426P54465726785.426P54477545773.426P57359536661.426P58442024179.426P58653288383.426P58827047411.426P58872537321.426P59032993907.426P5919988338.426 P59269885417.426P61424340083.426P62211762879.426P62786065983.426P65188904435.426P65768250815.426P65939810291.426P7750690063.373 P7750690063.374 P7750690063.432 P7866737985.426 P7878532397.426 P7889436915.426 P8498176191.426 P8908695657.426 P9980265493.426 Q10037255372.369Q11301460963.370Q11301468454.428Q12931746569.370Q1356059127.428 Q1432898026.428 Q1433031824.415 Q15985628819.428Q16497458532.369Q17093032469.426Q18957997811.426Q19215322905.426Q19546964817.426Q19561351767.379Q20712903500.369Q216805100.426  Q22085167405.426Q22304234355.426Q22674097016.370Q23132087401.426Q24594482857.370Q25155171900.426Q25797951096.371Q25797951096.429Q25816004610.369Q25818038665.370Q26030354684.432Q26070748403.426Q26479516165.370Q26481632642.369Q26482387177.426Q2676383091.428 Q26863064553.426Q26955938422.426Q2865573397.426 Q29801758323.426Q30010064115.426Q30038612969.426Q30419441897.426Q30602569224.369Q30603046306.369Q30604720970.428Q30605153321.370Q32046015329.374Q32046015329.432Q32047999329.373Q32047999329.431Q33562180266.426Q33592889065.426Q34900465062.428Q34964698202.432Q35238946325.426Q35835101688.370Q36310656301.426Q37763896721.370Q3853027959.428 Q3853162253.415 Q39029115498.428Q39410877282.426Q39430530833.429Q40011998712.429Q40707745001.426Q40772909426.372Q40772909426.373Q40772909426.431Q40775185266.373Q40775185266.374Q40775185266.432Q40956552420.369Q41090671081.426Q42186161645.370Q42439443119.373Q42439443119.374Q42439443119.432Q44470310505.426Q44601570803.426Q45626642098.426Q4567858025.426 Q46173603403.370Q46173611150.428Q47362689837.426Q47533990414.428Q49698585326.371Q49698585326.372Q49698585326.430Q49746415830.373Q49746415830.374Q50233692894.379Q51537603955.426Q51948947817.426Q53579518537.426Q54477545773.426Q57359536661.426Q57618602681.373Q57618602681.374Q57618602681.432Q58442024179.426Q58746002845.379Q58746361881.369Q58748470619.428Q58811134737.370Q58827047411.426Q58872537321.426Q59032993907.426Q59069861454.426Q5907672925.369 Q5909336925.370 Q5919988338.426 Q59269885417.426Q59865321072.432Q60633465569.373Q60635711713.372Q60701390757.370Q60703459362.369Q61424340083.426Q6193241394.426 Q6480654576.426 Q65188904435.426Q65734233328.426Q65939810291.426Q67038978349.373Q67038978349.374Q68281354854.426Q68616026845.369Q68618012381.370Q6913481631.428 Q6913604317.429 Q7480038765.371 Q7480038765.429 Q7721379553.426 Q7878532397.426 Q7889436915.426 Q8444860049.371 Q8444860049.429 Q8699115497.373 Q8699115497.374 Q8699115497.432 Q8754827779.426 Q8908695657.426 Q891931935.428  Q891940826.370  Q892316765.371  Q892316765.429  Q9634063272.379 Q9644386990.426 Q9980265493.426 00001602<03R04a06A07T08c0:C0;I0<^0>40?P0@h0BQ0Cd0E50F;0GQ0Ha0Im0KJ0LZ0Mf0OC0PS0Q_0S<0TL0UX0W50XE0YQ0Zn0\>0]J0^g0`70aC0b`0d10d50d:0d?0dD0dg0ee0ef0f<0gJ0g]0gb0gc0gd0ge0gf0gk0h^0jE0jc0kC0k\0k]0k^0kc0m>0mC0mD0md0nj0nk0nl0nm0nn0no0o:0oD0oE0oW0o\0o]0o^0o_0od0oe0of0oj0oo10010410511311411511611713Q13W14e14j14n15215815915:15?15@15b17217317818P19N1:_1:`1;f1;j1<;1<@1<E1<I1=X1=Y1=^1=g1>^1>_1>`1>a1>f1@M1Ag1B61B:1B;1CB1CC1CD1CE1CF1DD1Dm1E21E31E41E91E:1E;1E@1EE1Fn1G31G81Gl1Gm1Gn1H61H;1H<1HA1HB1HC1HG1HH1HI1HJ1HK1HL1HM1HN1HT1HY1H^1H_1Hd1JS1K61L41ME1MF1MG1ML1Md1Nk1O01O11QG1QH1QI1QJ1QO1QT1Re1Rj1SI1SN1SR1SW1S[1S\1S]1S^1S_1U91V71V81X?1X@1XY1Y61Y>1Y?1[91\o1_?1a@1bL1c\1dj1f81gH1hV1jR1kb1m01n>1oJ21K22[23k25926P27^29_2;[2=\2>j2@f2B22C@2DP2FQ2G_2Hm2Jn2Lj2N82OH2PT2Qb2Sc2U12W22Y32[42\D2]R2_T2`b2an2c>2e?2fO2g]2hm2j;2kI2lY2nZ30[31k33l35<36n38\3:d3<`3=n3?>3A?3BM3CY3DP3EG3FQ3Ga3IX3Jl3L@3LA3M83M93M:3O33PN3Q^3RU3RV3RW3RX3Sk3Sl3UK3WG3XZ3ZI3[Y3\i3^L3^M3_]3`m3`n3b93b:3d>3d?3d@3dA3dB3dC3e63fU3g[3i:3jB3k[3lc3n<40=40>41H43R43S44f44g45^47U49L4:`4:a4;k4=Z4=[4>g4?o4AH4BT4C\4E54El4Em4Fl4HC4IV4K:4K;4K<4K=4K>4L54M?4M@4NJ4ON4PR4Qi4SN4To4Uj4Uk4Ul4W64W74W84XL4Y\4[=4[>4\94\l4^24^i4^j4^k4^l4`m4ad4b[4b\4b]4b^4cj4e64fU4h44h54i?4kA4kB4mF4mG4o?51352^53U54L55V56`57_5915:m5:n5:o5;f5=05>]5@F5BI5D=5D>5EH5F?5G65H@5I>5JG5JHS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned1x2HxS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned1x2HxS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2FBS3CRTS3CRTS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FS2sp3CRT2bs2FB3sp13SP1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS1R2lo3LOS3ALO4DLOqS3CRTFFSFS3CRTS4blen1p4END14END26rawlen4rawp3RBL3Hp13Hp24Hp2'3Hp3S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2sp3CRT2bs2FB3sp13APC7rawjunkS1R2sp3CRT2bs3DCD2FB3sp17rawjunkS1p4END11a4rawp2p42HA3Hp4FFS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkS3CRTFS1R2sp3CRT2bs2FB3sp13FDD7rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFFFS6rawlen2RSS1R3HIA2hcFS3CRT2FB1x1k2Y12Y2S3CRTFFFS3CRTFFS2FBS3CRTFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FFFFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END26rawlen4rawp7rawjunk2RP3Hp13Hp24Hp2'3Hp33RA42p45owned3Hp4S4blenS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS3CRTS2FBS2FBS4CNTkFFS3CRTFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBS2FB1x2NF3CRT3Hx1S3CRTS3CRTS2loS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS1R3HIA1hS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HA2p43Hp4FFFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB71p7rawjunk2p45ownedS1p4END12p43Hp4S2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7FFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S4C24k4C24c5C24c12LB4blen5BUD242Lc3C242DPS3CRTSFS3CRTFFS3CRTS3CRTS1R4STKc4STKk5STKck2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS3CRTS3CRTS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFFS2rc3Hr3S3CRTFS3CRTFFS2FBFFFFFFFS1i2HiS3CRTS3CRTSS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS2LB4blen2Lc1p3C242p45owned4HC242DMS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFSS3sp1S1p4END14rawp2p43Hp13Hp4S2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7S3CRTFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END26rawlen4rawp7rawjunk2RP3Hp14Hp2'3Hp33RA42p45owned3Hp4FFFS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS3CRTS2sp3CRT2bs4CRT02FB3sp17rawjunkS3CRTS2FBS3CRTS2FBFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen7rawjunk2RS4RLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02Da5SBND0FS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS4blen1dFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF3CRT4blen2bs4LFB23LFB2B23DCD2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R2LF4blen2bs4LFB23LFB2B22FB3FDD4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned1c2HcFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk4SBND2p45owned3Hp4FFFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp42HB5Ha_st5Hl_stFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72HBS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stFFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72HB5Ha_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72HB5Ha_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p3sr45HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p5HTOPc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedFFS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7FS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk4SBND2p45owned3Hp4FS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p3sr42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc1p4END17rawjunk3HSc5HTOPc2p45owned3Hp4S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72HBS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45owned2HBS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk4SBND2p45owned3Hp4FFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p3sr45HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45HTOPc5owned3Hp42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB71p4END17rawjunk2p45owned3Hp4FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB71p7rawjunk2p45ownedF". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKk C24k PKPARSE STKcf CRTFREE STKc1 STKc2 STKck STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono CNTk0 PHIk_mono FFRk_mono PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono C24c C24c1 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF BUD24 SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_UID1"] Lemma S_PK : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 (CRT + 128)) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes 0 0 [] ext_own_zero sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes 0 0 [] ext_own_zero sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUD2 hc Lc a -> 0 <= a <= p - rawp -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (CRT + 152) 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (CRT + 152)) (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 96))
               (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9c30) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 B2' HA C24.
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 21 zstep.
    idtac "PK-PRE".
    do 4 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    owns_now OWm hc Lc. si_mu.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => rename HHx into HHg end.
    destruct (raw_side hc Lc mg _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    frame_aobj FSH (FB + 96) 1%nat as OPP.
    pose proof (uwc_callee hc mg PRES HSc SAVE) as UWF.
    destruct (BUD_pk_pre hc Lc a (END1 - p) B2' ltac:(clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia) ltac:(clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia)) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHg) as NDLc.
    assert (C24P : cnt24 (Lc ++ LB) + C24k <= C24MAX).
    { pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP. clear - C24 BUD24 C24c1 DP. lia. }
    idtac "PK-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PKPARSE with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (PKA := CRT + 360) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc;
        first [ exact HHg | exact HK1 | exact UWF | exact BPV | exact BPF | exact NDLc | exact RBY | exact RIN | exact OPP | exact TPV | exact C24P
              | eassumption | reflexivity
              | lazymatch goal with
                | |- bv_unsigned _ mod 2 = 0 => rewrite unsigned_lit by (clear; lia); reflexivity
                | |- _ => cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
                end
              | match goal with |- ?g => idtac "PK-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & rc & p4 & info & ctx & owned
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HC24 & HPP4 & Hp4 & HPK4 & PKR4 & HRZ & ND4 & HH4 & SIP4).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xa9c94)) with (Z_to_bv 64 0xa9c94 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
    idtac "PK-BACK".
    pose proof (owns_pres hc Lc mg m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc HP4 MI4
                  ltac:(intros x k Y1 Y2 Y3 Y4; apply disjoint_from_app_intro; [cbn [disjoint_from]; clear - Y1 Y2; lia| apply (si_fp_disjoint_offimg L SI); [exact Y4| exact (proj1 DIMG)| exact (proj2 DIMG)]])) as OWt.
    pres_call HP4.
    pose proof (BUD_pk_post hc hq3 Lc owned a (END1 - p) B2' ltac:(clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia) HV3 HFR3 HCNT3) as BK3.
    lazymatch goal with K10x : rw_cells _ mg (CRT + 360) _, PCx : rw_cells _ mg (FB + 96) _, STx : stk _ mg lo sp1, SSx : sshad _ _ mg slo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ =>
      clear K10x PCx STx SSx MIx SIx end.
    clear OW OWm HHg RBY ORAW OPP.
    (* [comment removed for export] *)
    assert (HP4d : presA asegs R (Lc ++ LB) LF' sp1 sp1 (hstkhi asegs R HIA hc) [(FB + 96, FB + 96 + 8); (CRT + 360, CRT + 360 + 16); (hl_data_lo L, hl_data_hi L)] mg m4).
    { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. cbn [outside app] in Hx |- *. ddestruct Hx as (X1 & X2 & X3 & _). split; [exact X1|]. split; [exact X2|].
      destruct (outside_dec (si_fp SI) x) as [O|NO]; [exact O|]. exfalso. ddestruct (si_data SI x NO) as (Dx & _ & _). apply X3. exact Dx. }
    pose proof (art_data_lo asegs R HIA) as DLOq.
    assert (DLO2 : hl_data_hi L <= lo) by (clear - DLOq ALO LOS; lia).
    presA_transport HP4d.
    clear HP4 HP4d DLOq DLO2.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, PKR4, HC24.
    clear_client_facts. client_facts hq3.
    assert (PERM1 : Permutation (owned ++ Lc) (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes info ctx owned ext_own_zero sigopts))).
    { rewrite crt_blocks_f_of. rewrite crt_blocks_f_of in PERM. cbn [app] in PERM. apply Permutation_app_head. exact PERM. }
    assert (OW1 : owns asegs PK m4 ((owned ++ Lc) ++ LB) CRT ob rawlen rawp inext inodes snext snodes info ctx owned ext_own_zero sigopts rawjunk).
    { pose proof (owns_grow hq3 owned Lc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ OWt PERM HH4 MI4) as OWg.
      unfold owns, crt_own_ok in OWg |- *. ddestruct OWg as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _ & _).
      cbn [f_of co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen co_pkinfo co_pkctx co_pkowned cj_raw jraw] in C1, C2, C3, C4, C5, C6, C7, C8 |- *.
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj PKR4 _))))))))).
      exact (nodup_of_perm hq3 (owned ++ Lc) m4 _ HH4 PERM1). }
    assert (C241 : cnt24 ((owned ++ Lc) ++ LB) <= cnt24 LB + 2 * (blen / 5889)).
    { rewrite <- app_assoc. pose proof (Z.div_le_mono (p4 - p) blen 5889 ltac:(clear; lia) ltac:(clear - Hp4 HA Hp1 Hp2 Hp2' Hp3 RBL; lia)) as DM.
      rewrite <- app_assoc in HC24. clear - HC24 C24 DM. lia. }
    idtac "PK-SWITCHED".
    rename HPK4 into K10.
    mu_reset hq3.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    2:{ idtac "PK-ERR". refold_mu INV2 OW2 hq3 (owned ++ Lc) FSHB. to_free.
        eapply free_walk with (Lc := owned ++ Lc) (r := rc); first [ exact INV2 | exact CH | exact OW2 | exact PERM1 | exact HOB | (clear - RS; lia) | (clear - Hr3; lia)
              | (eapply BUD_E; [exact BK3| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia])
              | match goal with |- ?g => idtac "PK-ERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 13 zstep.
    idtac "PK-OK". refold_mu INV2 OW2 hq3 (owned ++ Lc) FSHB.
    eapply S_UID1 with (Lc := owned ++ Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a) (p := p4);
      first [ exact INV2 | exact CH | exact OW2 | exact PERM1 | exact HOB | exact C241 | exact BK3 | eassumption
            | (clear - Hp4 Hp1 Hp2 Hp2' Hp3 HA; lia) | match goal with |- ?g => idtac "PK-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L22573296152.183L31489692490.183L55718059222.18300001702<03ES4FFRk2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71HS4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71HS4CNTk5CNTk02LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  #[using="NS1 STKc STKc0 NA1 STKc2 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 LB LF sp CRT Q BUF lo slo bs LFB2 LFB BIN B1 B2 B3 CRT0 DXB SLOS SLOL SLO SPH LOS FB sp1 SP1 FRSH APC SPR ALO ACV F0 APB SP1R LFB3 LFB512 LFB511 LFB7"] Lemma BUD2_E : forall (hc : HST asegs R HIA) Lc a, BUD2 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    intros hc Lc a B Ha. eapply BUD_E; [exact B| | | | exact Ha]; unfold KVc, KFc.
    - pose proof (PHIk0 blen B2). lia.
    - pose proof (FFRk0 blen (d + 1) B2). lia.
    - pose proof CNTk0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0:g0@C18971418195.402C23922862675.401D11881018327.412D11891817072.402D16071854214.402D16901939902.402D40091843490.452D40775185266.379D42033692510.412D42035635047.402D42945709401.412D43665348967.402D44374481682.412D49804782053.452D51070157262.452D52045925387.450D56536395888.402D60109196847.379D60109446735.402D60633465569.379D6203698357.450 K10114639055.402K10499531215.402K10674151503.402K13096823887.402K1396569935.402 K15835051771.379K1607432955.379 K16827801039.402K17610693583.402K21302816458.402K216607946.402  K21870859916.379K22861045682.402K22945712379.379K23131760207.402K26482584271.402K26863261647.402K28281397455.402K30038940111.402K30419638991.402K3179121999.402 K33593216207.402K33980871419.379K3591543988.379 K39316523727.402K40707548879.402K41090868175.402K41095599355.379K42696720207.402K44470506575.402K4568054095.402 K46427712719.402K50191716943.402K50368437455.402K51948751695.402K52147535611.379K57689895247.402K58872734415.402K59270213583.402K63420573106.402K64991401423.402K8908368463.402 L10102288217.2  L10304149557.3  L10314617926.5  L10487310937.2  L10687032281.2  L10840411873.2  L10912730231.1  L11183176311.1  L12082103731.2  L12348516960.17 L12408374717.1  L12974448687.17 L13066357277.2  L13092792281.2  L13543595425.19 L1408793817.2   L14402536426.389L14406603629.402L14447004729.2  L14693717588.95 L14695810623.2  L14786404065.2  L15081622413.1  L15275182349.1  L1540615640.71  L1548849343.89  L15519992260.1  L15522251860.95 L15522417010.89 L15595036650.6  L15595230333.4  L15597554710.6  L15771191613.1  L15822417165.2  L1594761485.2   L15985565909.2  L15985734202.4  L15987925446.4  L16023460231.89 L16209192302.269L16533871807.9  L16727285506.3  L16729017598.3  L16739881842.1  L16840545881.2  L1685717371.0   L168650209.2    L16960937224.2  L17442812634.95 L17443059548.1  L17570370680.95 L17578921351.3  L17606135897.2  L17611635570.89 L17958128354.1  L17962568218.3  L18023395959.1  L18302214263.1  L19001214825.3  L19002889365.3  L19007505646.1  L19047483503.95 L19047534057.1  L19364945151.18 L19376904127.18 L1951409339.1   L1955882052.3   L19613118329.4  L19613119379.2  L19615279849.65 L19615279849.67 L19615644805.3  L19615644805.4  L19625934710.1  L19912320701.1  L19979638891.95 L19980537034.4  L20105749565.1  L20127766261.95 L20128105044.3  L204253020.2    L21298324828.2  L21564613915.71 L21644325741.3  L21650968832.404L21654730866.2  L21655104302.376L21866712442.2  L22095213153.2  L22429046806.10 L22573296152.407L22866772043.3  L22941438733.2  L23119474137.2  L23513807686.2  L23766154372.428L23840803090.3  L23842740974.3  L23844837737.1  L23969902218.366L2461029603.14  L25160623805.2  L25339678326.2  L25341254165.95 L25636326795.2  L25644195765.269L2621559066.1   L26486612313.2  L26831527741.1  L26875616345.2  L26983613546.4  L27024765250.269L27386516966.1  L27543733740.2  L2770202465.2   L27940391089.89 L28277369689.2  L28880652623.3  L29066840183.1  L29345674871.1  L29487990029.1  L29874978829.1  L30042772057.2  L30431990105.2  L3058445732.2   L31033929043.4  L31034474422.6  L31036468298.6  L31489692490.407L3182954201.2   L31862502771.1  L31862612434.95 L32327136116.1  L32427148412.6  L32428889984.6  L32429087767.4  L32454903270.1  L33314616971.89 L33593681326.1  L33594193739.3  L33595860151.3  L33597048665.2  L33618159096.4  L33620162052.4  L33620491667.2  L33817424237.3  L33946383677.1  L33985112333.2  L34360251219.95 L34362187459.2  L3482380862.95  L3482806040.89  L3483319967.1   L35159717405.2  L3532059019.2   L35655538583.72 L35762075958.3  L35898373021.71 L3598635821.3   L36266554869.6  L36307103329.2  L363258721.2    L36442108371.2  L36449675308.95 L36460502135.1  L36667852792.0  L3726076129.2   L37782345752.3  L37784689561.1  L37784800228.3  L37875066173.1  L38070592189.1  L38235734261.1  L38939190544.4  L39141819957.6  L39143458733.4  L39144281545.6  L39321010521.2  L39472728318.4  L39756741698.2  L39864004961.2  L40228640085.0  L40281191306.3  L40711908697.2  L40920634893.1  L41099742989.2  L41103222873.2  L41175045497.1  L41187612937.3  L41663468698.393L41976525601.0  L42033526137.1  L42272513053.2  L42435007182.4  L42437198130.4  L42437611050.2  L42656549219.281L42683970777.2  L42950214838.1  L42950366411.3  L42952558391.3  L43226826465.2  L43571151479.1  L43597331579.5  L43647381704.12 L43654031417.10 L43801148432.14 L43810982283.2  L44298263949.1  L44374642997.1  L44466151385.2  L44482103862.3  L44483844554.3  L44484137049.1  L44795654490.4  L44797387430.4  L44798256124.2  L45703525153.0  L4572017369.2   L45802789271.2  L46012794146.95 L46014895433.4  L46164098627.4  L46164274750.2  L46166617535.4  L46354690673.3  L4638061450.89  L46431676249.2  L46715336767.2  L4700111548.17  L47049041130.3  L47242118263.1  L47508711168.269L47856733837.1  L47870616696.2  L48068055434.89 L48348887131.2  L48351147467.95 L48487939594.89 L49158833989.3  L49161360569.3  L49171160638.1  L49387356701.2  L50187819481.2  L50381248345.2  L50925318027.2  L51040545879.3  L51046802212.1  L5116735037.1   L51508673957.0  L5169687181.1   L51906071000.2  L51953172697.2  L52160193805.2  L52200163714.18 L52491779133.1  L52789871639.2  L52790171251.4  L52792427919.4  L5307035316.7   L5307727056.9   L5309722412.9   L53130300941.2  L53527181501.2  L5436592646.13  L5447135756.1   L54676236769.2  L54745125893.8  L55224207780.3  L55225352820.2  L56381092531.5  L56383349071.5  L56383615279.3  L56592702936.2  L566003128.281  L57048819133.3  L57056197698.95 L57685342937.2  L57779397874.2  L57798807159.1  L58302423030.2  L58304457431.95 L58314874790.14 L5855595306.4   L5855861578.6   L5858379958.6   L58584224602.365L58885089625.2  L59241344522.3  L59257267289.2  L59308586248.2  L59323590059.2  L59413075133.1  L59482804493.1  L59773150990.5  L59775612146.5  L59775870098.3  L6008660450.10  L6042617148.1   L60448817524.1  L60754583113.0  L60915193550.89 L61366595738.394L61366595865.366L61401481953.2  L61565331540.269L61628038753.3  L62263105549.1  L62370310267.281L62652188429.1  L6315985144.5   L63422184011.3  L6397268263.11  L6400673884.9   L64418367100.89 L64526681523.2  L6487220337.3   L64979181145.2  L6522106337.2   L65221205066.2  L65404616823.1  L66208565261.1  L66298372189.2  L66332265789.1  L66706832401.4  L66708381941.2  L66709352429.4  L66721351741.1  L66914912701.1  L66925224585.377L67301973408.3  L67558194717.2  L68455261432.3  L68456051864.5  L68458047332.5  L6899380056.1   L6906665613.1   L7038636857.3   L7040221599.1   L7041155269.3   L7088503905.2   L7282981857.2   L7382465640.1   L7736014575.2   L8105295519.1   L8113055584.95  L8121202101.4   L8122869321.4   L8133802437.2   L8339083405.1   L8401410506.366 L851918733.1    L8734254858.17  L8734490490.15  L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9160792157.4   L9161345720.2   L9241280651.89  L9241447853.95  L9243705405.1   N26872553873.401N48204456022.401N55966132906.401N60733400192.401N63430872977.401N66590330291.401O1001933565.402 O10618990077.402O11746403965.402O11930563540.400O14542167037.402O15460105085.402O16350966909.402O17494624509.402O17750585469.402O18155437218.402O18626760061.402O19357757918.399O19770425853.402O19931227630.402O20935596669.402O22221714158.402O30245212782.402O3078286936.402 O32096263534.402O32537874520.402O33239929326.402O33990841394.402O34031148413.402O35592798351.402O366419438.402  O36680917870.402O37630280430.402O39838419581.402O40463046306.402O41843596285.402O42197094638.402O43277289469.402O44195227517.402O4440802429.402 O44425156733.402O44938202843.400O45122245047.402O45423855982.402O45969540168.402O48862730990.402O50473853.402   O50817538813.402O52020260349.402O5312795005.402 O54023336829.402O54381021294.402O55209884805.400O55518239188.400O5585524989.402 O56848487390.399O57201466440.402O57537483645.402O59278274632.402O60687394173.402O60978474237.402O61464066679.402O62206064366.402O63123445358.402O63904362034.402O64128366333.402O64204162429.402O64474006218.402O65961212488.400O66562860014.402O67171060367.402O7590719101.402 P10851408966.402P13068530218.450P1406747886.450 P14461423358.379P14793198662.402P14832643384.450P182826822.402  P202219371.450  P21647862485.400P21658526154.400P22080053446.402P22141042872.450P23121499630.450P25154843674.402P25650503468.402P26027233478.450P26484447598.450P26873455726.450P2784312774.402 P29449380920.450P30040746606.450P30285664973.450P30429833582.450P3064266499.402 P32877070928.450P33007855928.450P33142142662.450P33380168760.450P33599225710.450P33810555850.400P34494424905.450P35157675562.450P3530433324.402 P357446086.402  P36322327750.402P3741301318.402 P39754564725.450P3982673080.450 P39879222214.402P41101054062.450P42270352426.450P426308536.450  P43225306182.402P43817786156.402P44185672902.450P44463990766.450P4574038766.450 P46340546774.399P46849745705.450P47047506707.402P47803277752.450P47876372191.400P49385208362.450P50927926572.400P51359658680.450P51951155438.450P53529750042.402P54467803334.450P54662134598.402P58668062264.450P58887115118.450P59259427950.450P61391540294.402P62226537272.450P62792329144.450P64538971685.402P6480458454.399 P6515303238.402 P65782836280.450P66292560634.402P67560343082.450P7086878406.402 P7297149254.402 P7606020176.450 P7750690063.379 P7852086470.450 P8495976760.450 P8754630693.402 P8893913582.450 Q12931747077.376Q13068530218.450Q1406747886.450 Q1432898026.438 Q1437489771.412 Q15985628819.452Q16071854214.402Q16472810971.402Q19546884730.404Q19559411796.376Q19561563123.377Q19561624278.450Q202219371.450  Q20712740552.375Q21294101882.377Q21767670690.402Q21832736479.402Q21930397408.402Q23121499630.450Q24594481317.376Q25161418683.450Q25473514713.402Q25816366470.375Q25818046792.403Q26479524806.399Q26479525064.403Q26484447598.450Q2676383091.452 Q26873455726.450Q2803826605.402 Q28880382025.450Q29775981542.402Q30040746606.450Q30429833582.450Q30602208140.375Q30602946598.375Q30604721986.403Q30605161704.403Q32437204119.402Q33599225710.450Q34669522109.402Q34671242809.377Q34671291067.402Q35157675562.450Q35835101688.376Q36630862464.402Q36633013669.376Q3849230838.412 Q3853027959.438 Q38831234053.376Q38833253152.402Q39439682456.402Q39754564725.450Q40550330331.402Q40772909426.378Q40775185266.379Q40956715360.375Q41101054062.450Q41414298335.402Q42186161645.376Q42270352426.450Q42439168719.402Q42439443119.379Q42982396641.412Q44463990766.450Q4574038766.450 Q46715308062.450Q47957748593.402Q48118064779.402Q49385208362.450Q49698585326.377Q49746198710.402Q49746415830.379Q50231978205.376Q50244489971.404Q51722040728.402Q51951155438.450Q52136395990.402Q53577458638.450Q54624410993.402Q55705402538.402Q57618602681.379Q57828105177.402Q58743871165.402Q58744348080.404Q58746002845.375Q58748469587.403Q58748479390.376Q58811134737.376Q58887115118.450Q59259427950.450Q59323860141.450Q60633465569.379Q60635711713.378Q60701380968.403Q60701382246.399Q6203698357.450 Q6486966647.450 Q67038703949.402Q67038978349.379Q67153740698.412Q67560343082.450Q68266720225.450Q68615929689.375Q68618012381.376Q8362820247.402 Q8699115497.379 Q8699324297.402 Q8744444804.450 Q8893913582.450 Q9008343465.376 Q9356559674.379 Q9631848875.376 Q9633798953.450 Q9634015756.377 Q9644499845.404 Q9644583048.402 00000400801A02G04C06107F08]09f0:l0<50=;0>D0?Y0@n0BA0CG0Dg0F60GM0H\0I_0Jb0Ke0Lh0Mk0O?0PS0QV0RY0S\0T_0V30Wk0Y?0ZB0[E0\H0]K0^N0_Q0`T0aW0bk0dR0eU0fX0g[0ho0j20k50l80m;0n>0oA10D11X12[13^14a16Y17\18_18`18a18b18c18d18e18f18j19119A19F19b19c19d1:g1:h1:i1:j1:k1;O1;P1;Q1;V1;[1<11=N1=O1>]1?k1?l1?m1?n1@31@41@51@61@71@81@R1Af1Ag1Ah1Ai1Aj1Ak1Al1Am1B51CD1CE1EX1EY1EZ1Fh1Fi1Fj1Fn1Fo1G01G11G21GQ1GR1GS1GT1GU1GV1GW1GX1GY1GZ1G[1G\1G]1Gb1I=1I>1IC1Jl1Jm1Jn1Jo1KG1KH1LQ1LR1MX1MY1MZ1Mk1O=1O>1O?1O@1OK1OL1OM1ON1OO1PU1Pe1Pf1Pg1QJ1QK1RW1R\1R]1Rb1Rc1S01Tk1To1U01U11V91V:1V;1V?1VC1VH1VM1VN1VO1VP1VQ1VR1VS1Wc1Wd1We1Y31Y71Y81Y91Y:1Y>1Y[1Y\1Y]1Y^1Y_1Y`1Ya1Yb1Yc1Yh1Yi1ZK1ZL1[\1\l1\m1\n1\o1^G1^H1^`1^a1_51_61_71_81`>1`B1`C1`D1`E1`F1`G1`L1`Q1`U1`V1`W1`X1`Y1`Z1`[1`\1`]1`^1`g1`h1`m1`n1`o1a01a11b:1b;1b@1bA1bB1bC1bD1bm1bn1bo1c01c11c21c61cH1cI1cJ1c_1c`1ce1cj1ck1cl1cm1cn1co1d01d11d21d31d41em1en1eo1f01f11f21gn1go1h01hL1hM1hQ1i@1iE1iF1kB1kC1ka1lg1lh1li1lj1lk1ll1lm1ln1lo1m01m51m61m;1mC1mD1mE1nD1nI1nJ1nK1nL1nM1nN1nO1nV1nW1oK1oP1oQ1oR1oS1o[1o\1o]1o^1of20K20L22322422<22@22A23_24324424524625E25F25G25H25N25O25T25Y25Z25[25\25m26226626727f28o2:52:62;l2;m2<22<[2<`2<a2<b2<c2<d2>K2>L2>M2>N2>O2>P2>T2>Y2>Z2>_2>`2>a2>b2>g2>l2@22@>2@?2@@2@A2@B2@F2@K2@L2@M2@N2@O2@P2@T2@U2@V2B02B12B22B32B82C>2CC2CD2CE2CF2EG2EH2EI2Eb2Ec2Ed2FA2F^2F_2G`2Hl2Im2KV2KW2MM2MN2MO2MP2MQ2MR2MS2MT2MU2MV2MW2MX2MY2MZ2M[2M\2M]2M^2M_2M`2Ma2Mb2Mc2Md2Me2Mf2Mg2Mh2Mi2Mj2Mk2Ml2Mm2Mn2Mo2N02N12N22N32N42N52N62N72N82N92N:2N;2N<2N=2N>2N?2N@2NA2NB2NC2ND2NE2NF2NG2NH2NI2NJ2NK2NL2NM2NN2NO2P<2QE2RN2TL2V92Wl2YY2Zb2Zc2[j2]W2_J2`S2b;2cc2eQ2fZ2gc2iP2kC2lL2m^2ng30T32B34535c37V38_39f3;T3<]3>K3@83Ae3CR3D[3FN3H;3ID3JM3L@3Mm3OU3QC3RL3SU3UC3W63Xn3Za3\I3]R3_:3`m3b63c^3eR3g?3i23j;3kD3m13nd40W42743e45R47E48K49T4;A4<n4>\4@R4B@4D34ES4F\4H44H54H64IE4JN4JO4L64L74MJ4NZ4Oj4QC4QD4RC4S>4Ti4Ud4Ue4Uf4WM4Y;4Y<4ZT4[l4]D4^\4^]4_c4_d4`c4bV4c\4c]4c^4dY4f@4g;4hb4hc4hd4i_4jZ4kU4kV4m14nX50?51b53K54c56;57657757858H59X5:W5:X5;S5<Z5<[5=a5?<5@@5@A5@B5Am5An5CQ5CR5D^5F25G[5HV5IQ5JL5JM5L:5M?5M@5N;5OS5Pk5Qf5Ra5S\5TW5UR5VQ5VR5VS5XF5YV5Zf5\M5^45_95`m5bT5dP5eZ5e[5g85h75i65i75jh5lD5mj5mk5ml5o05on61262062n63lS2FBS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp7rawjunk3x264RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB71p6rawlen4rawp7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp7rawjunk3x264RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFFFFFFS2FBS2p12LwS4END12p12Lw3HLwS3CRTS1p1a4rawp2HA2p12Lw4Hp1a3LWRFFS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HA2p12Lw4Hp1a3HLw3LWRFFFFS2sp3CRT2bs2FB3sp17rawjunk2p12Lw3LWRFFS3CRTS3CRTS2sp3CRT2bs2FB3sp13SP1S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R6rawlen4rawp7rawjunk4RLEN3RA3FS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFFFS3CRTFFFFFS2sp3CRT2bs2FB3sp17rawjunkS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R1p1a4rawp7rawjunk2RP2HA2rg2p12Lw4Hp1a3LWRFFFFFSFS2rg3HrgS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R1p4END14END26rawlen4rawp7rawjunk2RL3Hp14Hp2'3Hp34RLEN3RA13RA22p12Lw4Hp1a3HLw3LWRFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFFS2FBFFFFS2sp3CRT2bs4CRT02FB3sp17rawjunkFFFFFFFFFFFFS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS1R4STKc4STKn5STKcn2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkFFFS1R2sp3CRT2bs2FB3sp13FDDFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2rc3Hr31r2Kr1q1HS4FFRk2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg1HFFFS6rawlen2RSFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1p4END12p14Hp1rFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkFS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R1p4rawp7rawjunk2RP3Hp12rg2p14Hp1aS3sp1FS3CRTFS1p1a4rawp2HAS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R1p4END14END26rawlen4rawp7rawjunk2RP3Hp14Hp2'3Hp33RA42rg2p12Lw4Hp1a3HLw3LWRS2FBSFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFFS2FBS2FBS3CRTS3CRTFFFFFFS4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg1HFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS2FBFFFS2FBS2sp3CRT2bs2FB3sp12F07rawjunkFFFFFFFFS3CRTFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFFFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFS1R2sp3CRT2bs3DCD2FB3sp1FS3CRT2FB2xx2kk2Y12Y2FFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBSFFFFS3CRTS3CRTS2loFFFFFFFFSS1R3HIA1hFS3CRTFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgSS3CRTFFFFS2sp3CRT4blen2bs2B22FB3sp17rawjunk2rg3HrgFFFFFS2FBS2FB2x32NF3CRT3Hx1FFS1p1a4rawp2HA2p14Hp1aFS3CRTS3CRTFFFFFFFSFSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLEN2p12Lw3HLwFFFFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkFFS1p1a4rawp2HA2p12Lw4Hp1a3LWRFS2FBS2sp3CRT4blen2bs2B22FB3sp17rawjunk2rg2p12Lw3LWRS3CRTFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkFS2sp3CRT2bs2FB3sp13APC7rawjunkS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FFFFFFFFFS3CRTSS3CRTS2rg3HrgFFS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HA2p12Lw4Hp1a3HLwS3CRTFFFFFFS2p12LwFS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAS3CRTFFFS2rc3Hr3FFFS2sp3sp1S2sp3CRT4blen2bs2B22FB3sp17rawjunk2rgFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FS2Lw3LWRS2FBFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R1p4rawp7rawjunk3Hp12p14Hp1aS1p4rawp3Hp12p14Hp1aFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFFS1i2HiFS3CRTS3CRTFFFS2rg3Hrg1r2Kt1q1HS3CRTS2FBSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R1p4END14END21a6rawlen4rawp7rawjunk2RP4Hp2'3Hp32HA3RA42rg2p14Hp1r4Hp1aFS3CRTS2sp3CRT4blen2bs2B22FB3sp17rawjunk2rg3HrgS3CRTFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FFFFSS2FBS3CRTFS3CRTFFFS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LB4blen2DPFFFFS2FBS3CRTFFFFFS2FBFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen7rawjunk2RS4RLENFFFS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS3CRTFFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02DaSFS2sp3CRT2lo2bs2FB3sp13SP1FFS2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT2bs2FB3sp12F07rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x341CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x341CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFFS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk5nodes1c2HcFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B23SPH2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc7rawjunk3HSc5HTOPc5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFFS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT PHIn FFRn CNTn STKn GETNAME STKk C24k PKPARSE STKcf CRTFREE STKc1 STKc2 STKcn STKck STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIn_le FFRn_le CNTn_le PHIk0 FFRk0 CNTk0 PHIk_mono FFRk_mono PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono C24c C24c1 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF BUD24 SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_UID1"] Lemma S_SUBJ : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes : list Z) (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 (CRT + 128)) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes 0 [] 0 0 [] ext_own_zero sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes 0 [] 0 0 [] ext_own_zero sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUD2 hc Lc a -> 0 <= a <= p - rawp -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 96))
               (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9ba4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 B2' HA C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 12 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP. frame_aobj FSH (FB + 64) 1%nat as OLN.
    idtac "SUBJ-GT".
    gt_call p END1 (FB + 64) 48 ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "SUBJ-GT-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into rg; rename H0 into Hrg end.
    match goal with H : p <= ?q <= END1 |- _ => rename q into p1; rename H into Hp1r end.
    match goal with H : rw_cells _ _ (FB + 64) [C8 ?w] |- _ => rename w into Lw end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HOK end.
    (* [comment removed for export] *)
    zstep. if_cases Kt; zify_cond Kt.
    2: { idtac "SUBJ-TAG". do 3 zstep. refold_mu INV2 OW2 hc Lc FSHB.
      first [ eapply A_x509_crt_parse_C.free_call with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) (RA := 0xa9be4) (Lc := Lc)
            | eapply A_x509_crt_parse_C.free_call with (STKc := STKc) (BUF := BUF) (bs := bs) (RA := 0xa9be4) (Lc := Lc)
            | eapply A_x509_crt_parse_C.free_call with (STKc := STKc) (RA := 0xa9be4) (Lc := Lc)
            | eapply A_x509_crt_parse_C.free_call with (RA := 0xa9be4) (Lc := Lc) ];
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear; lia) | reflexivity
              | (eapply BUD2_E; [exact B2'| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia]) | eassumption | idtac ].
      all: match goal with |- forall _ : HST _ _ _, _ => idtac | |- ?g => idtac "SUBJ-TAG-LEFT:" g end.
      intros hq mq y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INVq CZq BXq.
      pose proof (AIh_laws asegs R HIA hq) as LAWSq. pose proof (KF_kinv asegs R HIA hq mo0) as KINVq.
      pose proof INVq as INVx. unfold A_x509_crt_parse_C.cinv in INVx.
      destruct INVx as (_ & HCSq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RSLq & _ & _ & MIq & _).
      assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo))
        by (eapply crange_mono; [exact HCSq| eapply crange_sub; [exact SCS0| exact LOS| xl HTOPc]]).
      do 3 zstep.
      rewrite (swrap32_land_errsum rg 18446744073709543040) by (clear - Hrg; lia).
      zstep.
      try (if_cases Kc; zify_cond Kc; [ exfalso; clear - Kc Hrg; rewrite ?signed_lit64 in Kc by lia; first [ lia | (Z.div_mod_to_equations; lia) ] | ]; clear Kc).
      do 2 zstep.
      pose proof (chunks_of_zero asegs CRT mq CZq) as CH0.
      pose proof (owns_zero asegs PK CRT mq ([] ++ LB) (Z_to_bv 64 0) (Z_to_bv 64 0)) as OW0.
      first [ eapply A_x509_crt_parse_C.exit2_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) (Lc := @nil blk) (rawlen := 0)
            | eapply A_x509_crt_parse_C.exit2_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Lc := @nil blk) (rawlen := 0)
            | eapply A_x509_crt_parse_C.exit2_walk with (STKc := STKc) (Lc := @nil blk) (rawlen := 0)
            | eapply A_x509_crt_parse_C.exit2_walk with (Lc := @nil blk) (rawlen := 0) ];
        first [ exact INVq | exact CH0 | exact OW0 | exact BXq | reflexivity | (clear - Hrg; lia)
              | lazymatch goal with
                | |- Permutation _ _ => cbn; apply Permutation_refl
                | |- cnt24 _ <= _ => cbn [app]; pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP; clear - DP; lia
                end
              | eassumption | match goal with |- ?g => idtac "SUBJ-TAG-EXIT-LEFT:" g end ]. }
    r_zero Kt Hrg. destruct (HOK R0) as [Hp1a HLw]. clear HOK.
    pose proof (bv_unsigned_in_range 64 Lw) as LWR. unfold bv_modulus in LWR. cbn [Z.pow Z.of_N Pos.pow] in LWR.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "SUBJ-EMPTY". refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_PK with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a) (p := p1);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B2' | eassumption
              | (clear - Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 HA; lia) | match goal with |- ?g => idtac "SUBJ-EMPTY-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 9 zstep.
    idtac "SUBJ-NAME".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    owns_now OWm hc Lc. si_mu.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => rename HHx into HHg end.
    clear RBY ORAW RIN.
    destruct (raw_side hc Lc mg _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc RP RL) as (RBY & _ & RIN & ORAW & _).
    lazymatch goal with FSHx : rw_cells _ mg (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 96) 1%nat as OPPg end.
    lazymatch goal with PRx : presW _ _ _ hc _ _ _ _ _ _ mg, SVx : rw_cells _ mg (bv_unsigned sp + -104) _ |- _ => pose proof (uwc_callee hc mg PRx HSc SVx) as UWF end.
    destruct (BUD_pre hc Lc _ _ _ a (bv_unsigned Lw) PHIn FFRn B2' ltac:(clear - HA; lia) ltac:(clear - LWR; lia) ltac:(clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 RBL; lia)
                ltac:(unfold KVc; pose proof (PHIk0 blen B2); lia) ltac:(unfold KFc; pose proof (FFRk0 blen (d + 1) B2); lia) PHIn_le FFRn_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHg) as NDLc.
    replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) in * by (clear; lia).
    idtac "SUBJ-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GETNAME with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (CUR := CRT + 224) (P := p1) (END := p1 + bv_unsigned Lw) (BUF := rawp) (bs := rawjunk) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold NAME_SIZE;
        replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) by (clear; lia);
        first [ exact HHg | exact HK1 | exact UWF | exact BPV | exact BPF | exact NDLc | exact RBY | exact RIN | exact OPPg | exact TPV
              | eassumption | reflexivity | (f_equal; clear; lia)
              | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3 Hp1r Hp1a HLw LWR
              | match goal with |- ?g => idtac "SUBJ-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & rc & p4 & j48' & mg' & pad7' & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HCUR4 & HNC4 & HND4 & HAP4 & HH4 & HRZ & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xa9c2c)) with (Z_to_bv 64 0xa9c2c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold NAME_SIZE in HP4.
    replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) in HV3, HFR3, HCNT3 by (clear; lia).
    idtac "SUBJ-BACK".
    pose proof (owns_pres hc Lc mg m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc HP4 MI4
                  ltac:(intros xx kk Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OWt.
    assert (SIP4 : si_P SI m4).
    { lazymatch goal with SIx : si_P SI mg |- _ => eapply (si_heap_presx asegs L SI); [exact SIx| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|] end.
      intros xx Hxx. exact (si_outside2 L SI (FB + 96) 8 (CRT + 224) 64 xx ltac:(xl) ltac:(xl) Hxx). }
    pres_call HP4.
    assert (LNL : Z.of_nat (length (CrtStmts.SNAME (rev nodes))) <= CNTn (bv_unsigned Lw)) by (unfold CrtStmts.SNAME; rewrite length_map, length_rev; exact HCNT3).
    pose proof (BUD_post hc hq3 Lc (CrtStmts.SNAME (rev nodes)) _ _ _ a (bv_unsigned Lw) PHIn FFRn CNTn B2' ltac:(clear - HA; lia) ltac:(clear - LWR; lia) PHIn_le FFRn_le CNTn_le HV3 HFR3 LNL) as B23.
    lazymatch goal with K7x : rw_cells _ mg (CRT + 224) _, PCx : rw_cells _ mg (FB + 96) _, STx : stk _ mg lo sp1, SSx : sshad _ _ mg slo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ =>
      clear K7x PCx STx SSx MIx SIx end.
    clear OW OWm HHg RBY ORAW OPPg.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, HNC4.
    assert (PERM1 : Permutation (CrtStmts.SNAME (rev nodes) ++ Lc) (crt_blocks (f_of ob rawlen rawp inext inodes (hd 0 nodes) nodes 0 0 [] ext_own_zero sigopts))).
    { rewrite crt_blocks_f_of. rewrite crt_blocks_f_of in PERM. change (ext_blocks ext_own_zero) with (@nil blk) in PERM |- *. cbn [app CrtStmts.SNAME map] in PERM |- *.
      eapply Permutation_trans; [apply Permutation_app; [apply perm_SNAME_rev| exact PERM]|]. perm_front. }
    assert (OW1 : owns asegs PK m4 ((CrtStmts.SNAME (rev nodes) ++ Lc) ++ LB) CRT ob rawlen rawp inext inodes (hd 0 nodes) nodes 0 0 [] ext_own_zero sigopts rawjunk).
    { pose proof (owns_grow hq3 (CrtStmts.SNAME (rev nodes)) Lc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ OWt PERM HH4 MI4) as OWg.
      unfold owns, crt_own_ok in OWg |- *. ddestruct OWg as (C1 & _ & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
      cbn [f_of co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen co_pkinfo co_pkctx co_pkowned cj_raw jraw] in C1, C3, C4, C5, C6, C7, C8, C9 |- *.
      refine (conj C1 (conj HNC4 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 _))))))))).
      exact (nodup_of_perm hq3 (CrtStmts.SNAME (rev nodes) ++ Lc) m4 _ HH4 PERM1). }
    assert (C241 : cnt24 ((CrtStmts.SNAME (rev nodes) ++ Lc) ++ LB) <= cnt24 LB + blen / 5889).
    { rewrite <- app_assoc. rewrite cnt24_small_app; [exact C24|]. intros b Hb. exact (SNAME_small _ b Hb). }
    idtac "SUBJ-SWITCHED".
    rename HCUR4 into K7. unfold name_blob in K7.
    fold_cinv INV2 m4 hq3 (CrtStmts.SNAME (rev nodes) ++ Lc) FSHB. ch_close m4.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "SUBJ-ERR". to_free.
      eapply free_walk with (Lc := CrtStmts.SNAME (rev nodes) ++ Lc) (r := rc); first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | (clear - RS; lia) | (clear - Hr3; lia)
            | (eapply BUD2_E; [exact B23| clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 RBL LWR; lia]) | match goal with |- ?g => idtac "SUBJ-ERR-LEFT:" g end ]. }
    idtac "SUBJ-OK". r_zero Kr Hr3. match goal with Hz : rc = 0 |- _ => pose proof (HEND Hz) as EP4 end. subst p4.
    eapply S_PK with (Lc := CrtStmts.SNAME (rev nodes) ++ Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a + bv_unsigned Lw) (p := p1 + bv_unsigned Lw);
      first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | exact C241 | exact B23 | eassumption
            | (clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 LWR; lia) | match goal with |- ?g => idtac "SUBJ-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04M0@D11881314528.379D20225638161.406D21461409897.379D36777195873.370D40775185266.370D42945744494.379D52056127147.404D52338696485.379D53340075670.406D60109196847.370D6192911893.404 D64348882538.381D64348882538.406K15835051771.370K1607432955.370 K21870859916.370K22945712379.370K33980871419.370K41095599355.370K52147535611.370L10370335306.1  L11183176311.1  L12408374717.1  L12914467981.1  L13303554957.1  L13633815370.359L13787728731.2  L13790153709.89 L1408793817.2   L14447004729.2  L1540615640.71  L15519992260.1  L15522417010.89 L15771191613.1  L15822417165.2  L1594761485.2   L1685717371.0   L17090287777.0  L17403231030.2  L17403765425.89 L18774735949.1  L19912320701.1  L19979998541.89 L19980537034.4  L20105749565.1  L20222892045.1  L204253020.2    L2049809421.1   L20622506269.2  L21461672313.1  L21564613915.71 L21650528252.377L21866712442.2  L22488405914.13 L22538743887.3  L22941438733.2  L23119474137.2  L23513807686.2  L2368029853.71  L2438896397.1   L25160623805.2  L25223747903.2  L26486612313.2  L26831527741.1  L26875616345.2  L27386516966.1  L27733139229.2  L27940336144.6  L28211258445.13 L28294674829.1  L29345674871.1  L29988482044.89 L29988725596.1  L30042772057.2  L30288275819.89 L30288785644.3  L31163742194.358L31862502771.1  L31863041268.89 L32327136116.1  L32454903270.1  L33450796305.2  L33597048665.2  L33946383677.1  L33985112333.2  L34629260685.1  L3482806040.89  L3483319967.1   L35655538583.72 L36266554869.6  L36460502135.1  L37622627047.5  L37875066173.1  L38070592189.1  L38235734261.1  L40281191306.3  L40711908697.2  L41099742989.2  L41103222873.2  L42040144748.89 L42040425420.1  L42133206669.1  L43571151479.1  L44466151385.2  L4572017369.2   L45826000746.3  L45826514669.89 L45885110541.1  L45908482845.2  L48487939594.89 L48495798995.2  L49441483277.1  L50453671614.7  L51002642050.8  L51909129149.1  L51953172697.2  L52160193805.2  L52338958389.1  L52491779133.1  L5436592646.13  L54745125893.8  L55797076866.13 L56173068735.9  L57186025976.5  L57798807159.1  L58811373739.2  L58885089625.2  L59257267289.2  L59308586248.2  L59413075133.1  L59728556298.359L60098049293.1  L6042617148.1   L60754583113.0  L60907323927.3  L60915193550.89 L61053789918.358L61366595865.359L62419456268.1  L63199674356.379L63475677325.1  L64410505893.3  L64418367100.89 L64432594957.1  L64454402074.89 L64456827052.1  L64471510986.359L64584198252.2  L64586655724.3  L6487220337.3   L6586925716.17  L6588862828.17  L66332265789.1  L66721351741.1  L66914912701.1  L67367117072.89 L67376035273.4  L68012312349.2  L6899380056.1   L6906665613.1   L7382465640.1   L7736014575.2   L8254604469.3   L8255118642.89  L8742280115.2   L8793638983.75  L8896078297.2   L9080482849.71  L9179029314.2   L9551655181.1   L9579045661.2   P1396571726.404 P14461423358.370P14847612824.404P20635450250.404P216606155.404  P22134471192.404P23131762510.404P26033826406.404P26482582478.404P26863263438.404P27745557898.404P30038937806.404P30296385645.404P33010176920.404P33143934054.404P33377767064.404P33593214414.404P34508873193.404P3985014296.404 P40707551182.404P41090869966.404P428624152.404  P44179613286.404P44470508878.404P4568051790.404 P45912840586.404P46851611017.404P47601162904.404P47809338136.404P51365709848.404P51948749390.404P54465921638.404P58653617304.404P58872736718.404P59270211278.404P62211563928.404P62785740056.404P65767921304.404P67999892874.404P7750690063.370 P7866543718.404 P8497851288.404 P8908366670.404 P9191382485.404 P9566232970.404 Q10048016802.366Q12344480484.366Q12931746950.367Q1396571726.404 Q15985628819.406Q17943790173.366Q17946263133.367Q19546638454.404Q19546672262.377Q20635450250.404Q21200200696.367Q216606155.404  Q22540266473.404Q23131762510.404Q23708806264.367Q24594481446.367Q25154845979.404Q25226056638.404Q25816004610.366Q26482582478.404Q2676383091.406 Q26863263438.404Q27628535116.366Q27745557898.404Q29288584337.367Q29364068300.366Q30038937806.404Q30602569224.366Q30603046306.366Q30839988077.367Q33593214414.404Q36777195873.370Q36779176801.369Q40707551182.404Q40772909426.369Q40775185266.370Q41090869966.404Q42439443119.370Q44470508878.404Q4500090468.366 Q4568051790.404 Q45912840586.404Q47388050434.366Q49698585326.368Q49746415830.370Q50244178959.377Q51948749390.404Q53579323758.404Q57618602681.370Q58743905100.377Q58746361881.366Q58812957453.404Q58872736718.404Q59270211278.404Q60281595153.367Q6192911893.404 Q6480460759.404 Q65096557789.367Q65098225885.366Q67038978349.370Q67999892874.404Q68281680193.404Q8699115497.370 Q8754632996.404 Q8908366670.404 Q9191382485.404 Q9566232970.404 Q9644549497.377 Q9644581257.404 00001602A03G04Z05m07308=09C0:N0;j0=00=10><0?L0@\0Al0C<0DL0E\0Fl0G20G60G;0G@0GE0HC0HD0Hb0Hc0Hd0I:0I;0JI0JN0JO0JP0JQ0JR0JS0K[0K`0Ke0M@0MA0MF0MK0ML0MQ0MR0MW0Mo0O50O60OO0OP0OQ0OR0O]0P50P:0P;0P<0P=0PB0PC0PG0PH0PI0PY0P^0Pb0R10R20R30RU0RV0RW0RX0Sf0Sj0Sn0T<0T=0TB0TC0TH0UX0UY0W10WE0WI0WZ0W_0Wd0Wh0X10X20X30X40XW0XX0X]0Xa0Xb0Xc0Xd0YG0YL0YM0ZS0ZT0ZY0ZZ0Z[0Z`0Za0Zb0Zg0Zl0[`0[a0\;0\<0\=0\A0\B0\C0\D0\J0\O0]M0]R0]W0]X0]Y0_H0`O0aM0aR0aS0aX0aY0c@0cE0d90d:0e80e@0eA0eB0eC0eD0eI0eN0eS0gJ0gK0gL0gP0gU0gY0gZ0g[0h_0h`0ja0jb0k;0k<0kA0kB0lE0n?0ol10o12213_14b16J17M18P19S1:V1;b1=O1?71@d1Ag1CO1E<1F?1GB1Ho1JW1KZ1L]1M`1OM1Q:1Rg1TT1UW1WE1Y21Z51[81\e1^R1`?1aB1c41d\1fI1gL1hO1iR1k11kh1m81m91m:1n11nh20821H21I22\22]24J24K25^27=28e2:J2;Z2;[2<[2<\2=S2=T2>K2?B2?C2@62AU2BT2BU2Ca2Dm2Dn2F:2GF2GG2H^2H_2IV2IW2IX2Jh2Kl2MQ2NL2NM2OL2P`2Q[2RN2T;2T<2T=2U42V32Wa2XX2YO2[G2[H2\_2^L2_l2_m2_n2_o2`m2akS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS4rawpS2FBS3CRTS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FS2sp3CRT2bs2FB3sp13APC7rawjunkFFS2sp3CRT2bs2FB3sp13SP1FS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTFFSSFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkS3CRTS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS3CRTFS3CRTFS3CRTS1R2sp3CRT2bs2FB3sp13FDDS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS1p4END14rawp3Hp12p24Hp2rFFFS6rawlen2RSS1R2sp3CRT2bs3DCD2FB3sp1S3CRTFFFS3CRTFS2FBFFS1p4END12p24Hp2rS3CRTS2FBS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS2FBS2FBS4rawp7rawjunkFS3CRTFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS3CRT2FB2xx2kk2Y12Y2S2FBS2FB1x2NF3CRT3Hx1S3CRTS3CRTS2loS1R3HIA1hFFFS2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkFS3CRTS2FBFFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS3CRTFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FS3CRTFFS3CRTFFS3CRTS3CRTS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFS1p4END11a4rawp2HA2p24Hp2rFFS2FBFFFS1i2HiS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S3CRTS3CRTSFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S3CRTFS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S3CRTS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F02F14SP1R7rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2rk3HrkFFFFS3CRTS3CRTS3CRTS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4FFS2FBS3CRTS2FBFFS1R4STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02DaFS2sp3CRT2lo2bs2FB3sp13SP1FS3CRTFS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7FS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk1c2HcFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72HBFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stFS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72HB5Ha_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p3ir45HTOPc2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p3ir42HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc7rawjunk3HSc5HTOPcS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p3ir45HTOPc2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFFS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT DATES PHIn FFRn CNTn STKn GETNAME STKk C24k PKPARSE STKcf CRTFREE STKc1 STKc2 STKcn STKck STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIn_le FFRn_le CNTn_le PHIk0 FFRk0 CNTk0 PHIk_mono FFRk_mono PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono C24c C24c1 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF BUD24 SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_UID1"] Lemma S_DATES : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes : list Z) (rawjunk : list byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 (CRT + 128)) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128))
         (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes 0 [] 0 0 [] ext_own_zero sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes 0 [] 0 0 [] ext_own_zero sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUD2 hc Lc a -> 0 <= a <= p - rawp -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (Z.shiftr (CRT + 128) 3 + al_sb AL)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 FB) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 96))
               (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9b5c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 B2' HA C24.
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 17 zstep.
    idtac "DATES-PRE".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    owns_now OWm hc Lc. si_mu.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => rename HHx into HHg end.
    destruct (raw_side hc Lc mg _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    assert (RINc : In (rawp, Z.of_nat (length rawjunk)) ((Lc ++ LB) ++ fdata LF')) by (apply in_app_iff; left; exact RIN).
    lazymatch goal with FSHx : rw_cells _ mg (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 96) 1%nat as OPPg end.
    pose proof DATES as SPD. unfold x509_get_dates_stmtA, A_X509_GET_DATES in SPD.
    idtac "DATES-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPD with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (TM := CRT + 288) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_GET_DATES_STACK_A;
        first [ exact HHg | exact RBY | exact ORAW | exact OPPg | exact TPV | eassumption | reflexivity | (f_equal; clear; lia)
              | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
              | match goal with |- ?g => idtac "DATES-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_get_dates_postA in PO.
    ddestruct PO as (u0 & u1' & u2' & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3' & u4' & u5 & u6 & m2 & hq2 & rk & p2 & tb2
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & TM2 & Hp2r).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xa9ba0)) with (Z_to_bv 64 0xa9ba0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "DATES-BACK".
    pose proof (owns_pres hc Lc mg m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc HP2 MI2
                  ltac:(intros xx kk Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OW2.
    assert (SIP2 : si_P SI m2).
    { lazymatch goal with SIx : si_P SI mg |- _ => eapply (si_heap_presx asegs L SI); [exact SIx| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|] end.
      intros xx Hxx. exact (si_outside2 L SI (FB + 96) 8 (CRT + 288) 48 xx ltac:(xl) ltac:(xl) Hxx). }
    pres_call HP2.
    lazymatch goal with K8x : rw_cells _ mg (CRT + 288) _, PCx : rw_cells _ mg (FB + 96) _, STx : stk _ mg lo sp1, SSx : sshad _ _ mg slo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ =>
      clear K8x PCx STx SSx MIx SIx end.
    clear OW OWm HHg RBY ORAW OPPg.
    presA_transport HP2.
    clear HP2 SPD.
    switch_h hc hq2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (B22 : BUD2 hq2 Lc a) by (unfold BUD in *; rewrite Evol2, Efr2; exact B2').
    idtac "DATES-SWITCHED".
    rename TM2 into K8.
    fold_cinv INV2 m2 hq2 Lc FSHB. ch_close m2.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "DATES-ERR". to_free.
      eapply free_walk with (Lc := Lc) (r := rk); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrk; lia)
            | (eapply BUD2_E; [exact B22| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia]) | match goal with |- ?g => idtac "DATES-ERR-LEFT:" g end ]. }
    idtac "DATES-OK".
    eapply S_SUBJ with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a) (p := p2);
      first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B22 | eassumption
            | (clear - Hp2r Hp1 Hp2 Hp2' Hp3 HA; lia) | match goal with |- ?g => idtac "DATES-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0:S0@C18971418195.401C23922862675.400D11881018327.410D11891817072.401D16071854214.401D16901939902.401D26917807890.410D36777195873.379D3953997537.378 D3953997537.379 D40091843490.450D40775185266.379D42035635047.401D42945709401.410D43665348967.401D49804782053.450D51070157262.450D52045925387.448D56536395888.401D60109196847.379D60109446735.401D60189065437.378D60189065437.379D6203698357.448 D62588687198.410K10114639055.401K10499531215.401K10674151503.401K13096823887.401K1396569935.401 K15835051771.379K1607432955.379 K16827801039.401K17610693583.401K21302816458.401K216607946.401  K21870859916.379K22861045682.401K22945712379.379K23131760207.401K26482584271.401K26863261647.401K28281397455.401K30038940111.401K30419638991.401K3179121999.401 K33593216207.401K33980871419.379K3591543988.379 K39316523727.401K40707548879.401K41090868175.401K41095599355.379K42696720207.401K44470506575.401K4568054095.401 K46427712719.401K50191716943.401K50368437455.401K51948751695.401K52147535611.379K57689895247.401K58872734415.401K59270213583.401K63420573106.401K64991401423.401K8908368463.401 L10102288217.2  L10487310937.2  L10687032281.2  L10840411873.2  L10912730231.1  L11127496333.1  L11183176311.1  L11208760655.3  L12082103731.2  L12304858636.1  L12348516960.17 L12408374717.1  L12877562377.17 L12880089589.17 L12974448687.17 L13092792281.2  L13535484557.1  L13543595425.19 L1408793817.2   L14301694619.2  L14402536426.388L14447004729.2  L14693717588.95 L14695810623.2  L14786404065.2  L1540615640.71  L1548849343.89  L15519992260.1  L15522251860.95 L15522417010.89 L15771191613.1  L15822417165.2  L1594761485.2   L16023460231.89 L16840545881.2  L1685717371.0   L168650209.2    L16916955281.2  L17570370680.95 L17578921351.3  L17606135897.2  L17611635570.89 L17659824141.1  L18023395959.1  L18302214263.1  L19364945151.18 L19376904127.18 L19857242653.2  L19912320701.1  L19979638891.95 L19980537034.4  L20105749565.1  L20127766261.95 L20128105044.3  L204253020.2    L21022654349.1  L21113771402.366L21221417243.2  L21298324828.2  L21564613915.71 L21593730587.2  L21619305308.1  L21619519194.95 L21644325741.3  L21650968832.402L21652625941.375L21654730866.2  L21866712442.2  L22095213153.2  L22429046806.10 L22573296152.405L22866772043.3  L22941438733.2  L22982591434.2  L23119474137.2  L23513807686.2  L23766154372.426L24390532629.95 L24392100470.2  L25160623805.2  L25539744171.2  L25636326795.2  L2621559066.1   L26486612313.2  L26831527741.1  L26875616345.2  L26917907765.1  L26976280605.2  L26983613546.4  L27026841770.267L27026841770.391L27386516966.1  L2770202465.2   L27940391089.89 L28277369689.2  L28331070221.1  L28632618922.2  L29066840183.1  L29092470029.1  L29345674871.1  L30042772057.2  L30431990105.2  L3058445732.2   L31145622673.2  L31489692490.405L3182954201.2   L31862502771.1  L31862612434.95 L32327136116.1  L32454903270.1  L32802883775.9  L33314616971.89 L33597048665.2  L33817424237.3  L33946383677.1  L33985112333.2  L34360251219.95 L34362187459.2  L3482380862.95  L3482806040.89  L3483319967.1   L35250260877.1  L3532059019.2   L35445917965.1  L35627916443.2  L35655538583.72 L3598635821.3   L36266554869.6  L36307103329.2  L363258721.2    L36442108371.2  L36449675308.95 L36460502135.1  L3726076129.2   L37875066173.1  L38019675677.2  L38070592189.1  L38235734261.1  L38259954321.2  L38756030411.267L39321010521.2  L39379299611.2  L39768386075.2  L39864004961.2  L40228640085.0  L40281191306.3  L40312999379.267L40711908697.2  L41099742989.2  L41103222873.2  L41663468698.392L42683970777.2  L42754206861.1  L43226826465.2  L43571151479.1  L43597331579.5  L43810982283.2  L44466151385.2  L4572017369.2   L46012794146.95 L46014895433.4  L46354690673.3  L4638061450.89  L46431676249.2  L46882717723.2  L4700111548.17  L47049041130.3  L47242118263.1  L47506568936.267L47870616696.2  L48068055434.89 L48487939594.89 L49304025233.2  L49673405709.1  L50051061275.2  L50187819481.2  L50241372557.1  L50381248345.2  L50440147739.2  L50925318027.2  L51599199555.439L51906071000.2  L51908265048.3  L51909129149.1  L51953172697.2  L52160193805.2  L52200163714.18 L52245217821.2  L52491779133.1  L52501688386.2  L53130300941.2  L53516992816.391L53527181501.2  L53997053467.2  L54056779677.71 L54174754203.2  L5436592646.13  L54676236769.2  L54745125893.8  L55224207780.3  L55225352820.2  L56418360977.2  L56592702936.2  L57359870875.2  L57685342937.2  L57698627611.2  L57779397874.2  L57798807159.1  L58302423030.2  L58304457431.95 L58748093688.5  L58885089625.2  L59257267289.2  L59308586248.2  L59413075133.1  L6008660450.10  L6042617148.1   L60448817524.1  L60754583113.0  L60915193550.89 L61140948570.364L61366595738.392L61366595865.366L61401481953.2  L6152188705.0   L61567515068.267L61567515068.391L62011818785.0  L62588459385.1  L63422184011.3  L639424795.2    L64275438605.1  L64418367100.89 L64471510986.366L64526681523.2  L6487220337.3   L6495215682.95  L64979181145.2  L6503971261.3   L6522106337.2   L65404616823.1  L65482165311.2  L65607387291.2  L65772514707.267L6616277517.1   L66298372189.2  L66332265789.1  L66472807965.2  L66721351741.1  L66914912701.1  L66925224585.376L67195190383.95 L67195304425.1  L67461776529.2  L6798276507.2   L68220898317.1  L6899380056.1   L6906665613.1   L7088503905.2   L7282981857.2   L7382465640.1   L7736014575.2   L8105295519.1   L8113055584.95  L8548109403.2   L8550302155.95  L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.89  L9241447853.95  L9243705405.1   N26872553873.400N48204456022.400N55966132906.400N60733400192.400N63430872977.400N66590330291.400O1001933565.401 O10618990077.401O11746403965.401O11930563540.399O14542167037.401O15460105085.401O16350966909.401O17494624509.401O17750585469.401O18155437218.401O18626760061.401O19357757918.398O19770425853.401O19931227630.401O20935596669.401O22221714158.401O30245212782.401O3078286936.401 O32096263534.401O32537874520.401O33239929326.401O33990841394.401O34031148413.401O35592798351.401O366419438.401  O36680917870.401O37630280430.401O39838419581.401O40463046306.401O41843596285.401O42197094638.401O43277289469.401O44195227517.401O4440802429.401 O44425156733.401O44938202843.399O45122245047.401O45423855982.401O45969540168.401O48862730990.401O50473853.401   O50817538813.401O52020260349.401O5312795005.401 O54023336829.401O54381021294.401O55209884805.399O55518239188.399O5585524989.401 O56848487390.398O57201466440.401O57537483645.401O59278274632.401O60687394173.401O60978474237.401O61464066679.401O62206064366.401O63123445358.401O63904362034.401O64128366333.401O64204162429.401O64474006218.401O65961212488.399O66562860014.401O67171060367.401O7590719101.401 P10851408966.401P1406747886.448 P14304577628.378P14304577628.379P14461423358.379P14793198662.401P14832643384.448P16923509334.378P16923509334.379P182826822.401  P19859259946.448P202219371.448  P21207000028.378P21207000028.379P21608672476.378P21608672476.379P21647862485.399P21658526154.399P22080053446.401P22141042872.448P22971318541.378P22971318541.379P23121499630.448P25154843674.401P25650503468.401P26027233478.448P26484447598.448P26873455726.448P26974115882.448P2784312774.401 P28627113325.378P28627113325.379P29449380920.448P30040746606.448P30285664973.448P30429833582.448P3064266499.401 P31146933846.378P31146933846.379P32877070928.448P33007855928.448P33142142662.448P33380168760.448P33599225710.448P33810555850.399P34494424905.448P3530433324.401 P35626081884.378P35626081884.379P357446086.401  P3591543988.378 P3591543988.379 P36322327750.401P3741301318.401 P38017633834.448P38261788758.378P38261788758.379P39390572508.378P39390572508.379P39771269340.378P39771269340.379P3982673080.448 P39879222214.401P40714065262.448P41101054062.448P426308536.448  P43225306182.401P43817786156.401P44185672902.448P44463990766.448P4574038766.448 P46340546774.398P46849745705.448P46884029148.378P46884029148.379P47047506707.401P47607750712.448P47803277752.448P47876372191.399P49296947798.378P49296947798.379P50057614556.378P50057614556.379P50442506716.378P50442506716.379P50927926572.399P51359658680.448P51951155438.448P52247394858.448P52503840885.448P53529750042.401P53998888156.378P53998888156.379P54190221148.378P54190221148.379P54467803334.448P54662134598.401P56407612502.378P56407612502.379P57344928092.378P57344928092.379P57713046236.378P57713046236.379P58668062264.448P59259427950.448P61391540294.401P62226537272.448P62792329144.448P64538971685.401P6480458454.398 P6515303238.401 P653319132.378  P653319132.379  P65606077020.378P65606077020.379P66292560634.401P66474980906.448P67476194902.378P67476194902.379P6809023836.378 P6809023836.379 P7086878406.401 P7297149254.401 P7606020176.448 P7750690063.379 P7852086470.448 P8495976760.448 P8754630693.401 P8893913582.448 Q10048380702.375Q11208522825.448Q12931746950.375Q1406747886.448 Q15985628819.450Q16057205670.374Q16071854214.401Q16472810971.401Q17944153313.375Q17946263133.376Q19546884730.402Q19561349487.375Q19561563123.376Q19561624278.448Q19859259946.448Q202219371.448  Q21294101882.376Q21767670690.401Q21832736479.401Q21930397408.401Q23121499630.448Q23708806264.376Q23957120639.378Q23957120639.379Q24594481446.375Q25161418683.448Q25473514713.401Q25539506349.448Q25816364734.375Q25952160488.377Q25952160488.378Q26484447598.448Q2676383091.450 Q26873455726.448Q26974115882.448Q27938304182.436Q2803826605.401 Q28465177121.375Q28465177121.376Q29288584337.376Q29363966320.375Q29775981542.401Q30040746606.448Q30429833582.448Q30602209460.375Q30602636970.401Q30602945310.375Q30839988077.376Q32437204119.401Q3260556108.378 Q3260556108.379 Q33599225710.448Q34669522109.401Q34671242809.376Q34671291067.401Q35292017451.436Q36630502558.375Q36777195873.379Q36779176801.378Q37546564045.378Q37546564045.379Q38017633834.448Q38833220926.375Q39180574961.378Q39180574961.379Q39439682456.401Q40550330331.401Q40714065262.448Q40772909426.378Q40775185266.379Q41101054062.448Q41414298335.401Q42439168719.401Q42439443119.378Q42439443119.379Q44463990766.448Q4500447448.375 Q4574038766.448 Q45741809296.378Q45741809296.379Q47387953854.375Q47957748593.401Q48118064779.401Q49698585326.377Q49746198710.401Q49746415830.378Q49746415830.379Q50233694694.375Q50244489971.402Q51722040728.401Q51951155438.448Q52136395990.401Q52247394858.448Q52503840885.448Q5265442331.376 Q5265442331.377 Q53577458638.448Q53915159046.374Q54624410993.401Q55415036769.378Q55415036769.379Q55705402538.401Q57618602681.378Q57618602681.379Q57828105177.401Q58743871165.401Q58744348080.402Q58746001061.375Q58746425531.401Q59259427950.448Q59660120105.376Q60191312605.377Q60191312605.378Q6203698357.448 Q6486966647.448 Q65482193950.448Q66474980906.448Q67038703949.401Q67038978349.378Q67038978349.379Q68266720225.448Q8362820247.401 Q8699115497.378 Q8699115497.379 Q8699324297.401 Q8744444804.448 Q8893913582.448 Q9356559674.378 Q9633798953.448 Q9634015756.376 Q9634064528.375 Q9644499845.402 Q9644583048.401 00000400801A02G04C06107:08Q0:N0<P0=e0?<0@B0AK0BQ0Cf0E;0FN0GT0I40JC0LN0N^0Om0Q60R90S<0T?0UB0VE0WY0Xm0Z00[30\60]90^M0`E0aY0b\0c_0db0ee0fh0gk0hn0j10kE0ll0mo0o210511I12L13O14R15U16X17[18^1:21;51<81=;1?31@61A91A:1A;1A<1A=1A>1AC1AG1AH1AO1AT1Ad1Ai1Aj1Ak1BG1BH1BM1CP1CQ1CR1CS1CT1D81D91D:1DP1Em1En1G<1HJ1HO1HP1HQ1Hk1Hl1Hm1Hn1Ho1KB1KC1KD1LR1LW1L[1L\1L]1L^1L_1Ld1N?1N@1NE1On1Oo1P01P51Q;1Q<1Q=1QU1QV1QW1Rf1Rg1T01U61U71U81U91UJ1V\1V]1V^1V_1V`1Vk1Vl1WO1WP1WQ1WR1WS1WX1WY1W^1W_1Wd1We1X21Ym1\L1\P1\Q1]Y1]Z1]_1]`1]d1]i1]m1]n1]o1^01^11_A1_B1_C1`Q1`U1`Y1`Z1a71a81a91a>1a?1aa1ab1c21dB1dC1dH1dI1dN1dO1eg1eh1f<1f=1f>1f?1gE1gI1gJ1gO1gP1gU1gY1gZ1hg1hh1hi1hj1hk1hl1i51jH1jI1jJ1jK1kT1kU1kZ1k[1k_1l11l21l31l41mm1mn1mo1ok1ol1om20I20J20N21=21>23:24@24A24F24G24H24M24N24O24P27227:27;27@27A27B28A28B28G28H28O29X29Y29Z2:22:32:g2:h2:i2:j2;22;32;;2;<2;=2;>2;F2;J2;K2<i2<j2<k2<l2=22=72=H2=M2=Q2=R2?A2@P2AY2B_2B`2Ba2DW2G12G22G72G82G92G>2He2Ik2Il2Im2KT2KU2KV2KW2K[2K\2K]2K^2Kc2Kd2Ki2Kj2Ko2L42M:2MY2MZ2M[2M\2Ma2Me2Mj2Mk2Ml2N02N12N22OL2OM2Ok2Ol2Qm2Qn2Qo2RH2Re2SB2SC2TD2UP2VQ2X:2X;2Z12Z22Z32Z42Z52Z62Z72Z82Z92Z:2Z;2Z<2Z=2Z>2Z?2Z@2ZA2ZB2ZC2ZD2ZE2ZF2ZG2ZH2ZI2ZJ2ZK2ZL2ZM2ZN2ZO2ZP2ZQ2ZR2ZS2ZT2ZU2ZV2ZW2ZX2ZY2ZZ2Z[2Z\2Z]2Z^2Z_2Z`2Za2Zb2Zc2Zd2Ze2Zf2Zg2Zh2Zi2Zj2Zk2Zl2Zm2Zn2Zo2[02[12[22[32\`2]i2_e2af2cd2eQ2gD2iE2kP2m=2nF2oO31K33L35H37I37J38Q3:>3<13=m3?n3A73B_3DG3F53G>3HG3IP3K=3M83O83Pk3R43SF3TO3V<3X73Z73[e3]X3_F3a93bB3cI3e73fe3ha3jb3lO3nZ40j42W44D45M47H49H4;D4=E4?A4AB4C54Db4Ek4G44Hg4JT4L<4Mj4O34P<4Qj4S]4UY4WZ4YR4[E4]84^`4`[4b[4dW4fX4hT4jU4l=4n04o950B51K53354o57058l5:m5<a5>N5@I5BI5DE5FF5Ga5I?5K25L;5Mh5O[5QN5Rn5T\5VI5XE5ZF5\B5^C5_I5`R5bM5dM5fI5hJ5j75kd5mR5oH61662i64I65R67968l6:D6:E6:F6;m6=T6=U6>T6?S6@f6B66CF6D_6D`6Da6E\6GG6HB6HC6HD6I_6I`6Ia6KH6M66M76Nj6PB6Qm6S]6S^6Td6Te6Tf6VO6WN6XU6Y\6Z[6[Z6\`6\a6\b6]]6^X6`?6aF6aG6aH6aI6aJ6bE6c@6d;6eJ6g16hA6iQ6kM6mN6mO6ng70e72h73c73d73e75576E76F77A78G79d7;H7;I7<H7<I7<J7<K7=c7=d7?G7@S7Ag7CN7E<7F77G27Gm7Gn7I[7I\7I]7Je7Km7M27NJ7NK7Of7QD7R?7TP7Vh7X@7Y;7Z67[17[l7[m7[n7]h7_g7`l7b`7dK7dL7f37gm7in7kK7kL7m;7o180M82382483884<85:868876884S2FBS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTc2HB5Ha_st5Hl_st4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodes2x32HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp7rawjunk3x264RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB71p6rawlen4rawp7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END16rawlen4rawp7rawjunk3x264RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFFFFS3CRTS2FBFS2p12LwS3CRTS4END12p12Lw3HLwS3CRTFFS1p1a4rawp2HA2p12Lw4Hp1a3LWRFS3CRTS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HA2p12Lw4Hp1a3HLw3LWRFFFFS2sp3CRT2bs2FB3sp17rawjunk2p12Lw3LWRFFS2sp3CRT2bs2FB3sp13SP1S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R6rawlen4rawp7rawjunk4RLEN3RA3FS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTFFS2sp3CRT2bs2FB3sp17rawjunkFSFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R1p4END14END26rawlen4rawp7rawjunk2RL3Hp14Hp2'3Hp34RLEN3RA13RA22p12Lw4Hp1a3HLw3LWRFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTS2FBFFFFS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS1R4STKc4STKn5STKcn2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkFFS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS1R2sp3CRT2bs2FB3sp13FDDFFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFS2rc3Hr31r2Kr1q1HS4FFRk2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg1HFFFFS6rawlen2RSFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkFFFFS3sp1FS3CRTFS3CRTFS1p1a4rawp2HAS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R1p4END14END26rawlen4rawp7rawjunk2RP3Hp14Hp2'3Hp33RA42rg2p12Lw4Hp1a3HLw3LWRS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END26rawlen4rawp7rawjunk2RP3Hp14Hp2'3Hp33RA42rg2p12Lw4Hp1a3HLw3LWRS2FBFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFS3CRTFS2FBS3CRTS2FBFFFFS4PHIk2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rg1HFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS2FBS2FBFS2sp3CRT2bs2FB3sp12F07rawjunkFFS3CRTFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS3CRTFS3CRTFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFS3CRT2FB2xx2kk2Y12Y2FFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBFS3CRTFS3CRTS2loFS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R1p1a4rawp7rawjunk2RP2HA2rg2p14Hp1aFFFFSS1R3HIA1hS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R1p4rawp7rawjunk2RP3Hp12rg2p12Lw4Hp1a3LWRFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgFS3CRTFS2FBS2FB2x32NF3CRT3Hx1FFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLEN2p12Lw3HLwFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkFFS1p1a4rawp2HA2p12Lw4Hp1a3LWRFS2FBS2sp3CRT4blen2bs2B22FB3sp17rawjunk2rg2p12Lw3LWRFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FS3CRTFFS3CRTFFFS1R2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72ja2jb6rawlen7rawjunk2RL3RBL2rg2R02rc5nodes2R13WF13WF32L8S2rg3HrgFS3CRTFFS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HA2p12Lw4Hp1a3HLwFS3CRTFS2p12LwS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgFFS1R2sp3CRT2bs3DCD2FB3sp1FS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFFFS2rc3Hr3FS2sp3sp1FFFS2Lw3LWRS2FBFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R1p4rawp7rawjunk3Hp12p14Hp1aFFFS1i2HiS3CRTS2rg3Hrg1r2Kt1q1HS3CRTS2FBSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFSS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R1p4END14END21a6rawlen4rawp7rawjunk2RP4Hp2'3Hp32HA3RA42rg2p14Hp1r4Hp1aS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END21a6rawlen4rawp7rawjunk2RP4Hp2'3Hp32HA3RA42rg2p14Hp1r4Hp1aSS3CRTFFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FFFS2FBFFFS3CRTFS3CRTFS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2sp3CRT2bs4CRT02FB3sp17rawjunkFFFS3CRTS2FBS3CRTFFS2FBFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen7rawjunk2RS4RLENFS2sp3CRT2bs2FB3sp13APC7rawjunkFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT2bs2FB3sp12F07rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x341CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x341CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x341CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4FBLO4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1FS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA32HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA32HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunk2rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunk2rg5nodesFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk5nodes1c2HcFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBFFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1FS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st1p4END1FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st1p4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND2HB5Ha_st5Hl_st1p4END1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st1p4END1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc7rawjunk3HSc5HTOPc5nodesFS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st1p4END1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk5nodesFS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk5nodesS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT DATES PHIn FFRn CNTn STKn GETNAME STKk C24k PKPARSE STKcf CRTFREE STKc1 STKc2 STKcn STKck STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIn_le FFRn_le CNTn_le PHIk0 FFRk0 CNTk0 PHIk_mono FFRk_mono PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono C24c C24c1 Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF BUD24 SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_UID1"] Lemma S_ISSUER : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
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
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 B2' HA C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 16 zstep. ja_join. zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP. frame_aobj FSH (FB + 64) 1%nat as OLN.
    idtac "ISS-GT".
    gt_call p END1 (FB + 64) 48 ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "ISS-GT-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into rg; rename H0 into Hrg end.
    match goal with H : p <= ?q <= END1 |- _ => rename q into p1; rename H into Hp1r end.
    match goal with H : rw_cells _ _ (FB + 64) [C8 ?w] |- _ => rename w into Lw end.
    match goal with H : rg = 0 -> _ |- _ => rename H into HOK end.
    (* [comment removed for export] *)
    zstep. if_cases Kt; zify_cond Kt.
    2: { idtac "ISS-TAG". do 2 zstep. refold_mu INV2 OW2 hc Lc FSHB.
      eapply ea0_walk with (Lc := Lc) (rg := rg); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrg; lia)
            | (eapply BUD2_E; [exact B2'| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia]) | match goal with |- ?g => idtac "ISS-TAG-LEFT:" g end ]. }
    r_zero Kt Hrg. destruct (HOK R0) as [Hp1a HLw]. clear HOK.
    pose proof (bv_unsigned_in_range 64 Lw) as LWR. unfold bv_modulus in LWR. cbn [Z.pow Z.of_N Pos.pow] in LWR.
    (* [comment removed for export] *)
    do 11 zstep.
    idtac "ISS-NAME".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    owns_now OWm hc Lc. si_mu.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => rename HHx into HHg end.
    clear RBY ORAW RIN.
    destruct (raw_side hc Lc mg _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc RP RL) as (RBY & _ & RIN & ORAW & _).
    lazymatch goal with FSHx : rw_cells _ mg (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 96) 1%nat as OPPg end.
    lazymatch goal with PRx : presW _ _ _ hc _ _ _ _ _ _ mg, SVx : rw_cells _ mg (bv_unsigned sp + -104) _ |- _ => pose proof (uwc_callee hc mg PRx HSc SVx) as UWF end.
    destruct (BUD_pre hc Lc _ _ _ a (bv_unsigned Lw) PHIn FFRn B2' ltac:(clear - HA; lia) ltac:(clear - LWR; lia) ltac:(clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 RBL; lia)
                ltac:(unfold KVc; pose proof (PHIk0 blen B2); lia) ltac:(unfold KFc; pose proof (FFRk0 blen (d + 1) B2); lia) PHIn_le FFRn_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHg) as NDLc.
    replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) in * by (clear; lia).
    idtac "ISS-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GETNAME with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (CUR := CRT + 160) (P := p1) (END := p1 + bv_unsigned Lw) (BUF := rawp) (bs := rawjunk) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold NAME_SIZE;
        replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) by (clear; lia);
        first [ exact HHg | exact HK1 | exact UWF | exact BPV | exact BPF | exact NDLc | exact RBY | exact RIN | exact OPPg | exact TPV
              | eassumption | reflexivity | (f_equal; clear; lia)
              | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3 Hp1r Hp1a HLw LWR
              | match goal with |- ?g => idtac "ISS-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & rc & p4 & j48' & mg' & pad7' & nodes
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HCUR4 & HNC4 & HND4 & HAP4 & HH4 & HRZ & HEND).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xa9b54)) with (Z_to_bv 64 0xa9b54 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold NAME_SIZE in HP4.
    replace (p1 + bv_unsigned Lw - p1) with (bv_unsigned Lw) in HV3, HFR3, HCNT3 by (clear; lia).
    idtac "ISS-BACK".
    pose proof (owns_pres hc Lc mg m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWm PERM HHg HCSc HP4 MI4
                  ltac:(intros xx kk Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OWt.
    assert (SIP4 : si_P SI m4).
    { lazymatch goal with SIx : si_P SI mg |- _ => eapply (si_heap_presx asegs L SI); [exact SIx| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|] end.
      intros xx Hxx. exact (si_outside2 L SI (FB + 96) 8 (CRT + 160) 64 xx ltac:(xl) ltac:(xl) Hxx). }
    pres_call HP4.
    assert (LNL : Z.of_nat (length (CrtStmts.SNAME (rev nodes))) <= CNTn (bv_unsigned Lw)) by (unfold CrtStmts.SNAME; rewrite length_map, length_rev; exact HCNT3).
    pose proof (BUD_post hc hq3 Lc (CrtStmts.SNAME (rev nodes)) _ _ _ a (bv_unsigned Lw) PHIn FFRn CNTn B2' ltac:(clear - HA; lia) ltac:(clear - LWR; lia) PHIn_le FFRn_le CNTn_le HV3 HFR3 LNL) as B23.
    lazymatch goal with K6x : rw_cells _ mg (CRT + 160) _, PCx : rw_cells _ mg (FB + 96) _, STx : stk _ mg lo sp1, SSx : sshad _ _ mg slo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ =>
      clear K6x PCx STx SSx MIx SIx end.
    clear OW OWm HHg RBY ORAW OPPg.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, HNC4.
    assert (PERM1 : Permutation (CrtStmts.SNAME (rev nodes) ++ Lc) (crt_blocks (f_of ob rawlen rawp (hd 0 nodes) nodes 0 [] 0 0 [] ext_own_zero sigopts))).
    { rewrite crt_blocks_f_of. rewrite crt_blocks_f_of in PERM. change (ext_blocks ext_own_zero) with (@nil blk) in PERM |- *. cbn [app CrtStmts.SNAME map] in PERM |- *.
      eapply Permutation_trans; [apply Permutation_app; [apply perm_SNAME_rev| exact PERM]|]. perm_front. }
    assert (OW1 : owns asegs PK m4 ((CrtStmts.SNAME (rev nodes) ++ Lc) ++ LB) CRT ob rawlen rawp (hd 0 nodes) nodes 0 [] 0 0 [] ext_own_zero sigopts rawjunk).
    { pose proof (owns_grow hq3 (CrtStmts.SNAME (rev nodes)) Lc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ OWt PERM HH4 MI4) as OWg.
      unfold owns, crt_own_ok in OWg |- *. ddestruct OWg as (_ & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
      cbn [f_of co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen co_pkinfo co_pkctx co_pkowned cj_raw jraw] in C2, C3, C4, C5, C6, C7, C8, C9 |- *.
      refine (conj HNC4 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 _))))))))).
      exact (nodup_of_perm hq3 (CrtStmts.SNAME (rev nodes) ++ Lc) m4 _ HH4 PERM1). }
    assert (C241 : cnt24 ((CrtStmts.SNAME (rev nodes) ++ Lc) ++ LB) <= cnt24 LB + blen / 5889).
    { rewrite <- app_assoc. rewrite cnt24_small_app; [exact C24|]. intros b Hb. exact (SNAME_small _ b Hb). }
    idtac "ISS-SWITCHED".
    rename HCUR4 into K6. unfold name_blob in K6.
    fold_cinv INV2 m4 hq3 (CrtStmts.SNAME (rev nodes) ++ Lc) FSHB. ch_close m4.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "ISS-ERR". to_free.
      eapply free_walk with (Lc := CrtStmts.SNAME (rev nodes) ++ Lc) (r := rc); first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | (clear - RS; lia) | (clear - Hr3; lia)
            | (eapply BUD2_E; [exact B23| clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 RBL LWR; lia]) | match goal with |- ?g => idtac "ISS-ERR-LEFT:" g end ]. }
    idtac "ISS-OK". r_zero Kr Hr3. match goal with Hz : rc = 0 |- _ => pose proof (HEND Hz) as EP4 end. subst p4.
    ja_split. zstep.
    eapply S_DATES with (Lc := CrtStmts.SNAME (rev nodes) ++ Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a + bv_unsigned Lw) (p := p1 + bv_unsigned Lw);
      first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | exact C241 | exact B23 | eassumption
            | (clear - HA HLw Hp1r Hp1a Hp1 Hp2 Hp2' Hp3 LWR; lia) | match goal with |- ?g => idtac "ISS-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.
  End Call.
End Walk.
