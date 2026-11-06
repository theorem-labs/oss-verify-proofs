(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg P_x509_crt_parse.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_crt_parse_stmt24 A_crt_free_stmt2 A_pkcs7_free A_x509_crt_free A_x509_crt_parse_area A_x509_crt_parse_A A_x509_crt_parse_B A_x509_crt_parse_C A_x509_crt_parse_D A_x509_crt_parse_E A_x509_crt_parse_F A_x509_crt_parse_G A_asn1_get_int_loops A_x509_get_serial A_x509_get_alg A_x509_get_sig_alg A_x509_get_name_stmt A_x509_get_name_stmtE A_pk_parse_stmt A_x509_get_uid A_x509_crt_ext_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_x509_get_san_A A_x509_get_dates_A A_x509_crt_ext_A A_x509_get_sig_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
(* [comment removed for export] *)
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
Ltac chunk_split H n H1 H2 ::=
  lazymatch type of H with
  | OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.firstn n cs) in
      let post := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.skipn n cs) in
      change (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx A (Corelib.Init.Datatypes.app pre post)) in H;
      apply (proj1 (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.CellsX.rw_cells_app sg mx A pre post)) in H;
      destruct H as [H1 H2];
      let z := eval cbv in (Stdlib.ZArith.BinInt.Z.of_nat (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.cells_size pre)) in
      change (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx (Stdlib.ZArith.BinInt.Z.add A z) post) in H2
  end.
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


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19084332856.75L19088626119.72L19088626119.73L3488822390.1  00001R02702Q02VS1R2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR3ALO2F02F13APB4SP1R1B1k2HR3Bce3FB'2n'3HR'S1R3HIA1h2sp3CRT2lo2bs5CRTLO2FB3sp11XS1R2sp3CRT2bs3DCD2FB3sp11XS3CRT". (* [comment removed for export] *)
  Lemma cstk : forall (hc : HST asegs R HIA) Lh mq, HM asegs R HIA hc Lh LF' mq -> (forall b, In b LB -> In b Lh) -> CRT + 744 <= arl_stklo R.
  Proof.
    intros hc Lh mq HH SUB. flat constr:((hm_apart asegs R HIA hc _ _ _ HH)) 2%nat. intros BR _. rewrite Forall_forall in BR.
    pose proof (art_data_lo asegs R HIA) as DLO.
    destruct (CWX (CRT + 743) ltac:(clear; lia)) as [X|[X|X]]; [xl X| xl X DLO|].
    flat constr:(X) 3%nat. flclear X. intros (B & k) HB HR. cbn [fst snd] in HR. apply in_app_iff in HB. destruct HB as [HB|HB].
    - destruct (BR (B, k) ltac:(apply in_app_iff; left; apply SUB; exact HB)) as (_ & _ & Bce & _). cbn [fst snd] in Bce. xl Bce HR.
    - destruct (in_fdata_hull LF (B, k) (CRT + 743) HB ltac:(cbn [fst snd]; exact HR)) as ([FB' n'] & HF & HR').
      destruct (BR (FB', n') ltac:(apply in_app_iff; right; right; exact HF)) as (_ & _ & Bce & _). cbn [fst snd] in Bce, HR'. xl Bce HR'.
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
  Lemma own_apart : forall (hc : HST asegs R HIA) Lc mq x k, HM asegs R HIA hc (Lc ++ LB) LF' mq -> (forall y, CS y -> hcs asegs R HIA hc y) -> In (x, k) Lc -> 0 < k ->
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
    flat constr:((hm_apart asegs R HIA hc _ _ _ HH)) 2%nat. intros BR HAP. rewrite Forall_forall in BR.
    destruct (BR (x, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HIN)) as (_ & _ & Bce & Bimg). cbn [fst snd] in Bce, Bimg.
    pose proof (blocks_apart_app_lr (Lc ++ LB) LF' x k FB 512 HAP ltac:(apply in_app_iff; left; exact HIN) ltac:(left; reflexivity)) as A3.
    pose proof ALO. pose proof LOS. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact A5| exact Bimg].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L53965678973.198L56765669119.201L61160186364.20900000a01Q02QS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB3S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB31a2HaS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp14LFB31x1k2A12A22A32A4". (* [comment removed for export] *)
  Lemma owns_mu : forall (hc : HST asegs R HIA) Lc mm mm' ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
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
      flat constr:((own_apart hc Lc mm x k HH HCSq XL Hk)) 5%nat. intros A1 A2 A3 A4 _. cbn [disjoint_from]. pose proof SLOu. pose proof NS1. pose proof STKc0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L48789554681.1  L53965678973.20300000500fS3SPcS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB3". (* [comment removed for export] *)
  Lemma owns_pres : forall (hc : HST asegs R HIA) Lc mm mm' LFc SPc SSPc TOPc Wc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
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
      flat constr:((own_apart hc Lc mm x k HH HCSq XL Hk)) 5%nat. intros A1 A2 A3 A4 A5.
      apply HW; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L15085325610.193L59308579414.200L59310683405.196L59314873579.199L6037081027.194 00001a04405\07?08^S1R3HIA1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB34SSPc4TOPc3HSS2HT1c1HS1R4STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB23LFB2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL2FB3sp15BUFLO3SPR2F04FBLO4SP1R4LFB32G11a2Hs3Hin1H2H12H2S1R2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB3DCD2FB3sp13APC3SPR2F03APB3FDD4SP1R4LFB31a3Hd13HinS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB31a1B1j2Hr3Hin1HS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB33SPc2HS1a1H". (* [comment removed for export] *)
  Lemma presA_down : forall Lq SPc SSPc TOPc Wc mA mB,
    presA asegs R (Lq ++ LB) LF' SPc SSPc TOPc Wc mA mB -> SPc <= bv_unsigned sp -> SSPc <= bv_unsigned sp -> hstkhi asegs R HIA h <= TOPc ->
    (forall x, outside WSI x -> (FB <= x < FB + 512 -> False) -> outside Wc x) ->
    presA asegs R LB LF (bv_unsigned sp) (bv_unsigned sp) (hstkhi asegs R HIA h) WSI mA mB.
  Proof.
    intros Lq SPc SSPc TOPc Wc mA mB [P S] HS HSS HT HW. flat constr:(FRSH) 4%nat. intros G0 G1 G2 G3. split.
    - intros a Ha Hc Ho. apply P; [exact Ha| |].
      + destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
        exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; apply (fdata_cons_sub b [] FB 512 LF); exact Hb].
      + apply HW; [exact Ho|]. intros Hin. destruct Hc as [Hs|[[Hd1 Hd2]|(bk & Hbk & Hr)]].
        * pose proof ALO. pose proof LOS. pose proof SLOu. pose proof NS1. pose proof STKc0. lia.
        * lia.
        * destruct bk as [B j]. cbn [fst snd] in Hr. pose proof (G3 B j Hbk). lia.
    - intros c Hc Hs. apply S; [| exact Hs].
      destruct Hc as [H|[H|[H|H]]]; [left; lia| right; left| right; right; left| right; right; right; exact H].
      + flat constr:(H) 3%nat. intros b Hb Hr. exists b. split; [apply in_app_iff; right; exact Hb| exact Hr].
      + flat constr:(H) 3%nat. intros b Hb Hr. exists b. split; [right; exact Hb| exact Hr].
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
    (flat constr:(INV) 23%nat; flclear INV; intros HHc HCSc HTc HSc HFc FHD LV LN PC LP1 LP2 LO2 FSH SAVE RSL SThi STlo MI OCRT PRES SS1 SS2 SIP);
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
  Ltac ch_open CH := (flat constr:(CH) 16%nat; flclear CH; intros K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15);
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
              intros x Hx NF; cbn [outside app] in Hx |- *; (flat constr:(Hx) 2%nat; flclear Hx; intros Hx1 Hx2);
              repeat (split; [first [exact Hx2 | clear - Hx1 NF; lia]|]); first [exact I | exact Hx2] ]);
      let PX1 := fresh "PX" in let PX2 := fresh "PX" in
      (flat constr:(PRx) 2%nat; flclear PRx; intros PX1 PX2);
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
  Lemma uwc_callee : forall (hc : HST asegs R HIA) mq, presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) WSI m mq ->
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
  Lemma BUD_E : forall hc Lc kv kf kc a, BUD hc Lc kv kf kc a -> kv <= KVc blen -> kf <= KFc blen d -> kc <= 2 + CNTk -> 0 <= a <= blen -> BUDE hc Lc.
  Proof.
    intros hc Lc kv kf kc a (V1 & V2 & V3) HV HF HC Ha. unfold BUDE, PHIc, FFRc, CNTc in *.
    pose proof (PHIj_mono a blen ltac:(lia)). pose proof (FFRj_mono a blen d ltac:(lia)). pose proof (CNTj_mono a blen ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L29426751976.17500001SS4CNTk4CNTj2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB31H2H0". (* [comment removed for export] *)
  Lemma CNTc0 : 0 <= CNTc blen.
  Proof. unfold CNTc. pose proof (CNTj0 blen B2). pose proof CNTk0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L41433769834.18100001nS1R3HIA5PHIcf5FFRcf1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB32hc2Lc2V12V22V31H2H0". (* [comment removed for export] *)
  Lemma BUDE_X : forall hc Lc, BUDE hc Lc -> BUDX hc Lc.
  Proof.
    intros hc Lc (V1 & V2 & V3). pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). unfold BUDX. lia.
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
  Lemma raw_in_Lc : forall Lc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts,
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) -> 0 < rawp -> In (rawp, rawlen) Lc.
  Proof.
    intros Lc ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts PERM RP.
    eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite crt_blocks_f_of.
    do 5 (apply in_or_app; right). unfold oblk. destruct (Z.eqb_spec rawp 0) as [E|_]; [lia| left; reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L25914671739.203000014S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36rawlen4rawp7rawjunk2BB". (* [comment removed for export] *)
  Lemma raw_side : forall (hc : HST asegs R HIA) Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
    owns asegs PK mq (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    HM asegs R HIA hc (Lc ++ LB) LF' mq -> (forall y, CS y -> hcs asegs R HIA hc y) -> 0 < rawp -> 0 < rawlen ->
    bytes_at asegs mq rawp rawjunk /\ Z.of_nat (length rawjunk) = rawlen /\ In (rawp, Z.of_nat (length rawjunk)) (Lc ++ LB)
    /\ aobj asegs AL (hcs asegs R HIA hc) mq rawp (Z.of_nat (length rawjunk))
    /\ (rawp + rawlen <= CRT \/ CRT + 744 <= rawp) /\ (rawp + rawlen <= FB \/ FB + 512 <= rawp) /\ rawp + rawlen <= lo
    /\ rawp + rawlen <= alloc_ceiling.
  Proof.
    intros hc Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk OW PERM HH HCSq RP RL.
    flat constr:((raw_facts asegs PK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OW RP)) 4%nat. intros RBY RLEN RIN _.
    pose proof (raw_in_Lc _ _ _ _ _ _ _ _ _ _ _ _ _ PERM RP) as XL.
    flat constr:((own_apart hc Lc mq rawp rawlen HH HCSq XL RL)) 5%nat. intros A1 A2 A3 _ _.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L53965678973.198000014S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13ACV4LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  Lemma owns_grow : forall (hq : HST asegs R HIA) Lq Lc mq ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk,
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

  Lemma nodup_of_perm : forall (hq : HST asegs R HIA) Lx mq (l : list blk),
    HM asegs R HIA hq (Lx ++ LB) LF' mq -> Permutation Lx l -> List.NoDup (map fst l).
  Proof.
    intros hq Lx mq l HH P. pose proof (HMND _ _ _ _ HH) as N. rewrite map_app in N. apply NoDup_app_inv_l in N.
    eapply Permutation_NoDup; [apply Permutation_map; exact P| exact N].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L45217030384.199L45217031031.198L52460146199.20500001e03Z06YS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a1w2Ha2Hw3HawS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71a1w2Ha2Hw3HawS1R3HIA5PHIcf5FFRcf4PHIj4FFRj1h2LF2sp3CRT4blen3BUF2bs4LFB23LFB2B24CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2kv2kf1a1w4PHIq4FFRq2V12V22HV2HF1H2H02H12H22H32H42BV2BF2H52H6". (* [comment removed for export] *)
  Lemma BUD_pre : forall (hc : HST asegs R HIA) Lc kv kf kc a w (PHIq : Z -> Z) (FFRq : Z -> Z -> Z),
    BUD hc Lc kv kf kc a -> 0 <= a -> 0 <= w -> a + w <= blen -> kv <= KVc blen -> kf <= KFc blen d ->
    (forall x, 0 <= x -> PHIq x <= PHIj x) -> (forall x e, 0 <= x -> FFRq x (e + 1) <= FFRj x e) ->
    havol asegs R HIA hc + PHIq w <= AVOL_MAX /\ hfr asegs R HIA hc + FFRq w (d + 1) <= FR_MAX.
  Proof.
    intros hc Lc kv kf kc a w PHIq FFRq (V1 & V2 & _) Ha Hw Haw HV HF LP LF0.
    pose proof (LP w Hw). pose proof (LF0 w d Hw).
    pose proof (PHIj_sadd a w Ha Hw). pose proof (FFRj_sadd a w d Ha Hw).
    pose proof (PHIj_mono (a + w) blen ltac:(lia)). pose proof (FFRj_mono (a + w) blen d ltac:(lia)).
    pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc in BV, BF.
    pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L56925402997.20500003;S1R3HIA4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2h'2Lc2Lq2kv2kf2kc1a1w4PHIq4FFRq4CNTq2V12V22V32HV2HF2HN1H2H02H12H22H32H4". (* [comment removed for export] *)
  Lemma BUD_post : forall (hc h' : HST asegs R HIA) Lc (Lq : list blk) kv kf kc a w (PHIq : Z -> Z) (FFRq : Z -> Z -> Z) (CNTq : Z -> Z),
    BUD hc Lc kv kf kc a -> 0 <= a -> 0 <= w ->
    (forall x, 0 <= x -> PHIq x <= PHIj x) -> (forall x e, 0 <= x -> FFRq x (e + 1) <= FFRj x e) -> (forall x, 0 <= x -> CNTq x <= CNTj x) ->
    havol asegs R HIA h' <= havol asegs R HIA hc + PHIq w -> hfr asegs R HIA h' <= hfr asegs R HIA hc + FFRq w (d + 1) ->
    Z.of_nat (length Lq) <= CNTq w ->
    BUD h' (Lq ++ Lc) kv kf kc (a + w).
  Proof.
    intros hc h' Lc Lq kv kf kc a w PHIq FFRq CNTq (V1 & V2 & V3) Ha Hw LP LF0 LC HV HF HN. unfold BUD.
    pose proof (LP w Hw). pose proof (LF0 w d Hw). pose proof (LC w Hw).
    pose proof (PHIj_sadd a w Ha Hw). pose proof (FFRj_sadd a w d Ha Hw). pose proof (CNTj_sadd a w Ha Hw).
    rewrite length_app. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cnt24_small_all : forall l : list blk, (forall b, In b l -> snd b < 5889) -> cnt24 l = 0.
  Proof.
    induction l as [|[A k] l IH]; intros H; [reflexivity|].
    rewrite cnt24_cons_small by (apply (H (A, k)); left; reflexivity). apply IH. intros b Hb. apply H. right. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L60281290533.179000011S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lx". (* [comment removed for export] *)
  Lemma cnt24_small_app : forall (Lq Lx : list blk), (forall b, In b Lq -> snd b < 5889) -> cnt24 (Lq ++ Lx) = cnt24 Lx.
  Proof. intros Lq Lx H. rewrite cnt24_app, (cnt24_small_all Lq H). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L32248750578.17800000nS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  Lemma ext_blocks_small : forall eo b, In b (ext_blocks eo) -> snd b < 5889.
  Proof.
    intros eo b Hb. unfold ext_blocks, SSEQ in Hb. repeat (apply in_app_iff in Hb; destruct Hb as [Hb|Hb]);
      apply in_map_iff in Hb; (flat constr:(Hb) 3%nat; flclear Hb; intros x <- _); cbn [snd]; unfold SEQ_SIZE; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L53680648178.17800000nS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  Lemma SNAME_small : forall l b, In b (SNAME l) -> snd b < 5889.
  Proof. intros l b Hb. unfold SNAME in Hb. apply in_map_iff in Hb. flat constr:(Hb) 3%nat. flclear Hb. intros x <- _. cbn [snd]. unfold NAME_SIZE. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac perm_front :=
    rewrite ?app_assoc; repeat apply Permutation_app_tail; rewrite <- ?app_assoc;
    first [ apply Permutation_refl | eapply Permutation_trans; [apply Permutation_app_comm|]; rewrite <- ?app_assoc; apply Permutation_refl ].

  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L16526487874.188L19616048289.191L2192452093.187 L22676661558.188L24188363034.188L32883993289.191L38339916114.19100002004005i07b09_0;b0=9S2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz3HB12H22H32HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12HL1i2Hi1HS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12H3S2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H22HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz3HB02H12HLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB71B3bsx2P02Lz2H12H32HL1i2Hi1HS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72mX1B3bsx2P02Lz2HL1i2Hi1H". (* [comment removed for export] *)
  Lemma bslice : forall mX B bsx P0 Lz, bytes_at asegs mX B bsx -> B <= P0 -> 0 <= Lz -> P0 + Lz <= B + Z.of_nat (length bsx) ->
    bytes_at asegs mX P0 (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))
    /\ Z.of_nat (length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))) = Lz.
  Proof.
    intros mX B bsx P0 Lz (HB0 & HB1 & HB) H1 H2 H3.
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
      (flat constr:((bslice mx rawpz rj P0z nz RBYx ltac:(Hs) ltac:(Hs) ltac:(Hs))) 2%nat; intros PB PL);
      (flat constr:((bslice mx rawpz rj Q0z nz RBYx ltac:(Hs) ltac:(Hs) ltac:(Hs))) 2%nat; intros QB QL);
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L27206181164.184L27212478941.185L5436598838.187 L5436599221.186 L5919078973.193 00001502:03?04D071S2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71a2HaS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71a2HaS1R3HIA4PHIk4FFRk5PHIcf5FFRcf4PHIj4FFRj1h2LF2sp3CRT4blen3BUF2bs4LFB23LFB2B24CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc1a1w2V12V21H2H02H12H22BV2BF2H32H4". (* [comment removed for export] *)
  Lemma BUD_pk_pre : forall (hc : HST asegs R HIA) Lc a w, BUD2 hc Lc a -> 0 <= a <= blen -> 0 <= w <= blen ->
    havol asegs R HIA hc + PHIk w <= AVOL_MAX /\ hfr asegs R HIA hc + FFRk w (d + 1) <= FR_MAX.
  Proof.
    intros hc Lc a w (V1 & V2 & _) Ha Hw.
    pose proof (PHIk_mono w blen ltac:(lia)). pose proof (FFRk_mono w blen (d + 1) ltac:(lia)).
    pose proof (PHIj_mono a blen ltac:(lia)). pose proof (FFRj_mono a blen d ltac:(lia)).
    pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc, KVc, KFc in BV, BF.
    pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L27206187739.189L27212478941.190L56925402481.19100001>02L05HS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lc5owned1w2HwS2LF2sp3CRT4blen2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lc5owned1w2HwS1R3HIA4PHIk4FFRk4CNTk4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc2h'2Lc5owned1a1w2V12V22V32Hw2HV2HF2HN1H2H0". (* [comment removed for export] *)
  Lemma BUD_pk_post : forall (hc h' : HST asegs R HIA) Lc (owned : list blk) a w, BUD2 hc Lc a -> 0 <= w <= blen ->
    havol asegs R HIA h' <= havol asegs R HIA hc + PHIk w -> hfr asegs R HIA h' <= hfr asegs R HIA hc + FFRk w (d + 1) ->
    Z.of_nat (length owned) <= CNTk -> BUDK h' (owned ++ Lc) a.
  Proof.
    intros hc h' Lc owned a w (V1 & V2 & V3) Hw HV HF HN. unfold BUD, KVc, KFc.
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
  Lemma BUD2_E : forall (hc : HST asegs R HIA) Lc a, BUD2 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
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
  Lemma BUD1_E : forall (hc : HST asegs R HIA) Lc a, BUD1 hc Lc a -> 0 <= a <= blen -> BUDE hc Lc.
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

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma exit_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    BUDX hc Lc -> rawlen < 2^40 -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) -> -2^31 < r <= 0 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 CRT) (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) s9v (Z_to_bv 64 r) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a8edc) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_C.exit_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.exit_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.exit_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.exit_walk ]; eassumption.
  Qed.

  Lemma free_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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

  (* [comment removed for export] *)

  Lemma S_UID1 : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k64 k72 k96 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v s7v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 END2) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 k72 (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) k96 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 END1) ->
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
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) s5v (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a9580) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_D.S_UID1 with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_D.S_UID1 with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_D.S_UID1 with (STKc := STKc) | eapply A_x509_crt_parse_D.S_UID1 ]; eassumption.
  Qed.

  (* [comment removed for export] *)

  Lemma S_ISSUER : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k64 k72 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (rawjunk : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7v s10v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         (Z_to_bv 64 END2) (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 k72 (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 END1) ->
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
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) (Z_to_bv 64 CRT) (Z_to_bv 64 FB) s7v (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) s10v
               s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a93cc) fc None mm (seg_rom asegs)).
  Proof.
    intros. first [ eapply A_x509_crt_parse_E.S_ISSUER with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_E.S_ISSUER with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_E.S_ISSUER with (STKc := STKc) | eapply A_x509_crt_parse_E.S_ISSUER ]; first [ eassumption | exact S_UID1 ].
  Qed.

  (* [comment removed for export] *)

  Lemma S_SERALG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
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
  Proof.
    intros. first [ eapply A_x509_crt_parse_F.S_SERALG with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_F.S_SERALG with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_F.S_SERALG with (STKc := STKc) | eapply A_x509_crt_parse_F.S_SERALG ]; first [ eassumption | exact S_ISSUER ].
  Qed.

  (* [comment removed for export] *)

  Lemma S_TBS : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END2 : Z)
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
    intros. first [ eapply A_x509_crt_parse_G.S_TBS with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_G.S_TBS with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_G.S_TBS with (STKc := STKc) | eapply A_x509_crt_parse_G.S_TBS ]; first [ eassumption | exact S_SERALG ].
  Qed.

  (* [comment removed for export] *)
  Ltac post_callA_k segs m ktac :=
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO;
    destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
    (flat constr:(PO) 2%nat; flclear PO; intros E (MUc & (WMc & PO)));
    first [ (flat constr:(PO) 2%nat; flclear PO; intros MIc PO) | rename PO into MIc ];
    subst ms';
    lazymatch type of MUc with
    | munch _ m ?m' =>
        ktac MUc;
        transport_after_callA segs m m' MUc;
        transport_after_call segs m m' MUc WMc;
        clear MUc WMc;
        try match goal with H : mem_inv segs m |- _ => clear H end;
        try clear m
    end;
    try destruct_ands PO;
    try (lazymatch goal with
    | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ])
    end).
  Tactic Notation "acallxA_sp_k" constr(e) tactic3(apptac) tactic3(ktac) :=
    lazymatch goal with
    | |- aevtA ?segs (KF _ ?R ?HIA ?h ?mo0) _ (MS _ _ _ _ _ ?m _) =>
        eapply (aevtA_cut_evtA_KF segs R HIA h mo0);
        [ apptac
        | lazymatch goal with |- forall x, ?P x -> _ => let hd := head_of P in try unfold hd end;
          rewrite ?(unsigned_lit e) by qlia; post_callA_k segs m ktac ]
    end.

  (* [comment removed for export] *)
  Lemma owns_rawnull : forall mq LBq rl, owns asegs PK mq LBq CRT (Z_to_bv 64 0) rl 0 0 [] 0 [] 0 0 [] ext_own_zero 0 [].
  Proof.
    intros mq LBq rl. pose proof (crt_own_ok_zero asegs PK mq LBq CRT) as OZ. unfold owns, crt_own_ok, crt_own_zero, f_of, jraw in *.
    cbn [co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen
         co_pkinfo co_pkctx co_pkowned cj_raw eo_san_next eo_san eo_akid_next eo_akid eo_pol_next eo_pol eo_eku_next eo_eku ext_own_zero crt_blocks oblk] in *.
    flat constr:(OZ) 10%nat. flclear OZ. intros C1 C2 C3 C4 C5 C6 C7 _ C9 C10.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj (or_introl eq_refl) (conj C9 C10))))))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59314955108.300000:S2rp3RP01E". (* [comment removed for export] *)
  Lemma owns_raw : forall mq LBq ob rl rp rj, 0 < rp -> In (rp, rl) LBq -> 0 <= rl -> rw_cells asegs mq rp [CB (Z.to_nat rl) rj] ->
    owns asegs PK mq LBq CRT ob rl rp 0 [] 0 [] 0 0 [] ext_own_zero 0 rj.
  Proof.
    intros mq LBq ob rl rp rj RP0 RIN RL0 RC. pose proof (crt_own_ok_zero asegs PK mq LBq CRT) as OZ. unfold owns, crt_own_ok, crt_own_zero, f_of, jraw in *.
    cbn [co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen
         co_pkinfo co_pkctx co_pkowned cj_raw eo_san_next eo_san eo_akid_next eo_akid eo_pol_next eo_pol eo_eku_next eo_eku ext_own_zero crt_blocks] in *.
    flat constr:(OZ) 10%nat. flclear OZ. intros C1 C2 C3 C4 C5 C6 C7 _ C9 _.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj (or_intror (conj RIN (conj RL0 RC))) (conj C9 _))))))))).
    unfold crt_blocks, oblk. cbn [co_pkowned co_sigopts co_issuer co_subject co_eku co_san co_pol co_akid co_rawp co_rawlen map app].
    change (0 =? 0) with true. cbn [app]. destruct (Z.eqb_spec rp 0) as [E|_]; [exfalso; clear - E RP0; lia|].
    cbn [map fst]. constructor; [intros []| constructor].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition chz (mq : mem) : Prop := ltac:(lazymatch type of (chunks_of_zero asegs CRT mq) with _ -> ?T => exact T end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0<70@C17025509154.379C20605776350.380D10823602677.340D12660900391.340D12948125919.342D12948125919.359D12948125919.382D15171508883.342D15171508883.359D15171508883.382D20225638161.342D28276504733.381D29310291280.308D29310291280.343D29310291280.360D29310291280.381D3254887012.340 D36535857971.381D38829999353.381D3953997537.307 D3953997537.308 D4247594702.381 D50043152237.381D52056127147.340D53340075670.342D60109196847.308D60109196847.342D60109196847.343D60109196847.359D60109196847.360D60109196847.381D60109196847.382D60109462710.381D60135608610.308D60135608610.343D60135608610.360D60189065437.307D60189065437.308D6192911893.340 D64348882538.342K12406281821.342K12406281821.359K12406281821.382K13470823987.380K13673647951.308K13673647951.343K13673647951.360K13673647951.381K13814188457.380K15785876189.342K15785876189.359K15785876189.382K19528418680.308K19528418680.343K19528418680.360K19528418680.381K19901838685.342K19901838685.359K19901838685.382K20107851741.342K20107851741.359K20107851741.382K20585147443.380K2402099251.380 K24522234931.380K24570173524.359K24570173524.382K24696789939.380K26837814493.342K26837814493.359K26837814493.382K28039579049.380K31616223666.380K33952671453.342K33952671453.359K33952671453.382K35152870313.380K35794295631.308K35794295631.343K35794295631.360K35794295631.381K37872973533.342K37872973533.359K37872973533.382K38081081693.342K38081081693.359K38081081693.382K38539504307.380K38967881039.308K38967881039.343K38967881039.360K38967881039.381K39114298675.380K44164039966.308K44164039966.342K44164039966.343K44164039966.359K44164039966.360K44164039966.381K44164039966.382K46052363699.380K46204797353.380K49150115352.360K49150115352.381K49645997722.380K50003040079.308K50003040079.343K50003040079.360K50003040079.381K5102058973.342 K5102058973.359 K5102058973.382 K51923804253.342K51923804253.359K51923804253.382K52481290205.342K52481290205.359K52481290205.382K52975363123.380K53319133097.380K53339808051.380K53550014643.380K57117894991.308K57117894991.343K57117894991.360K57117894991.381K57674246562.380K59419363165.342K59419363165.359K59419363165.382K5943137414.380 K60454537011.380K6053107420.342 K6053107420.359 K6053107420.382 K64387845545.380K6534324147.380 K66325978845.342K66325978845.359K66325978845.382K66706676701.342K66706676701.359K66706676701.382K66917014109.342K66917014109.359K66917014109.382K6740335923.380 K67775544499.380K68169700175.308K68169700175.343K68169700175.360K68169700175.381L10110341284.8  L10139782565.9  L10195936580.3  L10390414532.3  L10728525522.365L10762723780.3  L10897409697.0  L11317809039.365L12410523051.2  L12992106945.1  L13176305223.2  L13458225234.6  L13686150329.2  L13818365896.6  L1387720423.0   L14163031713.79 L14301694619.2  L14447004729.2  L1540615640.71  L15584676755.7  L15756324293.71 L15773204779.2  L15822417165.1  L1594761485.1   L16326130581.30 L16354919745.1  L16722680008.298L1685717371.0   L16916955281.2  L17652900291.2  L17699354692.3  L18689686129.3  L18929205602.298L19515924110.2  L19722042104.8  L19914337963.2  L19979755003.71 L20103572523.2  L20285715777.1  L20572545618.6  L21218866939.2  L21221417243.2  L21593730587.2  L21866712442.1  L22251516267.2  L22324277402.79 L22941438733.1  L22982591434.2  L2354892431.365 L23723668098.3  L23842088513.1  L2414702162.6   L24518054482.6  L24574117036.6  L24574117036.8  L24619077828.3  L24709387730.6  L25056532498.364L25185999684.3  L25190023391.333L25190023391.343L25190023391.366L26171659739.2  L26640950725.7  L26833704747.2  L2732057889.7   L27386516966.1  L28043791304.6  L28632618922.2  L29604608213.0  L29765677068.344L29999895745.1  L30138332444.3  L30354668070.6  L30354668070.75 L30584639809.1  L30585657693.25 L30761295553.1  L31145622673.2  L31314021185.7  L31620401107.7  L32454903270.1  L32516831197.3  L3276082884.3   L32781056652.1  L33427819358.6  L33948564779.2  L33985112333.1  L33993909768.8  L340779473.8    L34319762369.1  L34783991938.3  L3482447776.75  L35157079496.6  L35330472652.0  L35539854113.0  L35627916443.2  L35655538583.72 L35790045369.2  L36463206329.4  L37877116203.2  L38068447915.2  L38235734261.1  L38259954321.2  L38552102098.6  L38925967467.333L38925967467.343L38963771065.2  L39118478162.6  L39220054468.3  L39280637297.0  L39379299611.2  L39768386075.2  L40281191306.3  L4037478596.3   L4074078069.7   L41409160545.3  L41628182337.1  L41663468825.299L41663468825.365L41898327682.3  L43166046660.3  L43583719247.0  L44069007811.14 L44166924249.3  L44168158952.3  L44168742175.3  L44423163457.1  L45013537572.8  L45107553834.79 L45184559169.1  L46039761874.6  L46217367496.6  L46815551714.298L46882717723.2  L48743046465.1  L48904736427.7  L491029745.9    L49146192608.6  L49146192608.8  L49304025233.2  L49658560763.6  L50007149753.2  L50051061275.2  L50280382404.3  L50440147739.2  L50491739569.79 L50790846049.71 L5114586667.2   L51508673957.0  L51911277483.2  L52160193805.1  L52493923371.2  L52941874306.3  L52971154002.6  L53331700168.6  L53343989586.6  L53537418962.6  L53997053467.2  L54174754203.2  L54793161284.3  L55081356057.6  L55085943702.3  L5565789826.3   L56418360977.2  L5683690049.1   L57122009785.2  L57200105028.3  L57359870875.2  L57616316680.82 L57670068163.5  L57698627611.2  L58790269211.75 L58800853013.79 L59308636045.10 L59314955108.3  L59415125163.2  L5955738343.6   L59706101938.9  L59980013761.1  L60056205954.3  L6040472874.2   L60458748242.6  L60754583113.0  L61167093839.3  L61323929028.3  L61366595865.299L61366595865.333L61366595865.343L61366595865.365L61366595865.366L6213972851.79  L6215971453.7   L6303995537.7   L63536403905.1  L639424795.2    L64140572076.9  L64375276488.6  L64686745924.3  L6538498514.6   L65607387291.2  L66330248491.2  L666322777.7    L66719203371.2  L66912895403.2  L6727734098.6   L67301973408.3  L67461776529.2  L6753817986.75  L67771364050.6  L6798276507.2   L67993121360.5  L68182231225.2  L6899380056.1   L6906665613.1   L7382465640.1   L7738195705.2   L8793638983.75  L881835912.0    L9080482849.71  O13009973273.380O13959695001.380O14478469379.380O1478932887.380 O14969417505.380O15264828477.380O15939174659.380O16212419179.380O17025509154.379O19498521113.380O20458828221.380O20605776350.380O20681810237.380O21324340889.380O23306835203.380O24508162713.380O26157569982.380O28722675819.380O2882670525.380 O29643854873.380O30318881262.380O31973244675.380O32052374275.380O33333321113.380O33712885764.380O34897061144.380O35068841533.380O3580511549.380 O37526612587.380O38132941721.380O39730653885.380O40736321802.380O40784667709.380O43849221576.380O45345422653.380O49655548313.380O50702749291.380O51856258329.380O52246153405.380O5257382681.380 O53955565629.380O53998903748.380O55959153853.380O56414250091.380O57396949401.380O58569456404.379O58689704564.378O59625545032.380O59806508861.380O59920328473.380O61727260126.380O61808263577.380O6525267203.380 O65263443097.380O66180433341.380O7499966059.380 O862016573.380  P10189124890.380P10397234330.380P10761154970.380P14304577628.307P14304577628.308P14461423358.342P14461423358.359P14461423358.382P14847612824.340P15572342635.381P15572342635.382P16923509334.307P16923509334.308P17664172804.308P17664172804.343P17664172804.360P17664172804.381P17685194778.380P18674477615.380P19717829785.380P21207000028.307P21207000028.308P21212047013.379P21608672476.307P21608672476.308P22134471192.340P22257803915.308P22257803915.343P22257803915.360P22257803915.381P22971318541.307P22971318541.308P23737819868.380P24620646554.380P25197005594.380P26033826406.340P28627113325.307P28627113325.308P29455900312.340P30296385645.340P31146933846.307P31146933846.308P31318230304.379P3282902682.380 P33010176920.340P33143934054.340P33377767064.340P33432028479.380P34508873193.340P34789755100.380P35626081884.307P35626081884.308P36465823719.380P38261788758.307P38261788758.308P39214291354.380P39390572508.307P39390572508.308P39771269340.307P39771269340.308P3985014296.340 P4031715482.380 P41419126079.380P41905139420.380P428624152.340  P43151886746.380P44164039966.307P44164039966.308P44179613286.340P46851611017.340P46884029148.307P46884029148.308P47601162904.340P47809338136.340P48892166346.378P49296947798.307P49296947798.308P50057614556.307P50057614556.308P50266222490.380P50442506716.307P50442506716.308P51293915238.340P51365709848.340P52940305628.380P53998888156.307P53998888156.308P54190221148.307P54190221148.308P54465921638.340P54777960986.380P55088569288.380P55093921144.380P5558970076.380 P56407612502.307P56407612502.308P57202722330.380P57344928092.307P57344928092.308P57674246562.380P57713046236.307P57713046236.308P58653617304.340P60050434780.380P61334943130.380P62211563928.340P62785740056.340P64680982810.380P653319132.307  P653319132.308  P65606077020.307P65606077020.308P65767921304.340P662112568.380  P67476194902.307P67476194902.308P6809023836.307 P6809023836.308 P7750690063.342 P7750690063.359 P7750690063.382 P7866543718.340 P8497851288.340 Q12602634320.381Q13117850455.340Q14315260792.305Q14315260792.357Q1432905896.339 Q1432905896.356 Q15020562984.377Q15072116113.305Q15072116113.357Q15457532689.340Q15457532689.357Q15766547626.380Q1697827660.306 Q1697827660.341 Q1697827660.358 Q1697827660.379 Q17480090062.305Q17480090062.340Q17480090062.357Q19144021196.377Q19144120944.304Q19146107084.356Q19546638454.340Q20011087272.377Q20060868089.339Q20060868089.356Q23957120639.307Q23957120639.308Q24655294256.342Q24655294256.359Q24655294256.382Q24657470768.341Q24657470768.358Q24657470768.381Q25952160488.306Q25952160488.307Q26030088805.381Q26030354684.342Q26030354684.343Q26030354684.359Q26030354684.360Q26030354684.381Q26030354684.382Q26479516034.304Q2676383091.342 Q27478886904.340Q27478886904.357Q28096287912.339Q28154688736.378Q28465177121.304Q28465177121.305Q29310291280.308Q29310291280.343Q29310291280.360Q29310291280.381Q29312239440.307Q29312239440.342Q29312239440.359Q29312239440.380Q29516740158.304Q30602209460.304Q30602569224.338Q30602569224.355Q30602569224.377Q30604712456.378Q3260556108.307 Q3260556108.308 Q32770127343.380Q32770127343.381Q33839963198.303Q34511873441.380Q34671223321.377Q34671586469.304Q34964432579.381Q34964698202.342Q34964698202.343Q34964698202.359Q34964698202.360Q34964698202.381Q34964698202.382Q36099344095.380Q37546564045.307Q37546564045.308Q37782350525.378Q3853036341.339 Q3853036341.356 Q38827724537.380Q38829999353.381Q39180574961.307Q39180574961.308Q41021611741.340Q41021611741.357Q41021645928.339Q41021645928.356Q41390230097.339Q41390230097.356Q42439171022.340Q42439184438.381Q42439443119.307Q42439443119.308Q42439443119.342Q42439443119.343Q42439443119.359Q42439443119.360Q42439443119.381Q42439443119.382Q42639691166.303Q43225777045.378Q43535656680.359Q43535656680.382Q4376401896.380 Q4376401896.381 Q43844324271.357Q44587282695.380Q45741809296.307Q45741809296.308Q47048715101.305Q47048715101.357Q47048829789.356Q47050807777.304Q47050970973.377Q48099074825.380Q48117823211.342Q48117823211.359Q48117823211.382Q48118080626.380Q48360064815.380Q49413559012.341Q49413559012.358Q49413559012.381Q49415575780.342Q49415575780.359Q49415575780.382Q49698585326.340Q49698585326.357Q49698585326.380Q49746415830.307Q49746415830.308Q49855256623.340Q49855256623.357Q50043152237.380Q519278494.304  Q52017694517.339Q52556335576.378Q5265442331.305 Q5265442331.306 Q52932718501.342Q52932718501.359Q52932718501.382Q53579323758.340Q53799279550.304Q55415036769.307Q55415036769.308Q55705303732.304Q55705465864.377Q56843884402.342Q57390260742.380Q57618602681.307Q57618602681.308Q57618602681.342Q57618602681.343Q57618602681.359Q57618602681.360Q57618602681.381Q57618602681.382Q58024421813.377Q58694915926.339Q58694915926.356Q58694915926.379Q58746001061.304Q58746361881.338Q58746361881.355Q58746361881.377Q58748478489.378Q59865321072.342Q59865321072.343Q59865321072.359Q59865321072.360Q59865321072.381Q59865321072.382Q59865586921.381Q60135608610.308Q60135608610.343Q60135608610.360Q60137823010.307Q60137823010.342Q60137823010.359Q60187641253.377Q60191312605.306Q60191312605.307Q60668057790.304Q60701389858.304Q62217140090.342Q62217140090.359Q62217140090.382Q63211573790.304Q64051781173.377Q64908775830.342Q64908775830.359Q64908775830.382Q64932735960.304Q64934943076.356Q65226068290.377Q65227746626.378Q6530087198.304 Q67038705740.340Q67038978349.307Q67038978349.308Q67113017815.377Q68281680193.340Q8699115497.307 Q8699115497.308 Q8699115497.342 Q8699115497.343 Q8699115497.359 Q8699115497.360 Q8699115497.381 Q8699115497.382 Q8699372912.381 Q9356559649.360 Q9644567153.381 Q9644581257.340 Q9788364536.378 00000100201?02L03d05>06\08409N0:l0<:0<;0=S0>k0@E0Ac0Ad0Ae0CC0EC0GC0GD0GE0HR0I`0KA0Lb0NC0Of0QI0S00TW0Uo0WG0X_0Z90\G0^U0_^0`l0bA0cX0e30f@0gU0hj0jA0kZ0lc0n80oO10j12?13T14k16D17Y1901:K1;`1=71>R1?_1@l1B91CQ1Dm1F:1GO1Hf1JA1KJ1LS1Mh1O?1PZ1Qc1S81TM1Ud1W=1XR1Yi1[D1\Y1^01_K1`X1am1cB1dY1f21g?1hX1im1kF1l]1n81oQ20h22523>24Z26:27C28X29m2;D2<]2>22?I2@d2B92CP2Dk2F@2GW2I22J?2KH2LU2Mb2O72PL2Qc2S<2S=2TR2Ui2WD2XQ2Y^2[32\J2]e2^n2`;2aP2bg2dB2eW2fn2hI2i^2k52lP2m]2nj30?31T32k34D34V35535635736b36c36d38338438938A38B38C38D38E3:83:93::3:P3:Q3;k3;l3<03<43=X3=]3@43@53@63@73@83@93A@3AA3AB3AC3BV3BW3B\3B]3B^3B_3B`3Bd3Be3DR3DV3DW3Ef3Eg3El3Em3En3Eo3F03F13F23GD3GE3HN3IY3Jh3K13KJ3KK3KW3K[3K\3K]3K^3MB3MG3MS3Mh3NN3NS3Ok3P03P13P23P33P73PB3PC3PF3PG3PH3PL3P^3Q43Q93Q:3RL3RM3RN3RO3RP3Sh3Si3Sj3Sk3Sl3T03T13T23U93VB3VC3VD3VE3VF3VG3VH3VQ3VR3Vj3Vk3W03X93YH3YI3YJ3YK3Yi3Yj3Yk3Yl3Z13ZY3\B3\G3\H3\I3^`3^a3^f3^g3_63_73_83_93_:3_;3_<3_=3_>3`R3aR3aS3aT3aU3aY3aZ3a[3a\3a]3a^3a_3a`3aa3ab3ac3ad3ae3af3ak3al3am3an3d@3dA3dB3el3gV3gj3h23h33h43hC3hH3hI3hJ3hK3hL3hX3hY3ib3jk3l63mE3nT3oe40>40X40]40^40i40j40k40l40m40n40o41041141241>41?41\41]41^41l41m42142642:42;44A44B44[44\44]44^44_44`44a44b44c44d44e44f44g44h44i44j44k44l44m44n44o45045145245345445545645745845945:45;45<45=45>45?45@45A45B45C45D45E45F45G45H45I45J45K45L45M45N45O45P45Q45R45S45T46g48:49M4;L4=K4?E4AA4CA4E14F`4HQ4JK4LI4NH4PG4RH4TK4U^4W14XK4ZJ4\I4\J4^I4`H4b84co4ef4g_4iZ4kY4mX4nf50951L53755156o58_59n5;h5=f5?55@H5B85Cc5ES5G;5Hf5J45L35N25OA5Q;5S95TL5VK5XJ5ZI5\H5^85_K5`Y5ag5cW5dj5fi5hl5jW5lG5nF60E62563e65U67O69M6;L6=K6>^6@]6B\6DG6F76GE6ID6KC6MB6OA6Q26RE6SU6UE6VS6XM6ZK6[^6]]6_\6_]6a56bQ6dA6eO6fb6hR6jB6kU6mT6oS71R73Q75A78O7:I7<G7>F7@E7B77Ck7Ec7GN7I>7JF7Kh7MF7Ni7P57QA7RQ7SS7TU7UW7VY7Wh7Y77ZF7[U7\h7^27_<7`F7aL7bN7cP7dc7f37g57h77h87h97iF7jU7kh7m57nD7oW81A82o84;85R86m88F89c8;B8<_8>:8?=8@[8B>8CJ8CK8DU8E_8G08HA8IT8Ji8L:8MK8N^8P38QN8RL8SJ8TH8UJ8VL8VM8VN8WR8XV8Z18Z28[48\28]\8_Q8aJ8cA8e<8g98i48i58k48m38nW90=91c93894M96J98K99M9:O9;Q9<S9=U9>W9?`9@m9BI9Ci9EA9F]9H79IU9K59LS9N=9OK9OL9OM9PQ9QU9QV9QW9QX9QY9R[9S]9T_9Ua9Vg9Vh9X]9ZT9\O9^99_I9`V9ae9c89dE9eT9fg9gn9i59j@9kf9mP9mQ9mR9mS9o=:0c:1i:34:4?:4@:4A:4B:5D:6_:87:9S::Q:;S:;T:<c:?7:AK:Bd:D=:EX:G3:HP:Io:KY:L]:Ma:Ni:Og:Pe:Qc:Re:Sg:Sh:Si:Sj:Sk:Sl:Sm:Sn:U?:VP:Wc:Y4:ZE:[X:\^:^W:`T:ao:cY:cZ:c[:c\:eF:g0:g1:g2:g3:h5:i7:j=:kC:lm:nW;0P;2M;3S;4m;6[;8M;:;;;m;=];?Q;AG;C;;D^;Ei;Fn;Go;H0FFS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL1x2HxFS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stFFS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw2p13HTc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw2p13HTc2RL2HB5Ha_st5Hl_stFFS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL1x2HxS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL1x2HxS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3HRL4NAPF2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPF3SRL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPBS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B23DXB2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B23DXB2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB72Lw2p12RL1N2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B23DXB2FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B23DXB2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3HRL4NAPC2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPC3SRL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPHS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPFS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL4NAPCS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1Q4blen2Lw2p13HRLS1Q4blen3BUF2bs2B32Lw2p12RL3HRLFFS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03B302FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB71N2RL3HRL2N0FSS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLFS3CRTS2lo3sp1FFFSS1R2sp3CRT1Q4blen2bs4CRT02FB3sp13SPR3ACV2F04SP1R2Lw2p11N2RL3HRL2N13NS14STKc5STKc13BUF2lo2B35CRTLO3SPH5BUFLO2F14SLOuFFS2sp3CRT2bs2FB3sp13SP1FS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1RFS2FBS2FBS1R3HIA4PHIk4FFRk5PHIcf5FFRcf4PHIj4FFRj1h1Q4blen1d2hc2Lw2p13BV03BF02RL3HRL2D02BV2BF1H2H02H12H22H32H4S3CRTS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw2p13Hq13Hq23LWRSFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7FFFS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1RFS3CRTFFFFS2FBFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B34CRT05CRTLO4SLOS4SLOL2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO4SP1R2Lw2p12RL3HRLS2FBFS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLFS3CRTFFFFFFS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB71N2RLFS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL1NS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLS4blen2B2S1Q4blen3BAM2Lw2p12RL3HRLFS1Q2Lw2p12RLS2FBFFSS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71N2RL3HRL2N02N1S3CRTS2LB4blen2DMS1Q4blen2Lw2p12RL3HRLS2sp3CRT1Q4blen2bs2FB3sp12Lw2p12RL3HRLS3CRTS1R3HIA4PHIj4FFRj4CNTj1h1Q4blen1d2hc2Lw2p13BV03BF03hq22RL3HRL2D03HV24HFR22Lq3HLq1H2H02H1S3CRTFFFS2FBS2sp2lo3sp1FS1NFFS2FBS1Q4blen2Lw2p13HRLS1Q4blen3BAM2Lw2p13HRLS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R2Lw2p12RL3HRLFSSFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFFS2loFFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB71NFFFSFFS1R3HIA1hFS1Q4blen2Lw2p12RL3HRL2EWFS3CRTS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLFFSS1R1Q2lo3LOS3ALO2Lw2p12RL1N2N1FFFS3CRTS4C24k4C24c5C24c15C24k02LB4blen5BUD242DPS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2Lw2p11N2RL3HRL2N1S3CRTFFS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B12B22B32B54CRT03SPH2FB3sp15BUFLO3SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw2p13Hq13Hq23LWRFS3CRTFS1Q2Lw2p11N3LWRFFFFFFFFS2sp3CRT1Q4blen3BUF2bs2B12B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw2p11N2RL3HRL4NAPBS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT03LOS2FB3sp13SPR2F04SLOu4SP1RFSFS2FBFFFFFFFFFFFFFS3CRTFFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R2Lw2p11N2RL3HRL2N12N21a2Da4DLOxFFS1R3NS14STKc5STKc52sp3CRT1Q4blen3BUF2lo2bs2B12B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R2Lw2p12RL3HRLS1R3NS14STKc5STKc22sp3CRT1Q4blen3BUF2lo2bs2B12B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R2Lw2p12RL3HRLS1Q2Lw2p11N2RL2N02KnS1N2N01EFFS1Q2Lw2p11N3Hq1S3CRTFFFSS2LB4blen2DPFS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL1NS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RLS2sp3CRT1Q4blen3BUF2bs2B12B34CRT03DXB3B302FB3sp13APC3SPR2F03APB4SP1R2Lw2p12RL3HRLS1Q4blen3BAM2Lw2p12RL3HRLS1Q4blen2Lw2p13Hq13Hq23LWRS3CRTFS1Q2Lw2p11NFFFFFFFFFS2LB4blen2DPFS2sp3CRT1Q2bs2FB3sp12Lw2p12RLFFS1Q2Lw2p11N2RLFS2FBS3CRTS2FBFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2Da5SBND0SS2sp3CRT2lo2bs2FB3sp13SP1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B33DXB2FB3APC3APB4LFB36LFB5126LFB5114LFB72Lw2p12RL3HRL3SRL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B33DXB2FB3APC3APB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3HRL3SRL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22B32FB3sp15BUFLO4LFB36LFB5126LFB5114LFB72Lw2p12RL3HRL3SRLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL3NLOS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3NLOS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp15BUFLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP15BUFLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP15BUFLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3NLOS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3NLOS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stFS2LF2sp1Q4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3HIA3NS14STKc3NA15STKc21h2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B12B22B35CRTLO3DXB3TOP3LOS2FB3ALO2F14FBLO3APB4SLOu4LFB36LFB5126LFB5114LFB72hc2Lw2p11N3hq23HSc5HTOPc2RL3HRL3HS22N14NAPB4NAPF4NAPH3NLO4NAPC3SRLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL3HRLS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72hc2Lw2p13HSc5HTOPc2RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2N0S2LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R2LF1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF3CRT1Q4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF3CRT1Q4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF3CRT1Q4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLFFS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL1N2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL1c2HcS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2N0S2LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLFS2LF1Q4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF1Q4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLFFS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RLS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLFS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw2p11N2RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R2LF1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R2LF1Q4blen3BUF3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R2LF1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF3CRT1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_st3sp1S1R2LF1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF3CRT1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF3CRT1Q4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF3CRT1Q4blen3BUF3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF1Q4blen3BUF3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HBFFS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RLFFFFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLFS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL1N2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stFFFS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stS2LF1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_stFFFS2LF1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLS2LF2sp1Q4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLFS2LF3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw2p14SBND2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_st3NS14STKc3NA15STKc25CRTLO3LOS3sp13SP13ALO2F14FBLO4SLOu4SBNDS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R2LF2sp3CRT1Q4blen3BUF2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF1Q4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw2p12RL2HBS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLFFFFFFFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p11N2RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLFFFS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLFFFS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3NS14STKc3NA15STKc22LF2sp1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT1Q4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw2p12RL2HB5Ha_st5Hl_stS2LF3CRT1Q4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw2p12RLS1R3HIA1h2LF2sp1Q4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc2Lw2p13HSc5HTOPc2RLS1R3HIA1h2LF2sp1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p11N5HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p11N5HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT1Q4blen3BUF3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RL2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen3BUF3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p11N2RL5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1Q4blen3BUF3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw2p15HTOPc2RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen3BUF2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw2p12RLS2LF1Q4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw2p12RLF". (* [comment removed for export] *)
  Lemma S_COPY : forall (hc : HST asegs R HIA) (mm : mem) (lv Lw : word) (p1 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k64 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s11v x28 x29 x30 x31 : word),
    cinv [] mm hc FSHB lv Lw p1 a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 k40 k48 (Z_to_bv 64 0) k64 (Z_to_bv 64 (FB + 32))
         (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 1) ->
    chz mm -> bytes_at asegs mm BUF bs -> aobj asegs AL (hcs asegs R HIA hc) mm BUF n ->
    Q + 2 <= p1 -> p1 + bv_unsigned Lw <= Q + blen ->
    havol asegs R HIA hc <= havol asegs R HIA h -> hfr asegs R HIA hc <= hfr asegs R HIA h ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 CRT) (Z_to_bv 64 FB) (Z_to_bv 64 Q) (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (FB + 128))
               s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a9040) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH HBUF OBUF Hq1 Hq2 BV0 BF0. unfold chz in CH.
    open_cinv_mu INV hc. ch_open CH.
    pose proof (bv_unsigned_in_range 64 Lw) as LWR. unfold bv_modulus in LWR. cbn [Z.pow Z.of_N Pos.pow] in LWR.
    set (RL := p1 + bv_unsigned Lw - Q) in *.
    assert (HRL : 2 <= RL <= blen) by (subst RL; clear - LWR Hq1 Hq2; lia).
    (* [comment removed for export] *)
    do 19 zstep.
    idtac "COPY-PRE".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    fold RL in K0 |- *.
    si_mu.
    replace (Z_to_bv 64 429840 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_calloc R)) by (rewrite ACAL; reflexivity).
    lazymatch goal with PRx : presW _ _ _ hc _ _ _ _ _ _ mg, SVx : rw_cells _ mg (bv_unsigned sp + -104) _ |- _ => pose proof (uwc_callee hc mg PRx HSc SVx) as UWF end.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (BP : havol asegs R HIA hc + (2 * (1 * RL) + AVOL_CALL) <= AVOL_MAX /\ hfr asegs R HIA hc + fr_charge (d + 1) <= FR_MAX).
    { pose proof BUDV as BV. pose proof BUDF as BF. unfold PHIc, FFRc, KVc, KFc, X509_SIG_ALG_PHI, X509_SIG_ALG_FFR, fr_charge, AVOL_CALL in *.
      pose proof (PHIk0 blen B2). pose proof (FFRk0 blen (d + 1) B2). pose proof (PHIj0 blen B2). pose proof (FFRj0 blen d B2).
      pose proof CNTc0 as C0. pose proof (PHIcf0 _ C0). pose proof (FFRcf0 _ 0 C0). clear - BV BF BV0 BF0 HRL D0 H H0 H1 H2 H3 H4. lia. }
    flat constr:(BP) 2%nat. flclear BP. intros BPV BPF.
    assert (BINc : In (BUF, n) (([] ++ LB) ++ fdata LF')) by (apply in_app_iff; left; exact BIN).
    idtac "COPY-CALLOC".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := hc) (LB := [] ++ LB) (LF := LF') (cnt := 1) (sz := RL) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HSc;
        first [ exact HK1 | exact LOS | exact TPV | exact UWF | exact BPV | exact BPF | eassumption | reflexivity
              | lazymatch goal with
                | |- _ <= htop _ _ _ _ => rewrite HTc; xl
                | |- _ < AMAX => clear - HRL BAM; lia
                | |- win24 _ = true -> _ => intros _; cbn [app]; pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP; clear - BUD24 C24c1 C24k0 DP; lia
                | |- _ => xl HRL
                end
              | match goal with |- ?g => idtac "CALLOC-LEFT:" g end ]. }
    cbv beta. intros ms2 mo2x (mo1 & [HK1 MF1] & PO).
    flat constr:(PO) 4%nat. flclear PO. intros ms2' mo2 E2 PO. injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    flat constr:(PO) 31%nat. flclear PO. intros u0 u1 u2 r ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 Ems2 MI2 ST2 MF2 WM2 HP2 hq2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 CASES.
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xa908c)) with (Z_to_bv 64 0xa908c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite ?Z.mul_1_l in CASES, HV2.
    idtac "COPY-CALLOC-POST".
    assert (SIP2 : si_P SI m2).
    { lazymatch goal with SIx : si_P SI mg |- _ => eapply (si_heap_presx asegs L SI); [exact SIx| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| intros xx Hxx; exact I] end. }
    pres_call HP2.
    lazymatch goal with STx : stk _ mg lo sp1, MIx : mem_inv _ mg, SIx : si_P SI mg |- _ => clear STx MIx SIx end.
    lazymatch goal with HHx : HM _ _ _ hc _ _ mg |- _ => clear HHx end.
    presA_transport HP2.
    clear HP2.
    apply (aevtA_enter asegs (KF asegs R HIA hq2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    switch_hm hc hq2 HCS2 HT2 HS2 HF2.
    assert (B12 : forall Lq, Z.of_nat (length Lq) <= 1 -> BUD1 hq2 Lq 0).
    { intros Lq HLq. unfold BUD. pose proof (PHIj0 0 ltac:(clear; lia)). pose proof (FFRj0 0 d ltac:(clear; lia)). pose proof (CNTj0 0 ltac:(clear; lia)).
      unfold AVOL_CALL, fr_charge in *. clear - HV2 HFR2 BV0 BF0 HRL D0 HLq H H0 H1. lia. }
    destruct CASES as [[Er HH2] | (N & Er & NAL & NFR & NSTK & HH2 & NZ)]; subst r.
    - idtac "COPY-NULL".
      mu_reset hq2.
      (* [comment removed for export] *)
      do 12 zstep.
      si_mu.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => fold_cinv INV2 mx hq2 (@nil blk) FSHB; ch_close mx;
        pose proof (owns_rawnull mx ([] ++ LB) RL) as OWn end.
      eapply exit_walk with (Lc := @nil blk) (r := -10368) (rawlen := RL) (rawp := 0);
        first [ exact INV2 | exact CH | exact OWn | reflexivity
              | lazymatch goal with
                | |- Permutation _ _ => cbn; apply Permutation_refl
                | |- BUDX _ _ => apply BUDE_X; eapply BUD1_E; [apply B12; cbn; clear; lia| clear - B2; lia]
                | |- cnt24 _ <= _ => cbn [app]; pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP; clear - DP; lia
                | |- _ => clear - HRL BAM; unfold AMAX in *; lia
                end
              | match goal with |- ?g => idtac "COPY-NULL-LEFT:" g end ].
    - idtac "COPY-OK".
      change ((N, RL) :: [] ++ LB) with ([(N, RL)] ++ LB) in HH2.
      flat constr:(NFR) 4%nat. intros N0 N1 N2 N3.
      assert (FRN0 : fresh_apart R LB LF N RL).
      { split; [exact N0|]. split; [exact N1|]. split; [exact N2|]. intros B j Hb. apply (N3 B j). cbn [app].
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply (fdata_cons_sub (B, j) [] FB 512 LF); exact Hb]. }
      assert (NAPB : N + RL <= BUF \/ BUF + n <= N) by (apply (N3 BUF n); cbn [app]; apply in_app_iff; left; exact BIN).
      assert (NAPF : N + RL <= FB + 32 \/ FB + 32 + 472 <= N).
      { lazymatch goal with INDx : In (FB + 32, 472) _ |- _ => apply (N3 (FB + 32) 472); exact INDx end. }
      assert (NAPH : N + RL <= FB \/ FB + 24 <= N).
      { lazymatch goal with INHx : In (FB, 24) _ |- _ => apply (N3 FB 24); exact INHx end. }
      assert (NLO : N + RL <= lo) by (clear - N1 ALO LOS; lia).
      assert (NAPC : N + RL <= CRT \/ CRT + 744 <= N).
      { eapply (fresh_apart_client R LB LF lo CRT 744 N RL FRN0 (client_range_of_w L _ _ _ _ _ CWX)); [clear; lia| clear - HRL; lia| xl]. }
      clear_client_facts. client_facts hq2.
      mu_reset hq2.
      (* [comment removed for export] *)
      do 6 zstep.
      zstep. if_cases Kn; zify_cond Kn.
      { exfalso. clear - Kn N0 N1 ACV. rewrite ?Z.mod_small in Kn by lia. lia. }
      clear Kn.
      (* [comment removed for export] *)
      do 6 zstep.
      idtac "COPY-MEMCPY".
      replace (Z_to_bv 64 424008) with (Z_to_bv 64 (arl_amemcpy R)) by (rewrite AMC; reflexivity).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mk end.
      si_mu.
      destruct (bslice mk BUF bs Q RL HBUF B1 ltac:(clear - HRL; lia) ltac:(clear - HRL B3; lia)) as [SRB SRL].
      apply (u8arr_of_rw_cells asegs) in NZ.
      assert (RINk : In (N, RL) ([(N, RL)] ++ LB)) by (left; reflexivity).
      lazymatch goal with HHx : HM _ _ _ hq2 _ _ mk |- _ => pose proof (hm_aobj_block asegs R HIA hq2 _ _ mk N RL HHx RINk) as ODST end.
      repeat match goal with H : munch WMU _ _ |- _ => clear H end.
      pose proof (artA_amemcpy asegs R HIA (arl_amemcpy R)) as SPM.
      lazymatch type of SRB with bytes_at _ _ _ ?ssz =>
      lazymatch goal with HHx : HM _ _ _ hq2 _ _ mk, SIx : si_P SI mk |- _ =>
      acallxA_sp_k sp1
        (eapply SPM with (h := hq2) (LB := [(N, RL)] ++ LB) (LF := LF') (DST := N) (SRC := Q) (n := RL) (lo := lo) (ss := ssz) (ds := repeat (Z_to_bv 8 0) (Z.to_nat RL)); clear SPM;
           rewrite ?(unsigned_lit sp1) by exact SP1R;
           first [ exact HHx | exact NZ | exact SRB | exact SRL | exact ODST | exact LOS | reflexivity
                 | lazymatch goal with
                   | |- _ = arl_amemcpy R \/ _ => left; reflexivity
                   | |- Z.of_nat (length (repeat _ _)) = RL => rewrite repeat_length; apply Z2Nat.id; clear - HRL; lia
                   | |- aobj _ _ _ _ Q RL => eapply aobj_sub; [exact OBUF| exact B1| clear - HRL B3; lia]
                   | |- stk _ _ lo _ => eassumption
                   | |- mem_inv _ _ => eassumption
                   | |- crange _ lo _ => eassumption
                   | |- client_wrange _ _ _ _ N RL => eapply client_wrange_block; [apply in_app_iff; left; exact RINk| clear; lia| clear; lia]
                   | |- _ <= htop _ _ _ _ => rewrite HTc; xl
                   | |- _ => xl HRL N0 N1 NAPB
                   end
                 | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ])
        (fun MUc => let SIn := fresh "SIPk" in
                    assert (SIn : si_P SI _) by (eapply (si_munch_offdata L SI); [exact SIx| exact MUc|];
                      let a := fresh "a" in let Da := fresh "Da" in let Wa := fresh "Wa" in intros a Da Wa; cbn [outside];
                      pose proof (art_data_lo asegs R HIA) as DLOx; xl Da DLOx N2 N0 N1 HRL))
      end end.
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MEMCPY-LEFT:" g end.
      match goal with H : ?x = Z_to_bv 64 N |- _ => subst x end.
      match goal with H : u8arr _ _ N _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rename H into RAWC end.
      mu_reset hq2.
      (* [comment removed for export] *)
      do 16 zstep.
      idtac "COPY-TAIL".
      si_mu.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => fold_cinv INV2 mx hq2 [(N, RL)] FSHB; ch_close mx end.
      lazymatch goal with RC : rw_cells _ ?mx N [CB ?k ?rj] |- _ =>
        assert (OWn : owns asegs PK mx ([(N, RL)] ++ LB) CRT (Z_to_bv 64 1) RL N 0 [] 0 [] 0 0 [] ext_own_zero 0 rj)
          by (pose proof (owns_raw mx ([(N, RL)] ++ LB) (Z_to_bv 64 1) (Z.of_nat k) N rj N0) as OWk; rewrite Nat2Z.id in OWk; rewrite SRL in OWk;
              apply OWk; [left; reflexivity| clear - HRL; lia| exact RC]) end.
      assert (PERMn : Permutation [(N, RL)] (crt_blocks (f_of (Z_to_bv 64 1) RL N 0 [] 0 [] 0 0 [] ext_own_zero 0))).
      { rewrite crt_blocks_f_of. change (ext_blocks ext_own_zero) with (@nil blk). unfold oblk. change (0 =? 0) with true. cbn [app CrtStmts.SNAME map].
        destruct (Z.eqb_spec N 0) as [E|_]; [exfalso; clear - E N0; lia| apply Permutation_refl]. }
      assert (C24n : cnt24 ([(N, RL)] ++ LB) <= cnt24 LB + blen / 5889).
      { cbn [app]. rewrite cnt24_cons. cbn [snd]. pose proof (Z.div_pos blen 5889 B2 ltac:(clear; lia)) as DP.
        destruct (win24 RL) eqn:EW; [| clear - DP; lia].
        unfold win24 in EW. apply andb_true_iff in EW. flat constr:(EW) 2%nat. flclear EW. intros EW _. apply Z.leb_le in EW.
        pose proof (Z.div_le_mono 5889 blen 5889 ltac:(clear; lia) ltac:(clear - EW HRL; lia)) as DM. rewrite Z.div_same in DM by (clear; lia). clear - DM. lia. }
      eapply S_TBS with (Lc := [(N, RL)]) (rawp := N) (rawlen := RL) (END2 := N + RL);
        first [ exact INV2 | exact CH | exact OWn | exact PERMn | exact C24n | (right; reflexivity) | (apply B12; cbn; clear; lia) | exact N0
              | (clear - HRL BAM LWR Hq1; subst RL; unfold AMAX in *; lia) | match goal with |- ?g => idtac "COPY-TBS-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac ms_call Hc DSTz :=
    apply (rw_cells_CB_of asegs) in Hc; [| cbn; clear; lia]; cbn [cells_size csize Nat.add] in Hc; apply (u8arr_of_rw_cells asegs) in Hc;
    replace (Z_to_bv 64 425188) with (Z_to_bv 64 (arl_amemset R)) by (rewrite AMS; reflexivity);
    let SPMS := fresh "SPMS" in let ODST := fresh "ODST" in
    pose proof (artA_amemset asegs R HIA (arl_amemset R)) as SPMS;
    lazymatch goal with FSHx : rw_cells _ ?mx (Z.shiftr FB 3 + al_sb AL) _ |- _ (MS _ _ _ _ _ ?mx _) => frame_aobj FSHx DSTz 3%nat as ODST;
    lazymatch goal with HHx : HM _ _ _ ?hcx ?Lh _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPMS with (h := hcx) (LB := Lh) (LF := LF') (DST := DSTz) (v := 0) (n := 24) (lo := lo); clear SPMS;
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact HHx | exact Hc | exact ODST | exact LOS | reflexivity
               | lazymatch goal with
                 | |- _ = arl_amemset R \/ _ => left; reflexivity
                 | |- stk _ _ lo _ => eassumption
                 | |- mem_inv _ _ => eassumption
                 | |- crange _ lo _ => eassumption
                 | |- client_wrange _ _ _ _ _ _ => lazymatch goal with INDx : In (FB + 32, 472) _ |- _ => eapply client_wrange_block; [exact INDx| clear; lia| clear; lia] end
                 | |- _ <= htop _ _ _ _ => lazymatch goal with HTx : htop asegs R HIA hcx = _ |- _ => rewrite HTx; xl end
                 | |- _ => xl
                 end
               | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]) end end;
    try clear ODST;
    lazymatch goal with Hu : u8arr _ _ DSTz _ |- _ =>
      apply (rw_cells_of_u8arr asegs) in Hu; rewrite repeat_length in Hu; change (Z.to_nat 24) with 24%nat in Hu;
      eapply (rw_cells_reshape asegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in Hu; [| cbn; repeat split; exact I| vm_compute; reflexivity] end.

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1k d; try lx_pin1 WS; try lx_pin1 slo; try lx_pin1k lo; try lx_pin1k m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1k LF; try lx_pin1k LB; try lx_pin1 CNTj; try lx_pin1 FFRj; try lx_pin1 PHIj; try lx_pin1 FFRcf; try lx_pin1 PHIcf; try lx_pin1 CNTk; try lx_pin1 FFRk; try lx_pin1 PHIk; try lx_pin1k SI; try lx_pin1 PK; try lx_pin1k NSH0; try lx_pin1 SM3; try lx_pin1k UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0>J0@C15775521399.373C17025492443.355C17027589628.389C17027589631.372C18973515381.414C21482791540.390C23920765557.413C51712377427.356D11893914198.414D16069757088.414D16899842712.414D1699716194.316 D20844746087.358D24982003470.318D27847976046.358D27850073161.390D27850073162.373D28931139668.373D29434646851.373D32458983508.317D3374278032.315 D42037732161.414D43630174531.317D43663251777.414D45715803169.315D49496112240.358D56538493014.414D60098777666.316D60109265003.317D60109446735.358D60110821207.315D60111543912.390D60111543913.414D60111543915.373D62011770191.318D63542604887.390D65226085355.316D68405837779.315D6909504982.315 D9649016128.390 K10112541929.414K10501628393.414K10564380392.390K10672054377.414K10927776744.390K11138048616.390K13094726761.414K13547664719.358K1394472809.414 K16469905093.373K16829898217.414K16897964495.358K17106139215.358K17608596457.414K19686647503.358K20454862031.358K21103696619.373K21300719340.414K214510828.414  K22553882984.390K23133857385.414K24009118671.358K24979176808.390K26480487145.414K26861164521.414K2743966827.373 K27829466091.373K28279300329.414K2872222300.414 K29094539240.390K30036842985.414K30417541865.414K3177024873.414 K32472600680.390K33595313385.414K35254543439.358K35324991211.373K35501707627.373K36207788520.390K3626241896.390 K37323046346.358K38305913182.373K38881363435.373K39314426601.414K39765751016.390K40709646057.414K41088771049.414K42236382827.373K42438265067.373K42694623081.414K44468409449.414K4570151273.414 K45996752875.373K46048471132.414K46429809897.414K46702308456.390K47276501992.390K49686115023.358K49916522475.373K50189619817.414K50366340329.414K51946654569.414K52287600975.358K5238682973.390 K52982894278.390K53036410703.358K53685247339.373K56590166607.358K57242140779.373K57412567787.373K57691992425.414K58271690465.356K5846030287.358 K58692337384.390K58874831593.414K59272310761.414K59596294638.373K60337920975.358K61215647213.390K6300337003.373 K64279710671.358K64293748090.358K64993498601.414K65054173928.390K67835576015.358K7005909992.390 K8906271337.414 K9654319083.373 L10084946068.242L10102288217.2  L10195936580.3  L10390414532.3  L10487310937.2  L10557730137.2  L10590238699.71 L10687032281.2  L10762723780.3  L10840411873.2  L10912730231.1  L10934364249.2  L11123599833.2  L11183176311.1  L12731014519.1  L13092792281.2  L13176305223.2  L13543767769.2  L1408793817.2   L14786404065.2  L15173828345.252L15522136516.71 L16023736625.71 L1615798205.2   L1620283099.345 L16462806593.5  L16840545881.2  L168650209.2    L16910905945.2  L16991276653.3  L17102238681.2  L17606135897.2  L17611387844.71 L17699354692.3  L18018172279.1  L18023395959.1  L18302214263.1  L18430670468.0  L18686846321.3  L18689686129.3  L19039111101.2  L19546883930.247L19691203929.2  L19979755003.71 L204253020.2    L20467279705.2  L20517150065.3  L21089309017.2  L21218866939.2  L21298324828.2  L21644325741.3  L21646758165.388L21654730866.2  L22095213153.2  L22135776033.0  L22507830660.1  L22560471769.2  L23119474137.2  L23711142689.0  L23723668098.3  L24021538905.2  L24619077828.3  L24968328921.2  L25160623805.2  L25185999684.3  L2524128220.2   L25551803524.1  L25636326795.2  L26171659739.2  L2621559066.1   L26486612313.2  L26749591927.1  L2676383091.321 L26875616345.2  L27380263923.3  L27386516966.1  L2741508057.2   L2770202465.2   L27819145305.2  L27940667399.71 L28277369689.2  L2883004908.3   L28933071846.1  L29061550967.1  L29066840183.1  L29105251417.2  L29345674871.1  L30042772057.2  L30431990105.2  L3058445732.2   L30893447543.1  L31569554653.71 L3182954201.2   L32327136116.1  L32454903270.1  L32470277081.2  L32516831197.3  L3276082884.3   L32973469363.2  L33314373181.71 L33597048665.2  L33817424237.3  L34783991938.3  L3482529710.71  L35248827171.71 L35258380249.2  L3532059019.2   L35323190617.2  L35425629300.1  L35516619481.2  L35592291625.352L35631585896.1  L35655538583.72 L35894024561.3  L35915917940.71 L36217981529.2  L36307103329.2  L363258721.2    L3636561113.2   L36460502135.1  L36463206329.4  L36737856104.1  L3726076129.2   L37319210588.2  L3790516599.1   L38235734261.1  L38316036844.3  L38879563353.2  L3901628532.1   L39220054468.3  L39280637297.0  L39321010521.2  L39776468825.2  L39864004961.2  L40122001783.1  L40147631220.1  L4037478596.3   L40471618697.345L40711908697.2  L41103222873.2  L41409160545.3  L41853798621.71 L41898327682.3  L42238313945.2  L42435937113.2  L42683970777.2  L42894358525.71 L42918619434.369L43166046660.3  L43226826465.2  L43571151479.1  L43810982283.2  L44466151385.2  L44488276769.0  L4572017369.2   L45994423385.2  L46042342380.3  L46354690673.3  L46375167856.403L4638341948.71  L46431676249.2  L46695786457.2  L47232700279.1  L47242118263.1  L47261655129.2  L47290354355.2  L47870616696.2  L48067778876.71 L48117620902.242L48117620903.243L48132302231.269L48132302231.286L48132302231.303L48132302231.325L48844506756.1  L48853470583.1  L49508988902.1  L49681561945.2  L49922974809.2  L50187819481.2  L50280382404.3  L50381248345.2  L50925318027.2  L51582382348.337L51953172697.2  L52283110105.2  L5248810732.3   L52941874306.3  L52997799489.5  L53048700121.2  L53527181501.2  L53670729433.2  L5403160439.1   L54486890773.403L54676236769.2  L54793161284.3  L55085943702.3  L55227642495.247L5565789826.3   L55968330615.1  L56162417527.1  L5618218871.1   L56592702936.2  L56602976729.2  L57018078521.71 L57200105028.3  L57227103193.2  L57427085657.2  L57685342937.2  L57798807159.1  L58276650561.5  L5850455129.2   L58698265945.2  L58790416661.71 L58885089625.2  L58972513146.71 L59257267289.2  L59284234861.3  L59308586248.2  L59606483548.2  L60026893533.71 L60056205954.3  L60090598788.1  L60342276185.2  L60448817524.1  L60754583113.0  L61208379660.2  L61209128540.2  L61323929028.3  L61401481953.2  L62772417203.2  L62773985810.403L6297880793.2   L63277261175.1  L63544410086.1  L63685833661.2  L64283672665.2  L64306099948.3  L64526681523.2  L64686745924.3  L6487220337.3   L64979181145.2  L65051713881.2  L6522106337.2   L65391155891.250L65404616823.1  L66298372189.2  L66812728480.3  L66925224585.389L67011971447.1  L67840062809.2  L68123783969.0  L6899380056.1   L6906665613.1   L6912107235.242 L7003453529.2   L7088503905.2   L7282981857.2   L7382465640.1   L7423864255.405 L7731646056.1   L7887530605.3   L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241528381.71  L9656646745.2   N14666517091.373N14734152829.390N22579321058.390N25671718914.373N25747339380.390N26738689353.356N32135528520.373N36095892056.411N38769291813.411N39993692393.411N42015439709.390N42129917801.356N4428092386.356 N45148972570.356N46805509630.390N47136333556.373N47278789786.411N47726722469.356N52312493513.411N55446973656.356N61489387239.390N61497072655.373N61572990241.373N9867865186.411 O10223928153.373O10616892891.414O11202189437.358O11744306779.414O118902745.373  O11932660722.410O12203541638.373O12442373114.371O12665829342.355O13190810150.373O13350092933.390O14544264155.414O14610103385.373O1476819785.390 O1476819786.373 O1478916974.358 O15264779972.358O15266877152.373O15266877155.390O15458007899.414O15722459129.388O15775521399.373O15980584538.390O16212369554.358O16214466742.373O16353064027.414O16698656293.390O17025492443.355O17027589628.389O17027589631.372O17346869210.390O17496721627.414O17752682587.414O18086641154.358O18153340036.414O18260055898.390O18624662875.414O19359855096.410O19421572058.390O19768328667.414O19929130440.414O20456682336.373O20456682339.390O20458779460.358O20679730144.373O20679730147.390O20681827268.358O20937693787.414O21482791540.390O22223811272.414O23564648281.373O23611122160.372O23761539161.373O2432451801.373 O25645093721.373O25707050620.373O28168712666.390O28210256034.358O28722692754.358O28724789941.390O28724789942.373O2882719044.358 O2884816224.373 O2884816227.390 O30247309896.414O3076189822.414 O31167054041.373O32098360648.414O32535777406.414O33081188900.414O33242026440.414O33486960509.358O33682286426.390O34029051227.414O34606453337.373O34897012705.358O34899109829.373O34899109830.390O35068890308.358O35070987488.373O35070987491.390O35590701225.414O3578431456.373 O3578431459.390 O3580528580.358 O36683014984.414O368516552.414  O36877560665.373O37143297523.389O37528692917.390O37528692918.373O37628183240.414O3802965722.390 O3823870405.414 O38615494418.357O39003153661.358O39728539744.373O39728539747.390O39730636868.358O39840516699.414O39920534653.358O4028702351.358 O40346347866.390O40465143428.414O40782554848.373O40782554851.390O40784651972.358O41845693403.414O42194997448.414O42444125821.358O42666666002.358O42893338164.412O43279386587.414O43346802777.373O43849271089.358O43851368213.373O43851368214.390O44193130331.414O4438705243.414 O44423059547.414O44940300029.414O45120147857.414O4518158975.390 O45345472452.358O45347569632.373O45347569635.390O45421758792.414O45652012797.358O45967443054.414O46786196953.373O46796727165.358O48233649620.355O48860633800.414O49057268441.373O4947163994.390 O50436173018.390O50702732434.358O50704829621.390O50704829622.373O50815441627.414O51187063933.358O5160836186.390 O51712377427.356O52018163163.414O52100284413.358O52246202948.358O52248300128.373O52248300131.390O52570971.414   O5310697819.414 O53955549892.358O53957647072.373O53957647075.390O54025433947.414O54383118408.414O54625954301.358O55211981987.410O55516142066.410O5583427803.414 O55957007968.373O55957007971.390O55959105092.358O56414299794.358O56416396981.390O56416396982.373O56496609880.358O56846390264.410O57199369326.414O57539580763.414O58963832153.373O59280371822.414O59623432085.373O59623432086.390O59625529265.358O59804362208.373O59804362211.390O59806459332.358O60143181693.358O60342701914.390O60689491291.414O60980571355.414O6131873076.411 O62208161480.414O62601171929.373O62613783642.390O62935585451.373O62974493732.414O63121348168.414O63758506202.390O64130463451.414O64206259547.414O64471909100.414O65963309678.414O66178352992.373O66178352995.390O66180450116.358O66560762824.414O66805662077.358O67168963241.414O67738280189.358O6812381053.358 O68538934952.390O7241838682.390 O7499981970.358 O7502079157.390 O7588621915.414 O7960765437.358 O859936480.373  O859936483.390  O862033604.358  O999836379.414  P10189109219.358P10191206340.390P10191206343.373P10395186756.390P10395186759.373P10397283939.358P10759107396.390P10759107399.373P10761204579.358P10853506144.414P14791101536.414P1619512637.390 P16469905093.373P16979238126.372P17685179107.358P17687276228.390P17687276231.373P180729696.414  P18674428118.358P18676525297.390P18676525298.373P18676873174.355P19029103898.358P20503990257.388P21212095580.355P21214192760.372P21214192763.389P21649959667.410P21656429036.410P22082150624.414P22503994898.358P23735738370.390P23737835557.358P24620663395.358P24622760516.390P24622760519.373P25156940860.414P25196956131.358P25199053252.390P25199053255.373P25564552978.357P25648406282.414P2782215648.414 P3062169381.414 P3280854084.390 P3280854087.373 P3282951267.358 P32979467521.373P33812653036.410P34787641857.373P34787641858.390P34789739045.358P3528336138.414 P35898756082.371P359543264.414  P36320230624.414P36465839390.358P36467936569.390P36467936570.373P3739204192.414 P39214275427.358P39216372548.390P39216372551.373P39877125088.414P4031765091.358 P4033862212.390 P4033862215.373 P41419110342.358P41421207521.390P41421207522.373P41903025153.373P41903025154.390P43151870819.358P43153967940.390P43153967943.373P43223209056.414P43815688970.414P46342643952.410P47284224258.390P47874275065.414P48850636084.412P50266205539.358P50268302660.390P50268302663.373P50930023690.414P52938159617.373P52938159618.390P52940256805.358P52982894278.390P53531847228.414P54664231776.414P54777977059.358P54780074180.390P54780074183.373P55088519473.358P55090616597.373P55090616598.390P5559018533.358 P5561115649.373 P57202738403.358P57204835524.390P57204835527.373P58271690465.356P59279503597.389P60050384933.358P60052482049.373P60052482050.390P60083949108.411P61334894435.358P61336991556.390P61336991559.373P61389443168.414P62767929637.358P63672705342.373P64541068803.414P64680999907.358P64683097028.390P64683097031.373P6482555632.410 P6517400416.414 P66294657756.414P66816411169.414P7084781280.414 P7295052128.414 P7898593482.355 P8756727811.414 Q10084946068.325Q10087043224.332Q10099627429.321Q10523111611.324Q10592386206.323Q12559082837.373Q12654331938.327Q13355660090.324Q14851060497.329Q14851060498.330Q15766564435.358Q15768661620.390Q15768661623.373Q16069757088.414Q16474908157.414Q1706006080.328 Q1706006095.322 Q19546688630.337Q19548785744.369Q19548785747.352Q19551029871.388Q19561563123.389Q19965418459.358Q21294101882.389Q21765573508.414Q21834833657.414Q21928300230.414Q23925414038.331Q23927511186.324Q25431519408.390Q25475611903.414Q2698790617.369 Q27663295932.337Q27663313085.358Q2805923723.414 Q29719392699.323Q29778078656.414Q30770684634.352Q32435106993.414Q32440833928.321Q33190458471.327Q34335392191.390Q34519400191.337Q34615195986.323Q34667047568.414Q34667424923.414Q34671242809.389Q34964382778.358Q34966479901.390Q34966479902.373Q35655619522.329Q37036249080.323Q38250992820.329Q38250992823.330Q39429474460.413Q39441779646.414Q39460178071.358Q40548233213.414Q41412201209.414Q42437284299.353Q42437284299.370Q42437284299.387Q42437284302.416Q42439168719.358Q42441265896.390Q42441265897.414Q42441265899.373Q42441479405.336Q44587234302.358Q44589331417.390Q44589331418.373Q45463360324.321Q45649254414.321Q46656811515.373Q47230721790.324Q47959845719.414Q48096960980.373Q48096960983.390Q48099058160.358Q48117620904.323Q48118064779.358Q48120161964.390Q48120161965.414Q48120161967.373Q48132302231.321Q48358016497.390Q48358016498.373Q48360113622.358Q49746198710.358Q49748295824.414Q49748295825.390Q49748295826.373Q49748444821.334Q49748444826.415Q49761026999.354Q49761026999.371Q49761026999.388Q50052725144.358Q50240344806.388Q51041977134.324Q51723662261.414Q51724137918.414Q52138493168.414Q54626508119.414Q55922074.369   Q55935130.390   Q56531220660.323Q56699122006.390Q57388114136.390Q57388114139.373Q57390211327.358Q57830202367.414Q58740137381.388Q58741773979.414Q58746443193.413Q5936219132.390 Q60042976435.373Q60111362155.329Q62009673038.331Q62011770186.324Q62198693308.373Q62563604959.358Q65215601094.322Q65215601097.328Q67028562508.354Q67028562508.371Q67028562508.388Q67038703949.358Q67040801129.373Q67040801130.390Q67040801131.414Q67041146721.415Q67041146734.334Q67933129073.358Q68123604991.373Q6897428434.321 Q6910010095.332 Q6912107235.325 Q7093553561.352 Q7093601433.373 Q8192485880.390 Q8360723121.414 Q8697078920.416 Q8697078925.353 Q8697078925.370 Q8697078925.387 Q8699324297.358 Q8701272491.336 Q8701421485.373 Q8701421486.390 Q8701421487.414 Q9350596538.338 Q9350596538.353 Q9350596538.370 Q9356559674.391 Q9634015756.389 Q9640321936.388 Q9644565897.337 Q9644583048.358 Q9646663084.352 Q9646663087.369 Q9646680236.373 Q9646680238.414 Q9646680239.390 00000100200300400800900=00>01M03R05I06X07g09?0;90=30>m0@<0AK0BZ0B[0Cj0E90FH0GW0Hf0J50KM0Le0N=0OU0Pm0RE0S]0Tn0V=0WL0WM0X\0Yk0[70\C0]O0^[0_g0a30b?0cK0dW0dX0ed0g00h<0iH0jT0k`0ll0n80oD10P11\12h14415@16L17X18d1:01;<1<H1=T1>`1?l1A81BD1CP1D\1Eh1G41H@1IL1JX1Kd1M01N<1OH1PT1Q`1Rl1T81UD1VP1W\1Xh1Z41[@1\L1]X1^d1`01a<1bH1cT1d`1da1em1g91hE1iQ1j]1ki1kj1m61nB1oN20Z21f23224>25J26V27b28n2::2;F2<R2=^2>j2?n2?o2@02@12@22@32@O2@P2@Q2@R2@S2@T2@U2@Y2@]2@^2@f2@g2@h2@i2BC2CI2C[2C\2E72E82E92E:2E;2E<2E=2E>2FD2FE2FI2FM2FN2FO2FP2FQ2FR2Gk2Gl2I?2I@2IA2IB2IC2ID2IE2IF2JU2JV2JW2JX2JY2JZ2J[2J\2J]2J^2J_2J`2Ja2Jb2Jh2Ji2Jj2K32K82K92K=2LQ2LR2L]2La2Lb2Lc2Ld2Md2Me2Mf2Mj2Mn2N22N32N72N82N92N:2N>2NX2NY2N]2Na2Nb2Nm2Nn2No2OD2OE2OF2OG2PO2R=2R>2R?2R@2RD2RE2ST2SX2U02U12UK2UL2UM2UN2UO2US2UT2UX2UY2UZ2U^2Ub2Uc2Ud2Uh2Ui2Uj2Uk2Ul2Um2V12V52V62WN2WO2WP2WQ2Wk2Wl2Wm2Wn2Wo2XX2Yg2Yh2Yi2Ym2Yn2Yo2Z02Z12Z22Z32Z42\;2]o2^02^12^52^92^:2^;2^<2`02a\2cH2e42f`2hL2j82j92j=2jA2jB2jC2jD2jE2jF2jG2kV2kW2kX2kY2kZ2k[2k\2k]2k^2kb2mc2md2me2mf2oI2oJ2oN2oR2oV2o^2o_30130230330430530930:30;30<31\31]32732832932?32@32Z32[32\32]32a32b32h32i32j32k32l34F34G34K34O34P34Q34R34S34T34U34V34W34X36O36S36T36U37d37h37i37j37n38339739839939:39>3;b3;f3;g3;h3=h3=i3=j3>C3>X3>Y3?c3@m3BE3CV3Dg3F?3GI3HS3I]3KO3KP3La3Lb3NB3OL3Pd3Rc3Sm3UB3VL3Wl3Wm3YM3YN3YO3YP3YQ3YR3YS3YT3YU3YV3YW3YX3YY3YZ3Y[3Y\3Y]3Y^3Y_3Y`3Ya3Yb3Yc3Yd3Ye3Yf3Yg3Yh3Yi3Yj3Yk3Yl3Ym3Yn3Yo3Z03Z13Z23Z33Z43Z53Z63Z73Z83Z93Z:3Z;3Z<3Z=3Z>3Z?3Z@3ZA3ZB3ZC3ZD3ZE3ZF3ZG3ZH3ZI3ZJ3ZK3ZL3ZM3ZN3ZO3ZP3ZQ3ZR3ZS3ZT3ZU3ZV3ZW3ZX3ZY3ZZ3Z[3Z\3Z]3Z^3Z_3Z`3Za3Zb3Zc3Zd3Ze3Zf3Zg3Zh3Zi3Zj3Zk3Zl3Zm3Zn3Zo3[03[13[23[33[43[53[63[73[83[93[:3[;3[<3[=3[>3[?3[@3[A3[B3[C3[D3[E3[F3[G3[H3[I3[J3[K3[L3[M3[N3[O3[P3[Q3[R3[S3[T3[U3[V3[W3[X3[Y3[Z3[[3[\3[]3[^3[_3[`3[a3[b3[c3[d3[e3[f3[g3[h3[i3[j3[k3[l3[m3[n3[o3\03\13\23\33\43\53\63\73\83\93\:3\;3\<3\=3\>3\?3\@3\A3\B3\C3\D3\E3\F3\G3\H3\I3\J3\K3\L3\M3\N3\O3\P3\Q3\R3\S3\T3\U3\V3\W3\X3\Y3\Z3\[3\\3\]3\^3\_3\`3\a3^63_K3``3b53cJ3d_3f43gI3h^3jT3lJ3nA3nB3oR40g42<43Q45G46\48149F4;=4<n4>_4>`4>a4>b4>c4@34Ai4Aj4C:4DJ4E_4G44HI4J:4KO4Ld4N94N:4Ok4Qa4SW4Tl4VA4WV4Y?4ZO4[_4\o4^?4`64am4cc4eY4fn4hC4iX4kN4lc4n84oM51C52X53m55B56R57b5925:B5;R5<g5><5?Q5AG5C85Do5FX5HI5HJ5I_5K45LI5N:5OJ5PZ5Qj5Qk5S\5UR5Vg5X<5YQ5Zc5\55]G5^W5_g5a<5bQ5cf5cg5e75fG5gW5hg5hh5j=5kR5lg5n]60F62763`65566J67_69V6;L6<[6>Q6@G6B=6CM6E66F:6G>6HB6IK6JO6JP6KX6KY6KZ6Le6N66OG6PX6RH6RI6SQ6TY6V26WK6Xd6Z=6[V6[W6\[6^O6_S6_T6``6b96b:6b;6c?6dC6eG6fO6gS6hb6if6ig6ih6k06l46m86m96n=6oA70E72173]75I76e76f77m7947:87;<7;=7;>7<B7=Q7>`7?o7A>7BM7C\7Dk7F:7GI7GJ7GK7GL7GM7GN7HR7I\7I]7I^7I_7I`7KL7M87Nd7PP7R<7Sh7U:7VL7W^7Y;7ZX7\57]R7^o7`L7ai7cF7dc7eg7fk7fl7h07i47jj7jk7ko7m37m47m57nF7oW80h82I83M84Q85U85V85W86d87j8908:48;88<@8=H8?88@h8BX8DH8F88Gh8IX8KH8M88M98M:8N>8OB8PF8QJ8RN8SR8SS8U88V]8XB8Yg8[L8]18^V8`;8a`8bm8d:8eG8fT8g[8hb8ii8k08l78m>8nE8oL90SFFFFS2FBFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc3HTc4lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72hc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc3HTc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc3HTc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc3HTc4lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2bs4LFB23LFB2B22FB3APB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFFFS2sp3CRT1Q4blen2bs2B22FB3sp1FFFFFFS2FBS2FBFS2lo3sp1FFFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1RS2sp3CRT2bs2FB3sp1FS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn12p12Lw3H40FFFFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1RFS2FBS2FBFSFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1RFFFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFSFFFSFFFFFFS1R2FBFFS4blen2B2S3sp1FS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn11c2HcFS2rg3Hrg2NES2FBFFFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1RFFS2FBS2FBS2FBFS2FBFFFS2FBS2sp3CRT2lo2bs2FB3sp14FBLOFS2FBS2FBFS2sp2lo3sp1FFS2sp3CRT2bs2FB3sp12F0FFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1RS1R3NS14STKc5STKc12sp3CRT3BUF2lo3slo2bs4CRT05CRTLO4SLOS4SLOL2FB3sp13SP13APC5BUFLO3SPR3ALO2F02F14FBLO4SLOu4SP1RFFFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2FBS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFS2sp3CRT3BUF2bs2FB3sp13APBFFFFS2FBFS2FBFFS2FBS2loFFS2FBFSFFFS2FBS2FBFS2LF2sp3CRT1Q4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn12p13H41FFFS2sp3CRT2lo2bs2FB3sp14FBLOFFFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F14SP1RS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2FBFFSFFFFS4PHIk2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn12p14Hp1r1HS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFFS2FBS2FBFFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2FBS2FBFFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFFFFFFS2FBS4FFRk2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn11HFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2FBS2FBS2FBS2sp3sp1FS2sp3CRT2bs2FB3sp1FFFFS2FBFFFS1R3NS14STKc5STKc22sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1RFS2sp3CRT3BUF2bs3B472FB3sp1FFS1i2HiFS2sp3CRT2lo2bs2FB3sp14FBLOFFFS2FBSS1R2FBFFFFS4CNTk5CNTk02LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2FBS2FBFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2FBFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2FBFSS2FBS3CRTS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFS2FBS1R3HIA4PHIj4FFRj4CNTj1h2LF2sp3CRT1Q4blen3BUF2bs4LFB23LFB2B12B22B34CRT03DXB1d2FB3sp13APC3SPR2F03APB4SP1R4LFB36LFB5126LFB5114LFB72hc3BV03BF04lxHn5lxHn05lxHn11H2H02H2S2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F0FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x461CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x601CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x601CS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x461CS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x601CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x271CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x461CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x771CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x771CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x771CFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x271CFS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB74SBND4lxHn5lxHn05lxHn13x271CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x601CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x461CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB74SBND4lxHn5lxHn05lxHn13x771CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x271CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x771CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn13x271CS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB74SBND4lxHn5lxHn05lxHn13x601CFS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB74SBND4lxHn5lxHn05lxHn13x461CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2lo2bs4LFB23LFB2B22FB3sp15BUFLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2lo2bs4LFB23LFB2B22FB3sp15BUFLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen3BUF2lo2bs4LFB23LFB2B22FB3sp15BUFLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen3BUF2lo2bs4LFB23LFB2B22FB3sp13SP15BUFLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF2sp4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS1R3HIA1h2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1FFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2LF4blen3BUF2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2lo2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1FS2LF4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2bs4LFB23LFB2B22FB3ALO4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1FS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPc4lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB74lxHn5lxHn05lxHn1". (* [comment removed for export] *)
  #[using="LFB7 LFB511 LFB512 CRB LFB3 SP1R SLOu FDD APB F8 FBLO F1 F0 ACV ALO SPR BUFLO APC CFB FRSH F64 SP1M SP1 BUD24 BUDF BUDV UW DCD BAM B30 LOS TPV SPH SPA TOP SLO SLOL SLOS DXB CRTLO CWX CRT0 ALC B5 B47 B3 B2 B1 BIN LFB LFB2 C24k0 C24c1 C24c FFRcf_mono PHIcf_mono FFRcf0 PHIcf0 FFRk_mono PHIk_mono CNTk0 FFRk0 PHIk0 CNTx_le FFRx_le PHIx_le CNTn_le FFRn_le PHIn_le CNTj_sadd FFRj_sadd PHIj_sadd CNTj_mono FFRj_mono PHIj_mono CNTj0 FFRj0 PHIj0 STKcfr STKcx STKck STKcn STKc6 STKc5 STKc3 STKc2 STKc1 CRTFREE STKcf CRTEXT STKxx CNTx FFRx PHIx PKPARSE C24k STKk GETNAME STKn CNTn FFRn PHIn GETSIG UID DATES SIGALG XALG SERIAL GINT GT HMND DIMG NF1 NM1 NB1 NA1 ABCMP ACAL AMC AMS STKc4 SF5 STKc0 STKc NS1 IMG"]
  Lemma hdr_walk : forall (hc : HST asegs R HIA) (mm : mem) (lv len : word) (p : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s10v x28 x29 x30 x31 : word),
    cinv [] mm hc FSHP lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 (Z_to_bv 64 1) ->
    crt_zero asegs mm CRT -> bytes_at asegs mm BUF bs -> aobj asegs AL (hcs asegs R HIA hc) mm BUF n ->
    0 < Q ->
    havol asegs R HIA hc <= havol asegs R HIA h -> hfr asegs R HIA hc <= hfr asegs R HIA h ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 Q) (Z_to_bv 64 0) (Z_to_bv 64 (al_sb AL)) s10v
               (Z_to_bv 64 blen) x28 x29 x30 x31)
          F (Z_to_bv 64 0x0a8d88) fc None mm (seg_rom asegs)).
  Proof.
  (* [comment removed for export] *)
  intros until x31.
  intros INV CZ HBUF OBUF Q0 BV0 BF0.
  pose proof (chunks_of_zero asegs CRT mm CZ) as CH.
  open_cinv_mu INV hc.
  ch_open CH.
  try (pose proof (munch_refl W mm) as MU). try (pose proof (wmono_refl asegs mm) as WM).   (* [comment removed for export] *)
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  try lxg_b8u. lx_pre. lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N).
  lx_tree.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e7c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-2" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-3" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 FSHx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LP1 (FB + 128) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-MS1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 128) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8e88: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e7c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-2" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-3" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 FSHx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LP1 (FB + 128) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-MS1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 128) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8e88: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e7c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-2" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-3" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 FSHx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LP1 (FB + 128) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-MS1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 128) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8e88: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e7c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-2" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-3" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 FSHx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LP1 (FB + 128) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-MS1" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 128) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8e88: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e8c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LP2 (FB + 192) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS2-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 192) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8e98: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8e9c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x67ce4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => ms_call LO2 (FB + 256) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MS3-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 256) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-MS3" | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8ea8: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8ebc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x990e0) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with FSHx : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => frame_aobj FSHx (FB + 96) 1%nat as OPP; frame_aobj FSHx (FB + 64) 1%nat as OLN end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "HDR-GT" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with HBx : bytes_at asegs ?mx BUF bs |- _ (MS _ _ _ _ _ ?mx _) => pose proof GT as SPT; unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT; acallxA_sp sp1 (eapply SPT with (CS := hcs asegs R HIA hc) (PP := FB + 96) (LENP := FB + 64) (P := Q) (END := Q + blen) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ xl | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "HDR-GT-LEFT:" g end ]); clear SPT end| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "HDR-GT-POST-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename rg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hrg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?r, H0 : -127 < ?r <= 0 |- _ => subst x; rename r into rg; rename H0 into Hrg end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename p1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hp1r into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : Q <= ?q <= Q + blen |- _ => rename q into p1; rename H into Hp1r end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 64) [C8 ?w] |- _ => rename w into Lw end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HOK into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HOK end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xa8ec8: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052e24; 0x058190; 0x067848; 0x067ce4; 0x068f08; 0x068f10; 0x06adbc; 0x0990e0; 0x0994e8; 0x0a8ec8; 0x0a9040; 0x0a9904; 0x0a9aec; 0x0a9d34; 0x0a9e78; 0x0ab4b0; 0x0ab634; 0x0ac0bc; 0x0acf7c; 0x0ad228; 0x0aefd8] [(0xa8de8, DJoin); (0xa90cc, DJoin); (0xa9160, DJoin); (0xa9284, DJoin); (0xa9374, DJoin); (0xa939c, DJoin); (0xa9584, DJoin); (0xa95bc, DJoin); (0xa9604, DJoin)] 848%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H0 into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => first [ match goal with H : munch _ _ mx |- _ => rename H into MU end | idtac ]; first [ match goal with H : wmono _ _ mx |- _ => rename H into WM end | idtac ] end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f34) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x68f08) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f40 (A_WFREE)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f34) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x68f08) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f40 (A_WFREE)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f50) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6adbc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f5c (0x6adcc)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f50) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6adbc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f5c (0x6adcc)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f50) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6adbc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f5c (0x6adcc)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xa8f50) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6adbc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xa8f5c (0x6adcc)" ]; try clear LXM| |- _ => idtac end.
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xa8ec8) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "HDR-TAG") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (si_mu) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => fold_cinv INV2 mx hc (@nil blk) FSHB; ch_close mx; pose proof (owns_rawnull mx ([] ++ LB) 0) as OWn end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lx_via_eq (eapply free_walk with (Lc := @nil blk) (r := -8576) (rawlen := 0) (rawp := 0)); first [ lx_regs_eq | exact INV2 | exact CH | exact OWn | reflexivity | (left; reflexivity) | lazymatch goal with | |- Permutation _ _ => cbn; apply Permutation_refl | |- BUDE _ _ => eapply (BUD_E hc [] 0 0 0 0); [unfold BUD; pose proof (PHIj0 0 ltac:(clear; lia)); pose proof (FFRj0 0 d ltac:(clear; lia)); pose proof (CNTj0 0 ltac:(clear; lia)); cbn [length]; lia | unfold KVc, X509_SIG_ALG_PHI, AVOL_CALL; pose proof (PHIk0 blen B2); lia | unfold KFc, X509_SIG_ALG_FFR, fr_charge; pose proof (FFRk0 blen (d + 1) B2); lia | pose proof CNTk0; lia | first [ clear - B2; lia | lx_side_lia ]] | |- _ => clear; lia end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "HDR-TAG-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: block free_walk path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xa8ec8) _ _ _ (seg_rom _)] => first [ (lx_apply free_walk) | idtac "lxw: block free_walk path 1: neither the original block nor lx_apply closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xa8ec8) _ _ _ (seg_rom _)] => lx_apply free_walk | |- _ => idtac end.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xa9040) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (r_zero Kt Hrg) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try ((flat constr:((HOK R0)) 2%nat; intros Hp1a HLw)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HOK| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "HDR-OK") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (si_mu) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => fold_cinv INV2 mx hc (@nil blk) FSHB; ch_close mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lx_via_eq (eapply S_COPY with (p1 := p1) (Lw := Lw)); first [ lx_regs_eq | exact INV2 | exact CH | exact BV0 | exact BF0 | eassumption | (first [ clear - Hp1a HLw Hp1r; lia | lx_side_lia ]) | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "HDR-OK-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: block S_COPY path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xa9040) _ _ _ (seg_rom _)] => first [ (lx_apply S_COPY) | idtac "lxw: block S_COPY path 1: neither the original block nor lx_apply closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xa9040) _ _ _ (seg_rom _)] => lx_apply S_COPY | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw hdr_walk: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L1156686087.1 L16810015495.1L26892418956.1L29876834055.1L32463525127.1L37007349134.4L40281191306.3L42861492999.1L56385286098.7L60754583113.000000400800<00@00D00Q00Z00^015016S2FBS2FBS2spS2FBS2FBS1Q3BUF2B12B5S1R3HIA1hS2FBS1R3BUF2lo2bs3BCE3ALO1HS". (* [comment removed for export] *)
  Lemma main_call : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    crt_zero asegs m CRT -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m CRT 744 -> si_P SI m ->
    aevtS asegs POST
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CRT) (Z_to_bv 64 Q) (Z_to_bv 64 blen) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xa98d4) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros until t6. intros HH HK0 CZ HBUF ST SS MI OCRT SIP0.
    pose proof (hm_aobj_block asegs R HIA h LB LF m BUF n HH BIN) as OBUF.
    assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE.
      pose proof (art_lo asegs R HIA) as ALO. pose proof LOS. clear - BCE ALO H. lia. }
    assert (Q0 : 0 < Q) by (clear - B1 B5; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    (* [comment removed for export] *)
    do 4 zstep.
    clear LAWS KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_x509_crt_parse_A.pro_walk with (STKc := STKc) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs) (WS := @nil ivl);
        first [ exact HH | exact CZ | exact HBUF | exact ST | exact SS | exact MI | exact OCRT | exact OBUF | exact LFB | eassumption
              | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & ys10 & y28 & y29 & y30 & y31 & w0 & w1 & w2
                   & jloc & ja & jb & k24 & k32 & k40 & k48 & k56 & k64 & k72 & k80 & k88 & k96 & k104 & k112
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & FLOC0 & FSH & SAVE & RSL & SThi & STlo & MI1
                   & CZ1 & HB1 & OCRT1 & OBUF1 & APC & PRES0 & SS1 & SS2).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 512 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & _).
    (* [comment removed for export] *)
    assert (SIP1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIP0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES0))|].
      intros a Ha. exact (si_outside1 L SI CRT 744 a DCD Ha). }
    assert (PRES1 : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) ((CRT, CRT + 744) :: si_fp SI) m m1).
    { flat constr:(PRES0) 2%nat. flclear PRES0. intros P0 PX. split; [| exact PX].
      eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. split; [exact (proj1 Hx)| exact I]. }
    assert (PRES2 : presW asegs R HIA h1 LB LF (bv_unsigned sp) (bv_unsigned sp) ((CRT, CRT + 744) :: si_fp SI) m m1).
    { eapply (presW_hmono R HIA h h1); [exact PRES1| intros x Hx; rewrite Ehcs; exact Hx| exact Estk]. }
    (* [comment removed for export] *)
    apply (rw_cells_typed asegs m1 (FB + 32) [] 472 jloc [] [8; 24; 8; 24; 8; 24; 4; 4; 8; 8; 40; 4; 4; 8; 8; 40; 4; 4; 8; 8; 224]%nat) in FLOC0; [| reflexivity].
    cbn [tcells app Nat.eqb] in FLOC0.
    chunk_split FLOC0 1%nat LV R1. chunk_split R1 1%nat J1 R2. chunk_split R2 1%nat LN R3. chunk_split R3 1%nat J2 R4. chunk_split R4 1%nat PC R5. chunk_split R5 1%nat J3 R6.
    chunk_split R6 4%nat LP1 R7. chunk_split R7 1%nat J4 R8. chunk_split R8 4%nat LP2 R9. chunk_split R9 1%nat J5 R10. chunk_split R10 4%nat LO2 J6.
    clear J1 J2 J3 J4 J5 J6.
    lazymatch type of LN with rw_cells _ _ ?a _ => replace a with (FB + 64) in LN by (clear; lia) end.
    lazymatch type of PC with rw_cells _ _ ?a _ => replace a with (FB + 96) in PC by (clear; lia) end.
    lazymatch type of LP1 with rw_cells _ _ ?a _ => replace a with (FB + 128) in LP1 by (clear; lia) end.
    lazymatch type of LP2 with rw_cells _ _ ?a _ => replace a with (FB + 192) in LP2 by (clear; lia) end.
    lazymatch type of LO2 with rw_cells _ _ ?a _ => replace a with (FB + 256) in LO2 by (clear; lia) end.
    lazymatch type of PC with rw_cells _ _ _ [C8 ?pw] => rewrite <- (definitions.Z_to_bv_bv_unsigned _ pw) in PC end.
    intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    eapply hdr_walk with (FB := FB) (sp1 := sp1) (hc := h1);
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact APC | exact BUFLO | exact Q0 | exact CZ1 | exact HB1
            | (rewrite Ehcs; exact OBUF1) | (rewrite Evol; clear; lia) | (rewrite Efr; clear; lia)
            | (unfold cinv; spine; first [ exact HH1 | exact PRES2 | exact SIP1 | (intros x Hx; rewrite Ehcs; exact Hx) | (rewrite Ehcs; exact OCRT1) | eassumption
                                         | match goal with |- ?g => idtac "CINV-LEFT:" g end ])
            | match goal with |- ?g => idtac "HDR-PRE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  (* [comment removed for export] *)
  Theorem A_x509_crt_parse_spec : x509_crt_parse_der_stmtA24 asegs R HIA PK SI PHIc FFRc CNTc (A_x509_crt_parse_A.STKx R STKc) C24c 0xa98d4.
  Proof.
    unfold x509_crt_parse_der_stmtA24. intros until bs. intros; subst. unfold CRT_SIZE in *.
    eapply main_call with (bs := bs) (d := d) (slo := slo) (BUF := BUF) (lo := lo);
      first [ eassumption | reflexivity | match goal with |- ?g => idtac "SPEC-LEFT:" g end ].
  Qed.
End Walk.
