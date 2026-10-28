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
Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L19393915969.177L29782099606.1  L55831167499.168L66149329409.209L9354819225.178 00001N01O02i03R058S1R4STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23SPH2FB3sp13SPR3ACV2F02F14SP1R4LFB31H2H02H2SS1R2LF2sp3CRT4blen3BUF2lo3slo2bs4LFB23LFB2B24CRT05CRTLO4SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0S2LF2bs4LFB23LFB2FB2r11H1q1r2H02H12q13H10S1R4STKc3NA15STKc22LF2sp3CRT4blen2lo3slo2bs4LFB23LFB2B24CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4".
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
  | |- context [Z.eqb ?a ?b] =>
      first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; zlia)
            | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; zlia) ]
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
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xa9ca4 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xa9ca4) _ _ _ _) =>
      replace c with true; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zpre := repeat zchk_if.
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
    intros. first [ eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.ea0_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.ea0_walk ]; first [ eassumption | (clear - STKc2; lia) ].
  Qed.

  (* [comment removed for export] *)

  Hypothesis S_SERALG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0AB0@C18971418195.423C18973515383.449C52401662583.448C60410007123.422D11891817072.423D11893914196.449D16071854214.423D16901939902.423D16954620509.449D24579994018.449D32458870384.423D3953997537.423 D40775185266.373D40775185266.425D42035635047.423D42037732163.449D43629700967.423D50871073524.449D55186708378.449D60109196847.373D60109196847.425D60109446735.423D60111543915.449D60189065437.423D67258947169.373D67258947169.425K11645674384.449K12901509199.423K13074033359.423K13667079759.423K1394472811.447 K1396569935.423 K15835051771.373K15835051771.425K1607432955.373 K1607432955.425 K2038874319.423 K214510830.447  K216607946.423  K21870859916.373K21870859916.425K22593309295.447K22861045682.423K22863142806.449K22945712379.373K22945712379.425K23131760207.423K23133857387.447K26480487147.447K26482584271.423K26861164523.447K26863261647.423K27299522255.423K27684414415.423K30036842987.447K30038940111.423K30417541867.447K30419638991.423K31240246991.423K33593216207.423K33595313387.447K33980871419.373K33980871419.425K3591543988.373 K3591543988.425 K37355156075.448K38544919375.423K40707548879.423K40709646059.447K40741729903.447K41088771051.447K41090868175.423K41095599355.373K41095599355.425K4151664304.447 K4427075183.447 K44468409451.447K44470506575.423K4568054095.423 K4570151275.447 K45863235535.423K46975357874.423K5000048842.423 K51793631343.449K51946654571.447K51948751695.423K52147535611.373K52147535611.425K56707495759.423K58872734415.423K58874831595.447K58907964015.447K59270213583.423K59272310763.447K60265445967.423K63645101775.423K66272560811.448K67201981903.423K67950795727.423K8906271339.447 K8908368463.423 K9344607567.423 L10742455373.1  L10840411873.2  L1107926133.436 L11183176311.1  L11650366541.3  L12136144503.1  L12408374717.1  L12531231099.1  L12733015189.73 L12877562377.17 L12878060153.15 L12880089589.17 L12880089591.17 L12888630233.2  L13077864793.2  L13334634337.2  L13405620220.73 L13405747147.108L13662592473.2  L13765201303.97 L13765279664.132L1408793817.2   L14104530683.73 L14105265101.1  L14301694619.2  L14400447526.412L14402536426.411L14420490133.73 L14447004729.2  L14494355149.1  L14636542328.2  L14671452451.73 L14671571220.108L14786404065.2  L14843011723.2  L1549210296.89  L15522251732.95 L15522319221.89 L15684238357.73 L15756275669.95 L15771191613.1  L15822417165.2  L15921722588.1  L1594761485.2   L1619514415.73  L16339982716.73 L16340134219.108L16720167331.436L16722188630.265L16722188630.414L1685717371.0   L168650209.2    L16916955281.2  L16950639097.1  L1751239055.3   L17661654221.1  L17929607435.95 L18031574549.73 L18050741197.1  L18302214263.1  L18577134573.108L18577253338.73 L18605302283.95 L19405429527.95 L19700477813.89 L19912320701.1  L20068494618.95 L20105749565.1  L20254488545.2  L2034453337.2   L20405133530.73 L20405244141.108L204253020.2    L20435272274.108L20435399269.73 L20593040723.73 L20643575009.2  L20821275233.2  L21218032077.1  L21221417243.2  L21557199983.95 L21593730587.2  L21652984618.397L21654730866.2  L21866712442.2  L22095213153.2  L22149007239.73 L22174387027.73 L22488405914.17 L22540039658.3  L22587310557.2  L22866772043.3  L22941438733.2  L22982591434.2  L23033563285.73 L23119474137.2  L23228218977.2  L23513807686.2  L23886653674.394L24023900370.0  L24605490812.73 L24605560395.108L2461029618.11  L24970061901.1  L25060755370.443L25060755370.444L25160623805.2  L25636326795.2  L26171659739.2  L2621559066.1   L26351168119.1  L26486612313.2  L26831527741.1  L26875616345.2  L26979598561.2  L27311746393.2  L27327577336.2  L27386516966.1  L27504652693.73 L27652148129.2  L27696769113.2  L2770202465.2   L27757775585.2  L27816216555.2  L27832536201.398L2784167701.73  L27847074214.3  L27940752054.89 L28044972352.73 L28211258445.17 L28332892109.1  L28631860810.413L28632618922.2  L28633724782.1  L28721978061.1  L29345674871.1  L30042772057.2  L30288503757.95 L30431990105.2  L3058445732.2   L30958001265.3  L31145622673.2  L31163809616.238L31163809616.360L31253192025.2  L3129797493.1   L31322398716.73 L31322484683.108L32084790861.1  L32327136116.1  L32333429070.420L32454903270.1  L33424351062.412L33597048665.2  L33651545427.73 L33817424237.3  L33914883850.361L33985112333.2  L34098898304.89 L34822279507.73 L3482381758.95  L3482445087.89  L34910047158.2  L34911520566.3  L35102401974.1  L35129543782.73 L35156311117.1  L35289649569.0  L3532059019.2   L35455319922.2  L35497690475.3  L35497690475.4  L35497691765.444L35544998830.1  L35627916443.2  L35655538583.72 L3598635821.3   L3623723260.73  L3623833803.108 L36293534260.265L36307103329.2  L363258721.2    L36460502135.1  L36946886283.2  L37122937980.360L3726076129.2   L37353421273.2  L3759492348.73  L3759652043.108 L37875066173.1  L38070592189.1  L3810342902.89  L38235734261.1  L38259954321.2  L38346826506.3  L38412235745.2  L3851065863.73  L38548881625.2  L38756028491.265L39379299611.2  L39571956557.1  L39768386075.2  L39864004961.2  L40228640085.0  L40711908697.2  L40743534045.2  L4077651930.73  L4077844461.108 L4086362840.2   L40918601555.73 L41099742989.2  L41103222873.2  L4111361476.238 L41251426164.1  L4153464066.2   L41663468825.361L41733895573.73 L42411609006.0  L42482149836.1  L42488948659.2  L42656845416.262L42808306952.238L43035585427.412L43226826465.2  L43571151479.1  L43683057355.3  L43810982283.2  L44032115577.73 L44032209742.108L44061217931.2  L4410326440.73  L4410494367.108 L4416226781.2   L44466151385.2  L45057340874.361L4560340619.2   L45704312981.73 L4572017369.2   L45751024331.108L45751192316.73 L45859267673.2  L45950822922.413L46106660189.2  L46177731659.108L46177891452.73 L4638224781.89  L46491294669.1  L46880376525.1  L46882717723.2  L46969621579.3  L47049041130.3  L47870616696.2  L48022350876.420L48150385882.73 L48150504685.108L48455046775.1  L48488035500.95 L48488102925.89 L48707638735.5  L49233373885.2  L49304025233.2  L4943661468.238 L4943661468.360 L49473083873.2  L49997672612.2  L50051061275.2  L5012405084.2   L5021251703.1   L50440147739.2  L5116735037.1   L51785963157.73 L51803952093.2  L5186877564.73  L5187012683.108 L51906071000.2  L51909129149.1  L51953172697.2  L52160193805.2  L52491779133.1  L52835511649.2  L53516992816.360L53516994224.414L5383677973.73  L53849999973.435L53888958349.1  L53997053467.2  L54174754203.2  L54305239829.73 L54324727969.0  L54408904903.265L54408904903.95 L54676236769.2  L55105288843.2  L55182816653.89 L56054802405.73 L56054945746.108L56324446547.73 L56389819352.443L56389819352.444L56418360977.2  L565183155.262  L56587419617.2  L56592702936.2  L56719719641.2  L56847218714.1  L56848026270.73 L57359870875.2  L57389346444.89 L576250010.415  L57698627611.2  L57747140429.1  L57798807159.1  L58039649675.2  L5805279819.108 L5805406844.73  L58304458071.95 L58314874807.11 L58344578928.73 L58885089625.2  L58918812125.2  L59257267289.2  L59308579414.10 L59308580059.18 L59308586248.2  L59308634497.3  L59413075133.1  L59423452235.108L59423530108.73 L59551338477.108L59551498202.73 L6008660450.10  L60278190553.2  L60338798689.2  L6042617148.1   L60516634593.2  L60703606032.73 L60754583113.0  L6087613744.108 L6087732487.73  L60914439501.1  L60915094729.89 L60958946355.95 L61366595738.415L61366595738.436L61366595865.361L61401481953.2  L61497262844.73 L61497357003.108L61567516220.265L61567516220.414L61708038753.16 L62014684890.73 L62014754541.108L62032657340.360L62275882349.3  L62369558384.262L62680556151.1  L6292534466.238 L63430498709.73 L63641134425.2  L639424795.2    L6414907617.2   L64418530427.89 L64418598106.95 L64696484682.361L6487220337.3   L6522106337.2   L65221205066.2  L65232207949.1  L65289245065.429L65607387291.2  L65886782027.108L65886909052.73 L66282753305.2  L66298372189.2  L66332265789.1  L66594121190.2  L66597103718.3  L66721351741.1  L66914912701.1  L67073041482.238L67197556313.2  L67367021494.95 L67461776529.2  L67642182603.108L67642276860.73 L67825443681.2  L67938884378.265L67963146329.2  L6798276507.2   L68033950997.73 L68452440367.435L6899380056.1   L6906665613.1   L7088503905.2   L7282981857.2   L7382465640.1   L7736014575.2   L7945092351.2   L795161084.73   L795328971.108  L8171953640.394 L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241379468.89  L9241446957.95  L9332256473.2   L9960386709.73  N10265517050.448N16246473668.448N20278600635.448N21805675365.448N26872553873.422N30910526005.448N32818861852.448N48204456022.422N54451912735.448N55966132906.422N60733400192.422N63430872977.422N66590330291.422N7710544102.448 O10616892889.447O10618990077.423O11744306777.447O11746403965.423O11930563540.421O11932660720.447O12441062169.448O1259200074.447 O13661656428.447O14667023342.447O16350966909.423O16353064025.447O17217116232.422O17431956130.423O17494624509.423O17496721625.447O18624662873.447O18626760061.423O18999724541.423O19357757918.420O19359855098.446O19768328665.447O19770425853.423O19931227630.423O20160692861.423O20935596669.423O20937693785.447O21709205984.449O21849335257.448O22221714158.423O23600095229.423O2428031690.447 O24480224458.447O24544806105.447O24927677804.447O25875371261.423O26870824124.446O27008647532.447O27837070672.447O29968654986.447O30010457231.423O30011103818.447O30245212782.423O30872837119.447O31857991073.447O32096263534.423O32342533629.423O32535777404.449O32537874520.423O33239929326.423O33658030956.449O339327340.447  O34029051225.447O34031148413.423O34618340093.423O35590701227.447O35592798351.423O35781932925.423O366419438.423  O36680917870.423O37630280430.423O382206333.423  O39094383154.423O40098830794.447O40463046306.423O40465143430.447O41360858771.447O41843596285.423O41845693401.447O42197094638.423O42430790013.423O424351700.421  O44938202843.421O45122245047.423O4531152601.449 O45423855982.423O45969540168.423O46764983242.447O4698090442.447 O47886884318.420O48862730990.423O49701823576.423O50815441625.447O50817538813.423O5310697817.447 O5312795005.423 O53279408345.447O54023336829.423O54025433945.447O54360069450.447O54381021294.423O55209884805.421O55666839717.447O55757313405.423O57201466440.423O57836210557.423O58942634826.447O59278274632.423O60112519114.447O60130887293.423O60687394173.423O60689491289.447O61239930954.447O61464066679.423O62185100234.447O62206064366.423O62226578045.423O63123445358.423O6314859530.448 O63353470717.423O63902264854.449O63904362034.423O64128366333.423O64130463449.447O64464595146.447O64474006218.423O64512383193.447O65331034963.449O66546093258.447O66562860014.423O66601778393.447O66743393030.449O66792327293.423O67707060554.447O7588621913.447 O7590719101.423 P10851408966.423P13321539042.447P14304577628.423P14461423358.373P14461423358.425P14641216507.447P14793198662.423P14839361544.447P16923509334.423P1755912972.446 P182826822.423  P20259153250.447P20648240738.447P20833345762.447P21207000028.423P21608672476.423P21647862485.421P22080053446.423P22535285303.449P22971318541.423P23224560866.447P25154843674.423P25156940862.449P25650503468.423P26991710818.447P27665275170.448P27761498210.447P27803063656.449P2784312774.423 P28627113325.423P3064266499.423 P30967942870.420P31146933846.423P31289833292.426P31289833292.427P31289833292.449P31289833292.450P31289833292.451P324046647.401  P324046647.426  P324046647.449  P324046647.450  P33641443928.401P33641443928.426P33641443928.449P33641443928.450P33810555850.421P33812653038.447P3530433324.423 P35459034609.447P35626081884.423P357446086.423  P3591543988.423 P36322327750.423P36959972360.447P3741301318.423 P38261788758.423P38407561570.447P39390572508.423P39554440246.401P39554440246.426P39554440246.449P39554440246.450P39771269340.423P39879222214.423P42484919333.423P43225306182.423P43679374408.447P43817786156.423P44065883656.449P4548301832.447 P46118674398.447P46884029148.423P47047506707.423P47876372191.421P49230739482.423P49296947798.423P49461037922.447P50010726951.447P50057614556.423P50442506716.423P52847525858.447P53998888156.423P54190221148.423P54662134598.423P55101564936.447P56407612502.423P56574324066.447P57344928092.423P57713046236.423P58041177900.422P60342522594.447P60529728866.447P61391540294.423P62260666314.421P6418557538.447 P6480458454.420 P6482555634.446 P6515303238.423 P653319132.423  P65606077020.423P66292560634.423P67476194902.423P67821826530.447P6809023836.423 P7086878406.423 P7297149254.423 P7750690063.373 P7750690063.425 P7903954312.401 P7903954312.426 P7903954312.449 P7903954312.450 P7941177179.447 P8754630693.423 P8756727809.447 Q10371637966.401Q10371637966.402Q10371637966.427Q10371637966.428Q10371637966.450Q10371637966.451Q10371637966.452Q10592533181.423Q1100286102.422 Q11133374175.423Q1114360721.370 Q11891817072.423Q11893914196.449Q11939405142.385Q12228163960.370Q12945255386.381Q13305674448.421Q13318131160.449Q13676950805.380Q13963846262.390Q14021759145.370Q14360074768.422Q15752730517.394Q15815455344.424Q16020928498.449Q16071854214.423Q16439912048.424Q16472810971.423Q16474908159.449Q1683683270.369 Q16950496597.421Q16952477917.422Q16954620509.449Q17460489309.376Q18087201584.421Q18087207268.445Q18087208808.444Q18089299771.421Q18107911000.449Q18112461904.421Q1831049680.421 Q1843752664.449 Q19327708656.424Q19561449552.397Q19561563123.398Q19790690407.423Q19792787523.449Q19953245935.423Q20032613673.370Q20464211550.387Q20956566126.369Q21136610900.449Q21138708080.423Q21472160987.382Q21767670690.423Q21832736479.423Q21834833659.449Q21930397408.423Q22799085684.449Q22961590783.369Q22963397981.370Q23928209109.374Q23957120639.423Q2408599005.386 Q24579994018.449Q24913533424.424Q25389680632.422Q25473514713.423Q26062420905.422Q26425303288.370Q26481569056.369Q26500407375.370Q26614256344.449Q26618340816.421Q26920001689.384Q26982776420.375Q27665131153.394Q28010126007.395Q2803826605.423 Q28234306710.395Q28465177121.420Q28498905550.395Q28499118027.449Q28986869631.369Q28989404125.370Q2953304272.421 Q2965450712.449 Q29719672728.423Q29775522890.402Q29775522890.428Q29775522890.451Q29775522890.452Q29775981542.423Q30357303536.424Q30439524718.391Q30602636970.369Q30995755539.378Q32010102255.419Q32120916336.424Q32458870384.423Q3260556108.423 Q33447398408.401Q33447398408.427Q33447398408.450Q33447398408.451Q33640236611.449Q33642333799.423Q34615476081.423Q34667111065.396Q34671291067.369Q35010390169.374Q35067538392.449Q35080559824.421Q36585933457.376Q37036722651.423Q37106016912.423Q37106029626.421Q37134077776.421Q37138200664.449Q3731598672.421 Q3735902808.449 Q37546564045.423Q37664897648.424Q3799283926.398 Q38511566559.388Q39041068049.386Q39180574961.423Q39439682456.423Q39441779644.449Q39850762830.401Q39850762830.427Q39850762830.450Q39850762830.451Q39857052210.371Q40772909426.372Q40775185266.373Q40775185266.425Q42035624148.383Q42340228588.421Q42439168719.423Q42439443119.373Q42439443119.423Q42439443119.425Q42441265899.449Q42441548847.401Q42441548847.426Q42441548847.449Q42441548847.450Q42580734868.393Q43010690198.422Q43024701278.377Q43106127567.421Q43997683113.424Q44298944140.371Q44301027056.401Q44301027056.427Q44301027056.450Q44301027056.451Q44359965848.383Q44368939944.375Q45741809296.423Q46294542448.424Q46541987305.423Q46542072643.421Q47651296856.449Q47663800656.421Q47799523355.445Q47799524887.444Q47799530063.370Q47799530063.421Q47801628228.421Q47957748593.423Q47959845717.449Q48017401670.369Q48118064779.423Q48119910507.401Q48119910507.427Q48119910507.450Q48119910507.451Q48120161967.449Q48466957116.449Q48469054232.423Q48782272621.370Q48782272621.422Q49245538982.423Q49245538982.425Q49245821638.423Q49247644710.401Q49247644710.426Q49247644710.449Q49247644710.450Q49247918818.449Q49698585326.371Q49698585326.423Q49746198710.423Q49746415830.373Q49746415830.423Q49746415830.425Q49748295826.449Q49748522582.401Q49748522582.426Q49748522582.449Q49748522582.450Q50871073524.449Q51568379992.379Q51961662993.391Q52067830340.421Q52136395990.423Q52332670359.382Q52464623069.389Q5265442331.421 Q53213300372.379Q53315247896.423Q53332914930.424Q54384261766.449Q54941058045.449Q54994205552.424Q55410796738.449Q55415036769.423Q55613122833.422Q55660191.392   Q55705402538.369Q55942117014.419Q5596578838.401 Q5596578838.427 Q5596578838.450 Q5596578838.451 Q56530976407.423Q57141256644.449Q57146066158.369Q57424580861.449Q57618602681.373Q57618602681.423Q57618602681.425Q57620708409.401Q57620708409.426Q57620708409.449Q57620708409.450Q57828105177.423Q57893485213.396Q57985426136.449Q57998153168.421Q58447922544.424Q58741773977.449Q58742053010.395Q58743871165.423Q58746425531.369Q58845820120.449Q58850083792.421Q5920133699.449 Q5922230887.423 Q59615272911.421Q59615277975.444Q59615278491.445Q59617369028.421Q59769434899.388Q60047576656.421Q60060055896.449Q60133690902.381Q60138834194.377Q60356678983.421Q60703391872.369Q61097091039.378Q6190817072.449 Q6191098356.401 Q6191098356.426 Q6191098356.449 Q6191098356.450 Q6192914196.423 Q6193188724.423 Q6193188724.425 Q62190329447.423Q62586361045.384Q62967769840.424Q63119234008.449Q63132001488.421Q63588016985.380Q64228675114.400Q64228675114.426Q64228675114.449Q64228675114.450Q64635759216.424Q65190342793.449Q65213305287.389Q65509695634.387Q66043421264.421Q66047202648.449Q66063833015.449Q66484855892.449Q66486953072.423Q67038703949.423Q67038978349.373Q67038978349.423Q67038978349.425Q67040801129.449Q67041068973.401Q67041068973.426Q67041068973.449Q67041068973.450Q67041083245.390Q67256769633.372Q67256769633.424Q67258947169.373Q67258947169.425Q67618839536.424Q67781688024.449Q67794406864.421Q68075412041.421Q68077510210.421Q68077515290.444Q68077515798.445Q6909946600.398 Q7093291664.393 Q7264918896.424 Q7740170440.422 Q7970333713.370 Q8142890667.449 Q8360723123.449 Q8362820247.423 Q8551574768.424 Q8699115497.373 Q8699115497.423 Q8699115497.425 Q8699324297.423 Q8701202793.401 Q8701202793.426 Q8701202793.449 Q8701202793.450 Q8701421485.449 Q9356559653.426 Q9356559674.400 Q9600193946.385 Q9633964463.397 Q9634015756.398 Q9644583048.423 Q9646680236.449 Q9890590619.392 00000400800=00A01Q02d04j06b0850:>0;N0=U0?30@R0Ab0C50DE0EX0GS0I:0Jb0L;0MW0Ol0QJ0Ri0U00V=0WJ0XW0Yd0[10\L0]h0_C0`_0al0c90dF0ea0g=0hJ0jE0lL0mg0oC10P11]12j14715D16Q17^18k1:81;E1<R1=_1>l1@91AF1Ba1D=1Ek1Gh1I51JB1KO1L\1Mi1O61PC1Q^1S:1TG1UT1Va1Wn1Y;1ZH1[U1]P1^]1_j1a71bD1c_1e;1fH1gU1hb1io1k<1lI1mV1nc20021=22J23W24d26126626728Y28]28^28b28g28l2;22;32;42;52;62;72;82;92;:2;;2;<2;=2;>2;?2;\2;a2;b2;c2;d2=j2=k2>02>12>22>32>42>52?n2AF2B^2Dd2FP2FU2FV2F_2F`2Hc2Hd2He2KC2M@2O^2O_2O`2Oa2Of2Og2Ol2PY2R_2Rd2Re2Rf2Rg2SO2Ta2V92V>2WW2W\2W]2W^2W_2W`2Wa2Wb2Wc2Y_2Y`2Ya2Yf2Yg2ZP2ZQ2[a2[b2[c2[d2]52_12_X2_Y2_Z2_[2_\2_]2ac2ad2ae2b02cX2cY2cZ2c[2cn2co2ef2g]2g^2g_2gh2gm2h12h22h72h82h92h:2h;2h?2jE2jF2jG2jH2jI2jJ2kZ2m`2mh2o:31@31]31b33233333833=33A33B33n33o34034134235Y37d37e37j37k37l38138539h39l3;;3;<3=83=93>?3>@3>d3@`3B:3CT3C\3C]3C^3D83D=3D>3D?3D@3DA3DB3EU3EZ3E[3G33G43G53G63HQ3HR3HS3HW3HX3Ig3Ih3Ii3Ij3Ik3J03J53Jb3Jf3Jg3Jo3K03L83L93MM3MN3MS3MT3MU3MV3MW3MX3MY3MZ3Mb3O^3O_3O`3Pa3Pe3Pf3Ql3T23T33T83T93Tl3Tm3Tn3To3U33U43U53U63U73U83U93U:3U;3U<3VB3VC3XI3XJ3XK3XL3XM3Y]3Y^3Y_3Y`3[f3[k3\03\13\23\33\43\53\63\73\;3]K3^[3^o3_03_13`X3bc3bd3be3bf3bg3bh3bi3bn3e43e53e63e73e?3eD3eE3eF3eK3eL3fR3g[3ia3ib3ig3ih3ii3ko3l03li3mW3mX3mY3o_3o`3oa41]41^41_41`42O42P42X42Y42^44Z44[45B46U46V46[46_46`46a46b48H48d49>49?49@49A49R49l4:24:94:>4:?4:@4:A4:B4:S4:T4:U4:Z4:[4;g4;h4;i4;j4;o4=b4?_4A24BE4CK4CL4CM4CN4EE4G]4H74H84H94H:4H;4Hn4I24J:4L@4LA4LB4LC4N44Oe4Pk4Pl4Pm4Pn4Q34RK4RL4RM4RN4RO4RP4RU4R]4R^4Rc4Rh4SS4ST4UU4UV4UW4UX4UY4UZ4U[4U\4Wb4Wc4Wg4Wl4Wm4Wn4X24X34X44X54X64X74X84Z84Z94Z:4ZS4[:4[a4[b4]h4_>4`M4a\4bg4d24d34ef4g<4i<4jG4l:4l;4n;4oF4oG4oH4oI4oJ4oK4oL4oM4oN4oO4oP4oQ4oR4oS4oT4oU4oV4oW4oX4oY4oZ4o[4o\4o]4o^4o_4o`4oa4ob4oc4od4oe4of4og4oh4oi4oj4ok4ol4om4on4oo50050150250350450550650750850950:50;50<50=50>50?50@50A50B50C50D50E50F50G50H50I50J50K50L50M50N50O50P50Q50R50S50T50U50V50W50X50Y50Z50[50\50]50^50_50`50a50b50c50d50e50f50g50h50i50j50k50l50m50n50o51051151251351451551651751851951:51;51<51=51>51?51@51A51B51C51D53;55257859=5;C5=55>l5@d5Bo5Df5F]5HT5JK5LB5NH5PN5PO5RF5TP5VV5XM5Z?5\15]c5_Z5aQ5cH5e?5g65i;5k25lj5no60K60L61h63D63E64k66[68K6:;6;U6=96>]6@A6AR6Bc6D[6D\6Fb6HY6K66Lm6N_6PV6R[6TR6VX6XP6Z`6\b6_56a;6c26d\6fS6gi6i[6kM6mE6nU70[72]74O76A78F7:=7<47>:7@@7B77D=7FC7H:7Il7L17Mh7On7QQ7SC7U:7W17Xh7Z97\07]h7_`7aW7c]7ec7g37i87jo7m57nl80c82`84^86a88n8;;8=H8?78@a8BK8Cb8EE8Ff8HS8J48Ka8MN8NS8NT8OY8PX8Q]8Rb8T28UM8V]8V^8V_8Wo8YV8YW8[38\?8\@8^78_h8_i8_j8_k8`j8b38c<8dE8eU8fZ8g_8hd8ii8ij8ik8il8im8in8kH8lb8lc8ld8le8lf8n68o590:91?92O94D95I96N96O96P97O98N99^99_9:o9<`9<a9>F9>G9>H9?c9A;9B69B79B89CH9DX9Ed9Fc9Gl9I89JI9KH9KI9LH9MG9MH9MI9NN9P19Q^9SK9U89VH9VI9X79Y29ZB9[K9[L9\Q9\R9]i9_J9`k9bL9cQ9dV9dW9ec9f^9gn9go9h09i@9iA9jJ9kS9kT9kU9kV9kW9m]9m^9nj:0::1J:3R:4W:5\:6n:8J:9f:;B:<B:=Y:?0:@H:AX:AY:Bi:DK:F2:GU:He:J@:Ke:MJ:No:P;:P<:QL:RU:Sm:Tm:V?:W[:Y7:ZS:[c:]3:]4:]5:^>:_G:_H:_I:`N:aS:bN:cS:dX:dY:dZ:eY:gF:i>:k@:mB:oD;11;12;13;2:;3K;3L;3M;3N;3O;3P;3Q;3R;3S;4_;65;7S;9C;;4;<e;>C;?l;A_;CR;EE;FN;G^;I=;I>;K5;LE;MU;Ng;P7;P8;P9;Qn;Qo;R0;S@;Tc;Ul;W8;X3;Y<;Y=;Y>;Y?;Y@;YA;YB;ZA;[c;]B;_];a=;bY;d?;ee;gK;hm;j9;kB;lK;lL;mQ;n];ob<0]<0^<0_<0`<0a<0b<0c<0d<0e<25<26<27<3G<4W<5`<7G<8W<9`<;6<<V<>6<?V<@_<B;<CW<D\<El<Em<En<Eo<G?<I0<Jk<Li<Ng<P?<QH<RX<Sh<Si<Sj<U3<V8<W=<Xn<[1<]5<_9<`j<bf<dl<g2<i8<jn<lE<m]<o4=0L=0M=0N=0O=1T=2Y=3^=4c=5o=7;=7<=8X=9W=:`=:a=:b=:c=<[=>T=@M=B3=Cd=E_=GZ=IU=K;=LI=MW=Ng=Oo=Q7=R?=SG=TSS2FBS2FBS3CRTS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2Lw1p7rawjunk3HTc4END12rgS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x444END14RLEN3RA12p12Lv3x323x453x463x475POST0S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x264END14RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x444END14RLEN3RA22p12Lv3x323x453x463x475POST0S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp3tbq7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA12rg3Hrg2Kt3K982HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk3x264END14RLEN3RA22x33x273x323x334POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S3CRTFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv2p24Hp2rS2FBFS2FBS3CRTS3CRTS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFFFFFFFFFFFFS2LF2sp3CRT2lo2bs4LFB22FB3sp1S3CRTFFFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFS3CRTFFFFFS1R3NS14STKc5STKc12sp3CRT2lo3slo2bs4CRT04SLOS4SLOL2FB3sp13SP13SPR3ALO2F04SLOu4SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2Lw1p7rawjunk4END1S3CRTFS7rawjunkFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13SP14SP1M3APC3SPR3ALO3ACV2F03APB4SLOu4SP1RFFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv3LVRS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv3LVRS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p12Lv4Hp1a3HLv3LVRSFFS3CRTFS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp12Lw1p7rawjunk4END1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RS3CRTFFFS2sp3CRT2bs2FB3sp13APC2Lw1p7rawjunk4END1S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R2Lw1p7rawjunk4END1S3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S3CRTFFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFFS3CRTFS2sp3CRT2bs4CRT02FB3sp12Lw1p7rawjunk4END1FS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS1R3NS14STKc5STKc12LF2sp3CRT2lo3slo2bs4LFB24CRT04SLOL2FB3sp13SP13SPR2F04SLOu4SP1RS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RS2Lw1p4rawp3Hp14END12p12Lv4Hp1a2p24Hp2rFFFFFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFS6rawlen2RSS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxSFFS2Lw1p4END12p14Hp1rFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEst5CM8st3x322HxS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEst5CM8st3x322HxFFS4blen2B2S3sp1S2FBFS3CRTFFFSS2FBS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RS2ri3HriS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R2Lw1p7rawjunk4END1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RS2Lw1p4END12p12Lv3HLv2p24Hp2rS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS3CRTS3CRTS2FBFS2sp3CRT2lo2bs2FB3sp14FBLO2Lw1p7rawjunk4END1FFFFS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14Hp3'3Hp33RA43LWRS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB72Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14Hp3'3Hp33RA43LWRFS3CRTFFS3CRTS2FBS1R2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEst5CM8st2x32HxS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2sp3CRT2bs2FB3sp12Lw1p7rawjunk4END1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R2Lw1p7rawjunk4END1S2ri3HriFFS2LF2sp3CRT2bs4LFB22FB3sp1S3CRTSFFSSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS3CRTFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R2Lw1p4rawp7rawjunk2RP3Hp14END12rg2p12Lv4Hp1a3LVRFFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFFFS3CRTS3CRTS2sp3CRT2bs2FB3sp12Lw1p4END27rawjunk4END13HE1S2loFS2ri3HriFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB24CRT02FB3sp13SP13SPR2F04SLOu4SP1RFS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R2Lw1p4rawp7rawjunk2RP3Hp14END12rg2p14Hp1aFS3CRTFFSFFFFS2sp3sp1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFFS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R1p4rawp7rawjunk2RP3Hp1S2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RSS3CRTFS2sp3CRT4blen2bs2B22FB3sp12Lw1p7rawjunk4END12rg3HrgFFFS2FBFFFFFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R2Lw1p7rawjunk4END1S3CRTS3CRTFFFFFFFS2FBS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S2Lw1p4END24Hp3'3LWRFFS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14Hp3'3Hp33RA43LWRS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB72Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14Hp3'3Hp33RA43LWRFFFFFFS3CRTS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFFS2rg3HrgS3CRTFFS3CRTFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2rgS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFS3CRTFFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RSS2sp3CRT4blen2bs2B22FB3sp12Lw1p7rawjunk4END12rg2p12Lv3LVRS2sp3CRT2bs2FB3sp12Lw1p7rawjunk4END12p12Lv3LVRFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R2Lw1p7rawjunk4END1FFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFFFS2sp3CRT4blen2bs2B22FB3sp12Lw1p7rawjunk4END12rgFS2sp3sp1FS3sp1S1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1RFS2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgFS3CRTS2FBFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4rawp7rawjunk3Hp14END12p14Hp1aS2Lw1p4rawp3Hp14END12p14Hp1rS2LF2sp3CRT2bs4LFB22FB3sp1FFFS2ri3Hri1r2Ks1q1HS2rg3Hrg2r02Kt1r2Ks1q1H2H5S1i2HiS2ri2KbS3CRTFFFFS2rg3Hrg1r2Kt1q1HFFS3CRTFS1R3NS14STKc5STKc12LF2sp3CRT2lo2bs4LFB24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RSFFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4END26rawlen4rawp7rawjunk4END13Hp34RLEN3HE1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p4END26rawlen4rawp7rawjunk4END13Hp34RLEN3HE12p12Lv3HLvS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rgS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFS1R2sp3CRT4blen2bs2B24CRT02FB3sp13SPR3ACV2F04SP1R2Lw1p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p14Hp1r4Hp1aS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp14END13Hp33RA43HE12rg2p14Hp1r4Hp1aS2ri3Hri1q1r2r01H2H02q02H4FFFFS2sp3CRT4blen2bs2B22FB3sp12Lw1p7rawjunk4END12rg3HrgS2FBS2sp3CRT4blen2bs2B24CRT02FB3sp13SPR2F04SP1R2Lw1p4rawp7rawjunk2RP3Hp13LWRS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA2S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA2S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFSS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg1i2HiFFFFFS3CRTS2rg3HrgFS3CRTS3CRTS2sp3CRT4blen2bs2B22FB3sp12Lw1p7rawjunk3LWRFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4FFFFFFFS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RFS2FBS3CRTFFS2FBFFFFFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1S2sp3CRT2bs2FB3sp12F02Lw1p7rawjunk4END1FS1R3NS14STKc5STKc12LF2sp3CRT1Q4blen3BUF2lo3slo2bs4LFB22B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP15BUFLO3SPR3ALO2F02F14FBLO3APB4SLOu4SP1RS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND3x481CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x341CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND3x341CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END13x481CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA4S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp13ALO2F14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA42HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk2RL4RLEN3RA13RA22HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22rg3Hrg2Kt3K982HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B21d2FB3APC4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk2RL4END14RLEN3RA13RA22HB5Ha_st5Hl_st5SAEst2p12Lv2p24Hp2r2KeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp7rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stFS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HBS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p6rawlen4rawp7rawjunk4END14RLEN2HB5Ha_st5Hl_st5SAEstS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB74rawp7rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p4rawp7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HBFFFFFFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFFFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END14SBND2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFFFFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFFS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEstS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR2F02F84SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12rg2HB5Ha_st5Hl_st5SAEstS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_st5SAEstS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stFS2LF3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1FFFS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p3tbq7rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPc2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END15HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72Lw1p7rawjunk4END1S1R2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT GINT STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_SERALG"] Lemma S_VER : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv : word) (Lw : word) (p END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k24 k32 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl : word) (tbq : Z) (ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv Lw p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128))
         (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl (Z_to_bv 64 tbq) ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p + bv_unsigned Lw <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (CRT + 48)) (Z_to_bv 64 FB) s9v (Z_to_bv 64 (Z.shiftr (CRT + 48) 3 + al_sb AL))
               (Z_to_bv 64 (FB + 96)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa98f4) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp3' Hp3 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    pose proof (bv_unsigned_in_range 64 Lw) as LWR. unfold bv_modulus in LWR. cbn [Z.pow Z.of_N Pos.pow] in LWR.
    (* [comment removed for export] *)
    do 27 zstep.
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
    do 1 zstep.
    zstep. if_cases Kt; zify_cond Kt.
    2:{ (* [comment removed for export] *)
        zstep. zstep. if_cases K98; zify_cond K98.
        { idtac "VER-TAGERR".
          (* [comment removed for export] *)
          do 3 zstep.
          rewrite (swrap32_land_errsum rg 18446744073709543040) by (clear - Hrg; lia).
          do 4 zstep.
          zstep. if_cases Ks; zify_cond Ks.
          2:{ exfalso. clear - Ks Hrg Kt. r_zero Kt Hrg. change 18446744073709551615 with (Z.ones 64) in Ks. rewrite ?Z.land_ones in Ks by lia. Z.div_mod_to_equations. lia. }
          refold_mu INV2 OW2 hc Lc FSHB.
          eapply free_walk with (Lc := Lc) (r := rg + (18446744073709543040 - 2 ^ 64)); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hrg; lia)
                | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-TAGERR-LEFT:" g end ]. }
        idtac "VER-ABSENT".
        (* [comment removed for export] *)
        do 9 zstep.
        refold_mu INV2 OW2 hc Lc FSHB.
        eapply S_SERALG with (Lc := Lc) (END1 := END1) (END2 := END2) (p := p1);
          first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
                | (clear - Hp1r Hp1 HE1 Hp3; lia) | match goal with |- ?g => idtac "VER-ABSENT-LEFT:" g end ]. }
    idtac "VER-TAGOK".
    r_zero Kt Hrg. destruct (HOK R0) as [Hp1a HLv]. clear HOK.
    pose proof (bv_unsigned_in_range 64 Lv) as LVR. unfold bv_modulus in LVR. cbn [Z.pow Z.of_N Pos.pow] in LVR.
    (* [comment removed for export] *)
    do 14 zstep.
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
               | slot_aobj
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
        do 3 zstep.
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (bv_swrap 32 e) with (ri - 8704)
            by (try (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia);
                unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648;
                clear - Hri; Z.div_mod_to_equations; lia) end.
        do 2 zstep.
        zstep. if_cases Kb; zify_cond Kb.
        2:{ exfalso. clear - Kb Hri. rewrite ?signed_lit64 in Kb by lia. first [ lia | (Z.div_mod_to_equations; lia) | (match type of Kb with ?T => idtac "VER-INTCHK-LEFT:" T end; fail) ]. }
        clear Kb.
        do 2 zstep.
        zstep. if_cases Ks; zify_cond Ks.
        2:{ exfalso. clear - Ks Hri. change 18446744073709551615 with (Z.ones 64) in Ks. rewrite ?Z.land_ones in Ks by lia. Z.div_mod_to_equations. lia. }
        refold_mu INV2 OW2 hc Lc FSHB.
        eapply free_walk with (Lc := Lc) (r := ri - 8704); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear - Hri; lia)
              | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-INTERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    { idtac "VER-OK".
      (* [comment removed for export] *)
      do 3 zstep.
      refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_SERALG with (Lc := Lc) (END1 := END1) (END2 := END2) (p := p2);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact B1' | eassumption
              | (clear - Hp2r HLv Hp1r Hp1a Hp1 HE1 Hp3 LVR; lia) | match goal with |- ?g => idtac "VER-OK-LEFT:" g end ]. }
    idtac "VER-MISMATCH".
    (* [comment removed for export] *)
    do 5 zstep.
    refold_mu INV2 OW2 hc Lc FSHB.
    eapply free_walk with (Lc := Lc) (r := -8806); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | (clear - RS; lia) | (clear; lia)
          | (eapply BUD1_E; [exact B1'| clear - B2; lia]) | match goal with |- ?g => idtac "VER-MM-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "07I0@C18971418195.394C23922862675.393D11891817072.394D16071854214.394D16901939902.394D3953997537.371 D3953997537.372 D40775185266.372D42035635047.394D43665348967.394D56536395888.394D60109196847.372D60109446735.394D60189065437.371D60189065437.372D67258947169.372K10114639055.394K10499531215.394K10674151503.394K13096823887.394K1396569935.394 K15835051771.372K1607432955.372 K16827801039.394K17610693583.394K21302816458.394K216607946.394  K21870859916.372K22861045682.394K22945712379.372K23131760207.394K26482584271.394K26863261647.394K28281397455.394K30038940111.394K30419638991.394K3179121999.394 K33593216207.394K33980871419.372K3591543988.372 K39316523727.394K40707548879.394K41090868175.394K41095599355.372K42696720207.394K44470506575.394K4568054095.394 K46427712719.394K50191716943.394K50368437455.394K51948751695.394K52147535611.372K57689895247.394K58872734415.394K59270213583.394K63420573106.394K64991401423.394K8908368463.394 L10102288217.2  L10487310937.2  L10687032281.2  L10840411873.2  L10912730231.1  L11183176311.1  L12408374717.1  L12877562377.17 L12880089589.17 L13092792281.2  L1408793817.2   L14301694619.2  L14402536426.382L14447004729.2  L14786404065.2  L1548849343.87  L15522417010.87 L15771191613.1  L15822417165.2  L1594761485.2   L16023460231.87 L16840545881.2  L1685717371.0   L168650209.2    L16916955281.2  L17606135897.2  L17611635570.87 L18023395959.1  L18302214263.1  L19912320701.1  L20105749565.1  L204253020.2    L21221417243.2  L21298324828.2  L21593730587.2  L21644325741.3  L21652625941.368L21654730866.2  L21866712442.2  L22095213153.2  L22866772043.3  L22941438733.2  L2295337761.0   L22982591434.2  L23119474137.2  L23513807686.2  L25160623805.2  L25636326795.2  L26171659739.2  L2621559066.1   L26486612313.2  L26831527741.1  L26875616345.2  L27386516966.1  L2770202465.2   L27940391089.87 L28277369689.2  L28632618922.2  L29066840183.1  L29345674871.1  L30042772057.2  L30431990105.2  L3058445732.2   L31145622673.2  L3182954201.2   L32327136116.1  L32454903270.1  L33314616971.87 L33597048665.2  L33817424237.3  L33985112333.2  L3482806040.87  L3532059019.2   L35627916443.2  L35655538583.72 L3598635821.3   L36307103329.2  L363258721.2    L36460502135.1  L3726076129.2   L37875066173.1  L38070592189.1  L38235734261.1  L38259954321.2  L39321010521.2  L39379299611.2  L39768386075.2  L39864004961.2  L39925292426.360L40228640085.0  L40692963805.87 L40711908697.2  L41060389218.359L41099742989.2  L41103222873.2  L42683970777.2  L43226826465.2  L43571151479.1  L43810982283.2  L44466151385.2  L45057340874.360L4572017369.2   L46354690673.3  L4638061450.87  L46431676249.2  L46882717723.2  L47049041130.3  L47242118263.1  L47870616696.2  L48068055434.87 L48487939594.87 L49304025233.2  L50051061275.2  L50187819481.2  L50283706766.12 L50381248345.2  L50440147739.2  L50925318027.2  L5116735037.1   L51906071000.2  L51908265048.3  L51909129149.1  L51953172697.2  L52160193805.2  L52491779133.1  L53527181501.2  L53997053467.2  L54174754203.2  L54676236769.2  L56418360977.2  L56592702936.2  L57359870875.2  L57685342937.2  L57698627611.2  L57798807159.1  L58304389180.12 L58885089625.2  L59257267289.2  L59308586248.2  L59413075133.1  L6008660450.10  L6042617148.1   L60448817524.1  L60754583113.0  L61366595865.360L61401481953.2  L63422184011.3  L639424795.2    L64418367100.87 L64526681523.2  L6487220337.3   L64979181145.2  L6522106337.2   L65404616823.1  L65607387291.2  L66298372189.2  L66332265789.1  L66721351741.1  L66914912701.1  L66925224585.369L67461776529.2  L6798276507.2   L6899380056.1   L6906665613.1   L7088503905.2   L7282981857.2   L7382465640.1   L7736014575.2   L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.87  N26738689353.393N42129917801.393N4428092386.393 N45148972570.393N47726722469.393N55446973656.393O1001933565.394 O10618990077.394O11746403965.394O11930563540.392O14542167037.394O15460105085.394O16350966909.394O17494624509.394O17750585469.394O18155437218.394O18626760061.394O19357757918.391O19770425853.394O19931227630.394O20935596669.394O22221714158.394O30245212782.394O3078286936.394 O32096263534.394O32537874520.394O33239929326.394O33990841394.394O34031148413.394O35592798351.394O366419438.394  O36680917870.394O37630280430.394O39838419581.394O40463046306.394O41843596285.394O42197094638.394O43277289469.394O44195227517.394O4440802429.394 O44425156733.394O44938202843.392O45122245047.394O45423855982.394O45969540168.394O48862730990.394O50473853.394   O50817538813.394O52020260349.394O5312795005.394 O54023336829.394O54381021294.394O55209884805.392O55518239188.392O5585524989.394 O56848487390.391O57201466440.394O57537483645.394O59278274632.394O60687394173.394O60978474237.394O61464066679.394O62206064366.394O63123445358.394O63904362034.394O64128366333.394O64204162429.394O64474006218.394O65961212488.392O66562860014.394O67171060367.394O7590719101.394 P10851408966.394P14304577628.371P14304577628.372P14461423358.372P14793198662.394P16923509334.371P16923509334.372P182826822.394  P21207000028.371P21207000028.372P21608672476.371P21608672476.372P21647862485.392P21658526154.392P22080053446.394P22971318541.371P22971318541.372P25154843674.394P25650503468.394P2784312774.394 P28627113325.371P28627113325.372P3064266499.394 P31146933846.371P31146933846.372P33810555850.392P3530433324.394 P35626081884.371P35626081884.372P357446086.394  P3591543988.371 P3591543988.372 P36322327750.394P3741301318.394 P38261788758.371P38261788758.372P39390572508.371P39390572508.372P39771269340.371P39771269340.372P39879222214.394P43225306182.394P43817786156.394P46340546774.391P46884029148.371P46884029148.372P47047506707.394P47876372191.392P49296947798.371P49296947798.372P50057614556.371P50057614556.372P50442506716.371P50442506716.372P50927926572.392P53529750042.394P53998888156.371P53998888156.372P54190221148.371P54190221148.372P54662134598.394P56407612502.371P56407612502.372P57344928092.371P57344928092.372P57713046236.371P57713046236.372P61391540294.394P64538971685.394P6480458454.391 P6515303238.394 P653319132.371  P653319132.372  P65606077020.371P65606077020.372P66292560634.394P67476194902.371P67476194902.372P6809023836.371 P6809023836.372 P7086878406.394 P7297149254.394 P7750690063.372 P8754630693.394 Q1114360721.369 Q12228163960.369Q16071854214.394Q16472810971.394Q1683845592.368 Q19561349487.368Q19561563123.369Q20032613673.369Q20956599408.368Q21294101882.369Q21767670690.394Q21832736479.394Q21930397408.394Q22961297377.368Q22963397981.369Q23957120639.371Q23957120639.372Q25473514713.394Q25952160488.370Q25952160488.371Q26479524806.391Q26481467398.367Q2803826605.394 Q28465177121.368Q28465177121.369Q29775981542.394Q30602209460.368Q32437204119.394Q3260556108.371 Q3260556108.372 Q33842015361.368Q34669522109.394Q34671242809.369Q37546564045.371Q37546564045.372Q39180574961.371Q39180574961.372Q39439682456.394Q40550330331.394Q40772909426.371Q40775185266.372Q41414298335.394Q42439168719.394Q42439443119.371Q42439443119.372Q42641849633.368Q45741809296.371Q45741809296.372Q47957748593.394Q48118064779.394Q48782272621.369Q49698585326.370Q49746198710.394Q49746415830.371Q49746415830.372Q50233694694.368Q51722040728.394Q52136395990.394Q5265442331.369 Q5265442331.370 Q54624410993.394Q55415036769.371Q55415036769.372Q57618602681.371Q57618602681.372Q57828105177.394Q58743871165.394Q58746001061.368Q60191312605.370Q60191312605.371Q60701382246.391Q60703362470.367Q67038703949.394Q67038978349.371Q67038978349.372Q67256769633.371Q67258947169.372Q8362820247.394 Q8699115497.371 Q8699115497.372 Q8699324297.394 Q9356559674.371 Q9634015756.369 Q9634064528.368 Q9644583048.394 00000400801>03:04h06e08g0:>0;D0<J0=P0?00@?0BJ0DZ0F10G40H70I:0J=0K@0LT0Mh0Nk0On0Q10R40SH0U@0VT0WW0XZ0Y]0Z`0[c0\f0]i0^l0`@0ag0bj0cm0e00fD0gG0hJ0iM0jP0kS0lV0mY0nm10011312613n15116416516616716816916=16B16C16D16E16F16G16H16I16J18919G19L19M19N19h19i19j19k19l19m1;;1;?1;@1;E1;J1;K1;L1;M1;N1;O1<U1<V1<W1<X1<Y1<Z1<[1<\1<]1<h1<i1<j1=31=81=91=>1=?1=C1=D1>L1>M1>N1>R1>V1>W1>X1>Y1>Z1>[1>_1>c1?@1?A1?B1?C1@S1@T1@U1Am1An1Ao1B01B41B51B:1B?1BC1BD1BE1BF1BG1BH1CN1CO1E41E51FD1FE1FF1FG1FH1FL1FM1FN1GT1GU1GV1IR1IS1IT1IU1IY1IZ1KV1L\1L]1L^1L_1Lo1M01M11M21M71M?1M@1ME1MF1MG1ML1MM1MN1MO1MP1MQ1MY1MZ1M[1M\1M`1N41N51N61N<1NA1NR1NW1N[1N\1Ob1Oc1Od1Oe1QL1QM1QN1QO1QP1QT1QU1QV1Q[1Q`1Qe1Rk1Rl1Rm1S11S61S71S81S<1S=1S>1U>1U?1U@1UY1V61WB1Xk1Xl1Zb1[c1\d1\e1\f1\g1\h1\i1\j1\k1\l1\m1\n1\o1]01]11]21]31]41]51]61]71]81]91]:1];1]<1]=1]>1]?1]@1]A1]B1]C1]D1]E1]F1]G1]H1]I1]J1]K1]L1]M1]N1]O1]P1]Q1]R1]S1]T1]U1]V1]W1]X1]Y1]Z1][1]\1]]1]^1]_1]`1]a1]b1]c1]d1]e1]f1_S1aO1cP1eN1g;1i61k21l_1n[20\22X24Y24Z25a27N29J2;K2=32>[2@H2BC2D?2El2Gg2Ic2Jj2LX2NT2PU2RB2TM2VY2XF2Z32[n2]j2_f2ag2cc2ed2gQ2i>2jf2lT2nP30Q32I34135l37h39d3;e3=a3?b3AJ3C23Dn3Fo3Hk3Jl3LY3NT3PP3RL3TM3Uf3W@3Xm3ZM3\;3]h3_d3ae3ca3eb3fh3hc3j_3l[3n\40I42643l45L46K47f49M49N4:M4;]4<m4<n4=m4>h4@S4AN4AO4BN4CM4CN4CO4CP4E;4Fg4H?4IW4JV4K]4Ld4Mj4Ne4Nf4Ng4Nh4P@4Q;4R64T24V34X14Z04Zk4Zl4\<4]L4^G4_M4`j4bN4d54d64d74d84e[4fb4gn4iB4ji4lW4mR4nM50:51B52J52K53d55>57O59g5;?5<:5=55>o5@j5BQ5D85E_5GY5IZ5Jj5L:5L;5Mj5O`5Q<5R@5S>5T<5U:S2FBS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc4END27rawjunk3HTc2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk3x234RLEN3RA22x33x243x253x264POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B21d2FB4LFB36LFB5126LFB5114LFB71p6rawlen4rawp7rawjunk4RLEN3RA12HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B21d2FB3sp14LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk3x234RLEN3RA22x33x243x253x264POSTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFFFFS2FBS3CRTFFFFFFFFS1R3NS14STKc5STKc12sp3CRT2lo3slo2bs4CRT04SLOS4SLOL2FB3sp13SP13SPR3ALO2F04SLOu4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTFFS2sp3CRT2bs2FB3sp17rawjunkFSFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS2FBFS3CRTS3CRTFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFFFSFFS6rawlen2RSFFS4blen2B2S3sp1FS3CRTFS2FBFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFFS2FBS2FBFFFFFS2FBS2FBS2sp3CRT2bs2FB3sp12F07rawjunkFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFS2FBFS3CRTS3CRTS2loFFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END26rawlen4rawp7rawjunk3Hp34RLENFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFFFS2FBFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkFFFS2FBFS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO4SLOS4SLOL2FB3sp13SP13SPR3ALO2F02F14FBLO4SLOu4SP1R7rawjunkS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FFFS4END22p12Lw3HLwFFFS3CRTS2rg3HrgFS3CRTFFS3CRTFFFFFS2sp3sp1FFFS2FBS1p4rawp3Hp12p14Hp1aFFS1i2HiS3CRTS2rg3Hrg1r2Kt1q1HS3CRTS2FBSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FFFFS2FBFFS3CRTS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2FBS3CRTFFS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x271CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x271CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x271CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x271CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x271CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA32HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END26rawlen4rawp7rawjunk4RLEN3RA32HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R2LF3CRT4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_st3sp14END2S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B24CRT02FB4LFB36LFB5126LFB5114LFB77rawjunk2HBS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB33CRB6LFB5126LFB5114LFB77rawjunk2HB5Ha_stS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_st4END2S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_stFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO3LOS2FB3sp13SP13ALO2F14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND2HB5Ha_st5Hl_stS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_st3NS14STKc3NA15STKc25CRTLO3LOS3sp13SP13ALO2F14FBLO4SLOu4END24SBNDS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB74END27rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk2HB5Ha_st5Hl_stS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_st4END2S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB71p7rawjunk2HB5Ha_st5Hl_stFS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPc2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3CRT4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB71p7rawjunk5HTOPc2HB5Ha_st5Hl_st4END2S1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GT GINT STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIk0 FFRk0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7 S_SERALG"] Lemma S_TBS : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END2 : Z)
      (a1 a2 a3 a4 : word) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k24 k32 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 : word) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (img : byte) (ipad : list byte) (sj48 : list byte) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word)
      (rawjunk : list byte)
      (k40 k48 s9v x1 x5 x6 x7 x10 x11 x13 x15 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 k40 k48 (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 128))
         (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 0 img ipad sj48 0 smg spad dates pr1 pr2 pr3 pr4 0 0 u1 u2 u3 u4 v1 v2 v3 v4 ext_own_zero ext_junk_zero gtg gpd glen gq sigmd sigpk 0 ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0 rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp 0 [] 0 [] 0 0 [] ext_own_zero 0)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawlen <= blen -> rawp <= p -> p <= END2 -> END2 <= rawp + rawlen ->
    BUD1 hc Lc 0 -> cnt24 (Lc ++ LB) <= cnt24 LB + blen / 5889 ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 (Z_to_bv 64 (FB + 64)) x13 (Z_to_bv 64 END2) x15 (Z_to_bv 64 (FB + 96)) x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 Q) (Z_to_bv 64 FB) s9v (Z_to_bv 64 (Z.shiftr (CRT + 16) 3 + al_sb AL))
               (Z_to_bv 64 (CRT + 16)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9850) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp3 B1' C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 15 zstep.
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
    2:{ idtac "TBS-TAG". do 2 zstep. refold_mu INV2 OW2 hc Lc FSHB.
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
