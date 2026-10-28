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
Definition zchk_new : list Z := [0xa9410; 0xa9428; 0xa9438; 0xa943c; 0xa9440; 0xa9464; 0xa9468; 0xa9538; 0xa9544; 0xa9550; 0xa9554; 0xa9578; 0xa95b0; 0xa95b4; 0xa95d0; 0xa96ec; 0xa96f0; 0xa96f4; 0xa96f8; 0xa96fc; 0xa9700; 0xa9704; 0xa9708; 0xa970c; 0xa9710; 0xa9714; 0xa9718; 0xa9748; 0xa9750; 0xa9764; 0xa976c; 0xa97b0; 0xa97b4; 0xa97b8; 0xa97bc; 0xa97c0; 0xa97c4; 0xa97c8; 0xa97d0; 0xa97d4; 0xa97d8; 0xa97dc; 0xa981c; 0xa9824; 0xa9828; 0xa982c; 0xa9830; 0xa9838; 0xa9844; 0xa984c; 0xa9854; 0xa9860; 0xa9880; 0xa9884; 0xa9898; 0xa98ac; 0xa98f4; 0xa98f8; 0xa98fc; 0xa9900; 0xa9904; 0xa9908; 0xa990c; 0xa9910; 0xa9914; 0xa9950; 0xa9954; 0xa99a0; 0xa99b0; 0xa99b4; 0xa99b8; 0xa99bc; 0xa99c0; 0xa99d0; 0xa99e0; 0xa99e4; 0xa99e8; 0xa99ec; 0xa9a08; 0xa9a24; 0xa9a28; 0xa9a5c; 0xa9a60; 0xa9a7c; 0xa9acc; 0xa9ad8; 0xa9adc; 0xa9ae0; 0xa9ae4; 0xa9ae8; 0xa9af0; 0xa9af4; 0xa9af8; 0xa9afc; 0xa9b00; 0xa9b04; 0xa9b08; 0xa9b0c; 0xa9b10; 0xa9b14; 0xa9b34; 0xa9b38; 0xa9b3c; 0xa9b40; 0xa9b44; 0xa9b84; 0xa9bd8; 0xa9bdc; 0xa9be4; 0xa9be8; 0xa9bec; 0xa9bf0; 0xa9bf4; 0xa9bfc; 0xa9c00; 0xa9c08; 0xa9c0c; 0xa9c10; 0xa9c14; 0xa9c18; 0xa9c1c; 0xa9c20; 0xa9c24; 0xa9c58; 0xa9d54; 0xa9f1c; 0xa9fe4].
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6757220598.1000001S".
Lemma zchk_land1 x : Z.land x 1 = x mod 2. Proof. apply (Z.land_ones x 1); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41422538246.1000001S".
Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29782099606.1000001S".
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L19393915969.177L40819769766.1  L55831167499.168L66149329409.209L9354819225.178 00001N01O02i03R058S1R4STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B23SPH2FB3sp13SPR3ACV2F02F14SP1R4LFB31H2H02H2SS1R2LF2sp3CRT4blen3BUF2lo3slo2bs4LFB23LFB2B24CRT05CRTLO4SLOS4SLOL2FB3sp15BUFLO3SPR2F01H2H0S2LF2bs4LFB23LFB2FB2r11H1q1r2H02H12q13H10S1R4STKc3NA15STKc22LF2sp3CRT4blen2lo3slo2bs4LFB23LFB2B24CRT04SLOS4SLOL3SPH2FB3sp13SPR2F01S2H02H22H32H4".
Lemma zchk_land15 x : Z.land x 15 = x mod 16. Proof. apply (Z.land_ones x 4); lia. Qed.
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
Local Ltac zchk_false :=
  repeat match goal with H : context [Z.land ?x 7] |- _ => rewrite (zchk_land7 x) in H end;
  repeat match goal with H : context [Z.land ?x 3] |- _ => rewrite (zchk_land3 x) in H end;
  repeat match goal with H : context [Z.land ?x 1] |- _ => rewrite (zchk_land1 x) in H end;
  repeat match goal with H : context [Z.land ?x 15] |- _ => rewrite (zchk_land15 x) in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => destruct (Z.eqb_spec a b); cbn in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => destruct (Z.eqb_spec a b); cbn in H end;
  try discriminate; zlia.
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
  rewrite ?zchk_land1, ?zchk_land3, ?zchk_land7, ?zchk_land15;
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
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) zchk_new) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Local Ltac zstep_to L :=
  repeat (lazymatch goal with
          | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch eval vm_compute in (List.existsb (Z.eqb pc) L) with true => fail | false => zstep end
          end).
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

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKc2 Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH DCD SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma exit3_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    intros. first [ eapply A_x509_crt_parse_C.exit3_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.exit3_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.exit3_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.exit3_walk ]; eassumption.
  Qed.

  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SLOu"] Lemma f2f4_walk : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p : Z)
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
    intros. first [ eapply A_x509_crt_parse_C.f2f4_walk with (STKc := STKc) (BUF := BUF) (bs := bs) (Q := Q) | eapply A_x509_crt_parse_C.f2f4_walk with (STKc := STKc) (BUF := BUF) (bs := bs) | eapply A_x509_crt_parse_C.f2f4_walk with (STKc := STKc) | eapply A_x509_crt_parse_C.f2f4_walk ]; eassumption.
  Qed.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L32248750578.17800000nS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7". (* [comment removed for export] *)
  #[using="LF sp CRT blen bs LFB2 LFB B2 FB sp1 LFB3 LFB512 LFB511 LFB7"] Lemma ext_blocks_small : forall eo b, In b (ext_blocks eo) -> snd b < 5889.
  Proof.
    intros eo b Hb. unfold ext_blocks, SSEQ in Hb. repeat (apply in_app_iff in Hb; destruct Hb as [Hb|Hb]);
      apply in_map_iff in Hb; ddestruct Hb as (x & <- & _); cbn [snd]; unfold SEQ_SIZE; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  Ltac perm_front :=
    rewrite ?app_assoc; repeat apply Permutation_app_tail; rewrite <- ?app_assoc;
    first [ apply Permutation_refl | eapply Permutation_trans; [apply Permutation_app_comm|]; rewrite <- ?app_assoc; apply Permutation_refl ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0390@D11881314541.380D17454457060.380D20225638161.411D36579903016.380D42945744483.380D52056127147.409D53340075670.411D6192911893.409 D64348882538.382D64348882538.411L10370335306.1  L1107926133.402 L11183176311.1  L11891917965.1  L12087575053.1  L1408793817.2   L14648255538.87 L1540615640.71  L15450392973.1  L15522417010.87 L16375522333.2  L17454195193.1  L19979998541.87 L204253020.2    L21564613915.71 L21650528252.378L23119474137.2  L23131121677.1  L23513807686.2  L24373605877.6  L2485369708.87  L25160623805.2  L25928078093.1  L26486612313.2  L26687380749.1  L26875616345.2  L27036101880.2  L27386516966.1  L29345674871.1  L30042772057.2  L30245850637.1  L30288275819.87 L30431990105.2  L30603178013.2  L315074172.87   L31863041268.87 L32327136116.1  L32454903270.1  L33450796305.2  L33597048665.2  L33608807821.1  L3482806040.87  L35655538583.72 L36460502135.1  L36579641141.1  L37622627047.5  L38235734261.1  L40281191306.3  L40692963805.87 L40711908697.2  L41103222873.2  L41555119221.402L43571151479.1  L44466151385.2  L45665153858.2  L4572017369.2   L48031944461.1  L48487939594.87 L48495860913.87 L48677595711.2  L48765611037.2  L51953172697.2  L55880503837.2  L56727003629.87 L57798807159.1  L58885089625.2  L59257267289.2  L59268928141.1  L59308586248.2  L60754583113.0  L61366595865.402L61899024797.71 L62631872013.1  L62827399053.1  L63199674356.401L64418367100.87 L64454402074.87 L64584198252.2  L64586655724.3  L6487220337.3   L64889357135.3  L66188249869.1  L66212808353.0  L66577348109.1  L66718584747.2  L66940954653.2  L67367117072.87 L6899380056.1   L6906665613.1   L7234483181.87  L7382465640.1   L8742280115.2   L9080482849.71  L9756567308.1   P1396571726.409 P14847612824.409P16387876490.409P216606155.409  P22134471192.409P23131762510.409P26033826406.409P26482582478.409P26863263438.409P29455900312.409P30038937806.409P30296385645.409P30419637198.409P30615466634.409P33010176920.409P33143934054.409P33377767064.409P33593214414.409P34508873193.409P3985014296.409 P40707551182.409P41090869966.409P428624152.409  P44179613286.409P44470508878.409P45652865493.409P4568051790.409 P46851611017.409P47601162904.409P47809338136.409P48761777802.409P51365709848.409P51948749390.409P54465921638.409P55876079754.409P58653617304.409P58872736718.409P59270211278.409P62211563928.409P65767921304.409P66928011914.409P7866543718.409 P8497851288.409 Q1396571726.409 Q15985628819.411Q16387876490.409Q19546638454.409Q19546672262.378Q216606155.409  Q23131762510.409Q25154845979.409Q25805880151.378Q25818047808.410Q26479650234.395Q26479650234.396Q26482582478.409Q26483566295.378Q2676383091.411 Q26863263438.409Q30038937806.409Q30419637198.409Q30604720970.410Q30605160672.410Q30615466634.409Q30617628407.378Q33593214414.409Q33842007104.410Q33854476887.378Q40707551182.409Q41090869966.409Q42637231095.378Q42641841632.410Q44470508878.409Q45652865493.409Q4568051790.409 Q48680001726.409Q48761777802.409Q50244178959.378Q51948749390.409Q53579323758.409Q55876079754.409Q58743905100.378Q58748470619.410Q58872736718.409Q59270211278.409Q60701509658.395Q60701509658.396Q60713847671.378Q6192911893.409 Q6480460759.409 Q64883644649.409Q66711720973.409Q66928011914.409Q68281680193.409Q8754632996.409 Q9644549497.378 Q9644581257.409 00001602<03G04M05S06]07h08n08o0::0:@0<G0<K0<P0<U0<V0=Z0>00>50?C0?D0?I0@d0@e0A=0BC0BD0BI0BT0Bf0CI0CJ0CO0CP0CU0CV0CW0C[0C_0C`0Ce0DG0DH0DI0EX0Ff0Fj0Fn0G<0G=0GB0HR0Ij0In0J30JD0JH0JQ0L60L70L80N;0N?0N@0NA0NB0NG0OM0PU0PV0PW0PX0PY0Q<0Q@0QA0QB0QG0QM0QN0RT0Rl0S10S60S70T^0UR0UZ0U[0U\0U]0Ub0Uc0Uh0Ui0Uj0Wa0We0Wj0XH0XL0XM0Xf0Xk0Yn0[[0\^0]a0_N0`Q0b90c<0d?0el0fo0h;0i>0jA0kn0mV0oC10F11n13[14^15a17N1961:91;<1<?1=l1?Y1AF1BI1D61E91Fg1Gj1IW1JZ1K]1MJ1O71P:1Qb1SO1SP1SQ1SR1Tb1V21V31V41W\1Y41ZL1[d1]<1]=1^U1_U1_V1_W1_X1`S1b:1b;1cb1cc1e;1fS1fT1fU1h<1ic1id1ie1if1kK1kL1lG1lH1mG1mH1nC1o>1o?1o@20g22N24525426b28O2:<2:=2;T2=42>22?0S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1x2HxS4rawpS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp13Hp33RA42p24Hp2'S2FBS3CRTS3CRTFS1R4STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkS2sp3CRT2bs2FB3sp13SP1S3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFS1R2sp3CRT2bs2FB3sp13FDDS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS3CRTS6rawlen2RSS3CRT2FB1x1k2Y12Y2S2sp3CRT2bs4CRT02FB3sp13CRB7rawjunkFS3CRTFS3CRTFSS2FBS2FBFS3CRTS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkS2FBS2FBS4rawp7rawjunkFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2FBS3CRTS2FB1x2NF3CRT3Hx1S2loS1R3HIA1hS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END26rawlen4rawp7rawjunk3Hp34RLENFFS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END26rawlen4rawp7rawjunk2RP3Hp13Hp23Hp33RA4S2FBFFFS3CRTS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFFFFS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS2FBFFS3CRTS1i2HiSS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2sp3CRT2bs3DCD2FB3sp1S3CRTS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F02F14SP1R7rawjunkS2rk3HrkFFFS3CRTSS3CRTFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBS3CRTS2sp3CRT2bs2FB3sp13APC7rawjunkS2FBFS2sp3CRT2lo2bs2FB3sp13SP1S3CRTS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk1c2HcFFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc7rawjunk3HSc5HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 NA1 DIMG HMND GETSIG STKcf CRTFREE STKc1 STKc2 STKcfr CNTj0 CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_SIG : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END2 : Z)
      (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 : word) (ja jb : list byte) (k64 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k24 k32 k80 s11v s7v s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s10v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 (Z_to_bv 64 (FB + 128)) k80 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 so4 ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawp <= p -> p <= END2 -> END2 <= rawp + rawlen ->
    BUDE hc Lc -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) (Z_to_bv 64 CRT) (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) s9v s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9ebc) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS Hp1 Hp2 Hp3 BE C24.
    open_cinv INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    assert (RINc : In (rawp, Z.of_nat (length rawjunk)) ((Lc ++ LB) ++ fdata LF')) by (apply in_app_iff; left; exact RIN).
    (* [comment removed for export] *)
    do 5 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 96) 1%nat as OPP.
    pose proof GETSIG as SPG. unfold x509_get_sig_stmtA, A_X509_GET_SIG in SPG.
    idtac "SIG-CALL".
    eapply (aevtA_cut_evtA_KF asegs R HIA hc mo0).
    { eapply SPG with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (SIGB := CRT + 696) (P := p) (END := END2) (BUF := rawp) (bs := rawjunk) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc; unfold X509_GET_SIG_STACK_A;
        first [ exact HHc | exact K14 | exact PC | exact RBY | exact ORAW | exact OPP | exact STlo | exact SS1 | exact MI | exact TPV | eassumption | reflexivity
              | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp3
              | match goal with |- ?g => idtac "SIG-LEFT:" g end ]. }
    cbv beta. intros ms2 PO. unfold x509_get_sig_postA in PO.
    ddestruct PO as (u0 & u1' & u2' & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3' & u4' & u5 & u6 & m2 & hq2 & rk & p2 & tg2 & len2 & q2
                    & -> & HH2 & Ehcs2 & Ehtop2 & Estk2 & Eflag2 & Evol2 & Efr2 & HKI2 & HP2 & MI2 & ST2 & SS2' & -> & Hrk & HPP2 & SG2 & Hp2' & HOK2).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2' by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0xa9ed0)) with (Z_to_bv 64 0xa9ed0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "SIG-BACK".
    pose proof (owns_pres hc Lc mg m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc HP2 MI2
                  ltac:(intros x k Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OW2.
    assert (SIP2 : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. exact (si_outside2 L SI (FB + 96) 8 (CRT + 696) 24 a ltac:(xl) ltac:(xl) Ha). }
    pres_call HP2.
    clear OW HHc PC K14 STlo SS1 MI SIP RBY ORAW OPP.
    presA_transport HP2.
    clear HP2 SPG.
    switch_h hc hq2 Ehcs2 Ehtop2 Estk2 Eflag2 HKI2.
    assert (BE2 : BUDE hq2 Lc) by (unfold BUDE in *; rewrite Evol2, Efr2; exact BE).
    idtac "SIG-SWITCHED".
    rename SG2 into K14. unfold buf_cells in K14.
    fold_cinv INV2 m2 hq2 Lc FSHB.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "SIG-ERR". ch_close m2. to_free.
        eapply free_walk with (Lc := Lc) (r := rk); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE2 | (clear - RS; lia) | (clear - Hrk; lia) | match goal with |- ?g => idtac "SIG-ERR-LEFT:" g end ]. }
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    { idtac "SIG-MISMATCH". ch_close m2. to_free.
      eapply free_walk with (Lc := Lc) (r := -8678); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE2 | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "SIG-MM-LEFT:" g end ]. }
    idtac "SIG-OK". ch_close m2.
    eapply exit3_walk with (Lc := Lc); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact C24 | (apply BUDE_X; exact BE2) | (clear - RS; lia) | match goal with |- ?g => idtac "SIG-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "04M0@C17025492443.416C17027589631.441D27847976046.416D27850073162.441D60109446735.416D60111543915.441L10195936580.3  L10390414532.3  L10441195418.379L10756207399.4  L10762723780.3  L11066751742.92 L13176305223.2  L14218488609.0  L15915253274.408L15971718799.92 L16115535586.380L16419906752.92 L17491248329.92 L17699354692.3  L17731163056.3  L18689686129.3  L19440707482.400L19979755003.71 L20319255321.6  L20328933496.92 L21218866939.2  L23513807686.2  L23723668098.3  L24619077828.3  L25185999684.3  L25435917806.3  L2544212042.379 L25695017930.381L26281185272.92 L26543722394.400L27386516966.1  L28723971319.92 L30108554588.92 L30830536376.2  L32454903270.1  L32516831197.3  L3276082884.3   L33554725375.6  L33563454112.92 L33685630497.92 L34783991938.3  L3517300250.381 L35655538583.72 L38235734261.1  L39220054468.3  L4037478596.3   L41409160545.3  L41559125372.378L41898327682.3  L43166046660.3  L48250362310.92 L48281719268.92 L49935039257.6  L49942751302.92 L50280382404.3  L51294782641.92 L51303916321.0  L52941874306.3  L53168208738.92 L54793161284.3  L55085943702.3  L5565789826.3   L57200105028.3  L58629977369.400L58788355611.92 L58790452773.92 L59516735962.92 L59953576447.6  L60056205954.3  L60754583113.0  L61323929028.3  L61402260511.92 L62695943706.408L63852571929.400L64686745924.3  L6899380056.1   L6906665613.1   L7382465640.1   L8793638983.75  L881835912.0    L9080482849.71  N23667955994.442N25297080393.442N26738689353.417N42129917801.417N4428092386.417 N45148972570.417N58551664354.442N63610817641.442O1476819786.441 O1478916974.416 O15264779972.416O15266877152.441O16212369554.416O16214466742.441O17025492443.416O17027589631.441O20456682336.441O20458779460.416O20679730144.441O20681827268.416O27923786227.441O28280334807.416O28722692754.416O28724789942.441O2882719044.416 O2884816224.441 O31540198097.416O34897012705.416O34899109829.441O35068890308.416O35070987488.441O3578431456.441 O3580528580.416 O37526595730.416O37528692918.441O39728539744.441O39730636868.416O4011621941.441 O4013719057.416 O40782554848.441O40784651972.416O45345472452.416O45347569632.441O50702732434.416O50704829622.441O51688520437.441O52246202948.416O52248300128.441O53955549892.416O53957647072.441O55957007968.441O55959105092.416O56414299794.416O56416396982.441O59623432085.441O59625529265.416O59804362208.441O59806459332.416O66178352992.441O66180450116.416O7499981970.416 O7502079158.441 O859936480.441  O862033604.416  P10189109219.416P10191206343.441P10395186759.441P10397283939.416P10759107399.441P10759843066.441P10761204579.416P10761940190.416P17685179107.416P17687276231.441P18674428118.416P18676525298.441P20325049568.416P21212095580.416P21214192760.441P23735738369.441P23737835557.416P24620663395.416P24622760519.441P25196956131.416P25199053255.441P3280854087.441 P3282951267.416 P33559471650.441P34787641857.441P34789739045.416P39214275427.416P39216372551.441P4031765091.416 P4033862215.441 P41419110342.416P41421207522.441P41903025153.441P41905122341.416P43151870819.416P43153967943.441P49930347716.441P50266205539.416P50268302663.441P52938159617.441P52940256805.416P54777977059.416P54780074183.441P55088519473.416P55090616597.441P5559018533.416 P5561115649.441 P57202738403.416P57204835527.441P59960354310.416P60050384933.416P60052482049.441P61334894435.416P61336991559.441P64680999907.416P64683097031.441Q12553905694.391Q12555934336.389Q13117060669.410Q14442946303.389Q14444731485.390Q15605678131.416Q15766564435.416Q15768661623.441Q17728908328.416Q17729184166.410Q18091871916.410Q18560453000.416Q18560730118.410Q19317499537.390Q22253784312.392Q26479617982.391Q26479650234.377Q26479650234.398Q26479650234.422Q26481777440.389Q26483600166.410Q27578952152.391Q27663313085.410Q28568008233.390Q29072138257.392Q33682020925.410Q34581021865.392Q34964382778.416Q34966479902.441Q35702753056.389Q35704929214.391Q38999185262.389Q42439168719.416Q42441265899.441Q43710715426.416Q44587234302.416Q44589331418.441Q45167231796.391Q46114361968.391Q46719263404.410Q46956692012.410Q48096960980.441Q48099058160.416Q48358016498.441Q48360113622.416Q49746198710.416Q49748295826.441Q53792675368.416Q53792955302.410Q56740915493.391Q57388114139.441Q57390211327.416Q57693235746.416Q60701411870.391Q60701509658.377Q60701509658.398Q60701509658.422Q60703585920.389Q60713813638.410Q6087524923.389 Q63205072776.416Q63205315078.410Q63327603398.389Q63761773619.416Q65947949610.389Q67038703949.416Q67040801129.441Q7095698621.410 Q7370434092.410 Q8417152989.392 Q8417341921.391 Q8699324297.416 Q8701421485.441 Q9085963896.390 Q9354431266.396 Q9354431266.421 Q9644583048.416 Q9646680236.441 00000100202404505U07407507608<08=08>08_08g08h09n0;90<H0<k0=R0=S0=^0=_0>e0@80@90B<0B=0BH0BI0BJ0BK0BV0C\0Db0FK0GQ0GU0H=0I`0Ia0Ie0J00J10J20L<0Mk0Ml0O20PJ0PN0PO0PP0PQ0Q`0Qa0Qb0SK0T20T30V60V70WC0WD0WE0Xg0Xh0Xi0Xj0Xk0Z10[Y0]A0]i0]j0]k0]l0]m0_]0`c0ai0aj0an0b30b70d70d80dQ0f80gW0i70jP0jQ0l90l:0mR0mS0mT0mU0mV0mW0mX0mY0mZ0m[0m\0m]0m^0m_0m`0ma0mb0mc0md0me0mf0mg0mh0mi0mj0mk0ml0mm0mn0mo0n00n10n20n30n40n50n60n70n80n90n:0n;0n<0n=0n>0n?0n@0nA0nB0nC0nD0nE0nF0nG0nH0nI0nJ0og11C12_14<15X17D18a1:N1;k1=G1>d1@@1Af1Ag1Ah1C?1DW1F41GP1Hm1JI1Ke1MB1No1PF1Q^1S;1TW1V41WP1Xh1Z?1[V1\n1^K1_g1aM1bj1dF1e]1g51hR1in1kH1la1n91oP20m22I24525M26d28A29]2;:2<V2>=2?d2@_2A^2B]2CX2E12FI2Ga2I92J42K[2MB2NA2O\2Q42RL2Sd2U<2VT2Wl2Xk2Yf2Yg2Zf2[a2[b2]V2_I2`a2b92c82dO2ee2f`2fa2fb2g]2h\2iW2jR2jS2jT2km2mG2nl30P31h33@34;35S36l37g39N3;53<\3>C3?j3AQ3BL3D33EZ3FY3GT3HO3JG3L>3M93N43O33P23Q_3SK3Tf3V;3WO3X^3YlFFS1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc3ap24rawp3so33ap17rawjunk3HTcS1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc2a33pp13pp24rawp7rawjunk3HTcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS2sp3CRT2bs2FB3sp12a37rawjunk3A3RS2lo3sp1SS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2sp3CRT2bs4CRT02FB3sp13SPR2F04SP1R6rawlen4rawp3so33ap17rawjunk2RS3HA14HA1'S2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkS2sp3CRT2bs2FB3sp13so37rawjunk4SO3RS2sp3CRT2bs2FB3sp14rawp3ap17rawjunk3HA1FS2c33so32KlFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1RFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk4HA1'3RA33RA4FS6rawlen2RSFFFS2a32b33Kl2S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp3so33ap17rawjunk4HA1'4RLENS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2FBS2sp3CRT2bs2FB3sp13pp14rawp7rawjunk4HPP1S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R2a33pp16rawlen4rawp7rawjunk5HPP1'3RA43A3R2b33pp25HPP2'3EL2SS2FBS2sp2lo3sp1FFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2a32b33pp26rawlen4rawp7rawjunk5HPP2'3RA33RA43EL2S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2c33ap26rawlen4rawp3so37rawjunk4HA2'4RLEN2ELFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2loFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp14LFB33CRB6LFB5126LFB5114LFB77rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2a33pp16rawlen4rawp7rawjunk5HPP1'4RLENS2sp3CRT2bs2FB3sp13ap24rawp7rawjunk3HA2FS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R2a33pp16rawlen4rawp7rawjunk5HPP1'3RA33RA4FS2sp3CRT2bs4CRT02FB3sp13SPR2F04SP1R2a33pp16rawlen4rawp7rawjunk2RS4HPP15HPP1'SFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp3so33ap17rawjunk4HA1'3RA44SO3R2c33ap24HA2'2ELFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc5STKc32sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS1R3NS14STKc5STKc32sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS2sp3CRT2bs2FB3sp13pp24rawp7rawjunk4HPP2FFSFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R2a32b33pp26rawlen4rawp7rawjunk5HPP2'4RLEN3EL2S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2FBS3CRTS2FBS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSS2sp3CRT2lo2bs2FB3sp13SP1S1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk4SBND3x471CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk3x471CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunk3x271CS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunk3x271CFS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunk4SBND3x271CFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk3x471CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB72a33pp13pp26rawlen4rawp7rawjunk4RLEN3RA4S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB73ap26rawlen4rawp3so33ap17rawjunk4RLEN3RA4S2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB73ap26rawlen4rawp3so33ap17rawjunk4HA1'3RA32PLFFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72a33pp12b33pp26rawlen4rawp7rawjunk5HPP2'3RA33EL22QLS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp26rawlen4rawp7rawjunk5HPP1'3RA32PLS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB72c33ap26rawlen4rawp3so33ap17rawjunk4HA2'3RA32EL2QLS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunk5HTOPcS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk5HTOPcS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB73ap24rawp3so33ap17rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB72a33pp13pp24rawp7rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 ABCMP NA1 DIMG HMND GETSIG STKcf CRTFREE STKc1 STKc2 STKc3 STKcfr CNTj0 CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_CMP : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END2 : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 : word) (pp2 : Z) (c1 c2 c3 : word) (ap2 : Z) (w0 w1 w2 : word) (ja jb : list byte) (k64 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k24 k32 k80 s11v s5v s7v s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 (Z_to_bv 64 pp2) c1 c2 c3 (Z_to_bv 64 ap2) w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) k64 (Z_to_bv 64 (FB + 128)) k80 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawp <= p -> p <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen -> rawp <= ap2 -> ap2 + bv_unsigned c3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    ((pp2 = 0 /\ bv_unsigned b3 = 0) \/ (rawp <= pp2 /\ pp2 + bv_unsigned b3 <= rawp + rawlen)) ->
    BUDE hc Lc -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) s5v (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 (FB + 96)) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9dcc) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS Hp1 Hp2 Hp3 HA1 HA1' HA2 HA2' HPP1 HPP2 BE C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    pose proof (bv_unsigned_in_range 64 so3) as SO3R. unfold bv_modulus in SO3R. cbn [Z.pow Z.of_N Pos.pow] in SO3R.
    pose proof (bv_unsigned_in_range 64 a3) as A3R. unfold bv_modulus in A3R. cbn [Z.pow Z.of_N Pos.pow] in A3R.
    (* [comment removed for export] *)
    do 9 zstep.
    zstep. if_cases Kl; zify_cond Kl.
    { idtac "CMP-LEN1". refold_mu INV2 OW2 hc Lc FSHB. to_free.
      eapply free_walk with (Lc := Lc) (r := -9856); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "CMP-L1-LEFT:" g end ]. }
    assert (EL : bv_unsigned c3 = bv_unsigned so3) by (clear - Kl; first [lia | congruence]).
    (* [comment removed for export] *)
    do 10 zstep.
    idtac "CMP-BCMP1".
    bcmp_call ap1 ap2 (bv_unsigned so3) ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS HA1 HA1' HA2 HA2' EL SO3R).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "BCMP1-LEFT:" g end.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_cases Kb1; zify_cond Kb1.
    2:{ idtac "CMP-OID". refold_mu INV2 OW2 hc Lc FSHB. to_free.
        eapply free_walk with (Lc := Lc) (r := -9856); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "CMP-OID-LEFT:" g end ]. }
    clear Kb1.
    (* [comment removed for export] *)
    do 5 zstep.
    zstep. if_cases Kt; zify_cond Kt.
    { idtac "CMP-TAG". refold_mu INV2 OW2 hc Lc FSHB. to_free.
      eapply free_walk with (Lc := Lc) (r := -9856); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "CMP-TAG-LEFT:" g end ]. }
    clear Kt.
    (* [comment removed for export] *)
    do 4 zstep.
    zstep. if_cases Kl2; zify_cond Kl2.
    { idtac "CMP-LEN2". refold_mu INV2 OW2 hc Lc FSHB. to_free.
      eapply free_walk with (Lc := Lc) (r := -9856); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "CMP-L2-LEFT:" g end ]. }
    assert (EL2 : bv_unsigned b3 = bv_unsigned a3) by (clear - Kl2; first [lia | congruence]).
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { idtac "CMP-NOPAR". refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_SIG with (Lc := Lc) (END2 := END2); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | exact C24 | eassumption | match goal with |- ?g => idtac "CMP-NP-LEFT:" g end ]. }
    assert (A3NZ : bv_unsigned a3 <> 0) by (clear - Kz A3R; intros E; apply Kz; rewrite E; reflexivity).
    destruct HPP1 as [[_ HPP1]|[HPP1 HPP1']]; [exfalso; exact (A3NZ HPP1)|].
    destruct HPP2 as [[_ HPP2]|[HPP2 HPP2']]; [exfalso; rewrite EL2 in HPP2; exact (A3NZ HPP2)|].
    (* [comment removed for export] *)
    do 5 zstep.
    idtac "CMP-BCMP2".
    bcmp_call pp1 pp2 (bv_unsigned a3) ltac:(xl RLEN RA1 RA2 RA3 RA4 RP RL RS HPP1 HPP1' HPP2 HPP2' EL2 A3R).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "BCMP2-LEFT:" g end.
    (* [comment removed for export] *)
    zstep. if_cases Kb2; zify_cond Kb2.
    { idtac "CMP-OK". refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_SIG with (Lc := Lc) (END2 := END2); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | exact C24 | eassumption | match goal with |- ?g => idtac "CMP-OK-LEFT:" g end ]. }
    idtac "CMP-PAR". refold_mu INV2 OW2 hc Lc FSHB. to_free.
    eapply free_walk with (Lc := Lc) (r := -9856); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "CMP-PAR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06T0@C15777618515.419C17025492443.417C18971418195.418C21480694355.420D11880987239.390D11891817072.420D27847976046.420D28929042544.420D28935055463.390D29432549735.420D35633533417.390D42035635047.420D42945678569.390D60098780760.390D60109446735.420D63540507760.420D63546389607.390D7733626345.390 D9646919015.420 K10562283215.420K10929873871.420K11135951439.420K1396569935.420 K21101599439.420K216607946.420  K22555980111.420K22861045682.420K23131760207.420K24193256114.420K24981273935.420K26482584271.420K26863261647.420K2746063951.420 K27831563215.420K29092442063.420K30038940111.420K30419638991.420K32474697807.420K33593216207.420K35327088335.420K35503804751.420K36205691343.420K3624144719.420 K38883460559.420K39763653839.420K40707548879.420K41090868175.420K42234285647.420K42440362191.420K44470506575.420K4568054095.420 K45998849999.420K46700211279.420K47274404815.420K49918619599.420K51948751695.420K53683150159.420K57240043599.420K57414664911.420K58694434511.420K58872734415.420K59270213583.420K59594197450.420K61213550026.420K6218661554.420 K6302434127.420 K65056271055.420K7008007119.420 K8908368463.420 K9652221903.420 L10195936580.3  L10390414532.3  L10544667366.71 L10557730137.2  L10756207399.4  L10762723780.3  L10934364249.2  L11123599833.2  L11183176311.1  L12731014519.1  L13176305223.2  L13299672782.10 L1408793817.2   L15522417010.88 L1615798205.2   L16463381879.1  L16991276653.3  L17699354692.3  L18302214263.1  L18689686129.3  L19979998541.88 L204253020.2    L20517150065.3  L20929851427.17 L21089309017.2  L21218866939.2  L21650528252.385L22488409818.17 L22560471769.2  L22866772043.3  L23119474137.2  L23513807686.2  L24200041803.3  L24619077828.3  L24968328921.2  L25160623805.2  L25185999684.3  L25268991853.17 L26295235211.88 L26486612313.2  L26864420208.71 L26875616345.2  L27036101880.2  L27386516966.1  L2741508057.2   L27819145305.2  L29105251417.2  L29345674871.1  L30042772057.2  L30288275819.88 L30431990105.2  L30603190416.71 L30893447543.1  L31165784101.377L31569831019.88 L31675618311.71 L32327136116.1  L32454903270.1  L32470277081.2  L32516831197.3  L3276082884.3   L32973469363.2  L33597048665.2  L33817424237.3  L3482806040.88  L35323190617.2  L35425629300.1  L35516619481.2  L35589735568.387L35655538583.72 L35894024561.3  L36217981529.2  L3636561113.2   L36460502135.1  L38235734261.1  L38879563353.2  L3901628532.1   L39220054468.3  L39776468825.2  L40228640085.0  L4037478596.3   L40692963805.88 L40711908697.2  L41103222873.2  L41262276743.88 L41409160545.3  L41853517931.88 L41898327682.3  L42238313945.2  L42435937113.2  L4266075271.88  L42930873993.386L43166046660.3  L43571151479.1  L44466151385.2  L4572017369.2   L45994423385.2  L46695786457.2  L47261655129.2  L47290354355.2  L48487939594.88 L48853470583.1  L49037485618.88 L49922974809.2  L50280382404.3  L5080665970.88  L51953172697.2  L52941874306.3  L52997342583.1  L53670729433.2  L54135518087.88 L54274957729.0  L54793161284.3  L55085943702.3  L55968330615.1  L5618218871.1   L57200105028.3  L57227103193.2  L5724020363.88  L57427085657.2  L57431586522.8  L57798807159.1  L58698265945.2  L58885089625.2  L58999671816.17 L59257267289.2  L59284234861.3  L59308586248.2  L59606483548.2  L60056205954.3  L60754583113.0  L61209128540.2  L61323929028.3  L61366595865.377L6220259659.3   L6297880793.2   L63199674356.410L63277261175.1  L63685833661.2  L64418367100.88 L64584198252.2  L64586655724.3  L64686745924.3  L6487220337.3   L65051713881.2  L65289245065.395L65556712137.377L67011971447.1  L67367117072.88 L6899380056.1   L6906665613.1   L7003453529.2   L7382465640.1   L7480812975.71  L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.88  L9258496882.88  L9656646745.2   N13520806443.418N14415960011.418N38327509834.418N41798350943.418N45047156712.418N51078381008.418O10221831037.420O10618990077.420O11746403965.420O11930563540.417O120999933.420  O12201444514.420O12444470238.416O13347995810.420O13386885170.420O14612200573.420O1478916974.420 O15264779972.420O15720361950.416O15982681725.420O16350966909.420O17025492443.417O17344772093.420O17494624509.420O18257958781.420O18626760061.420O19357757918.416O19423669245.420O19770425853.420O20458779460.420O20681827268.420O20935596669.420O23566745469.420O23613219284.417O23763636349.420O2430354685.420 O25647190909.420O25709147736.420O28166615549.420O2882719044.420 O31164956925.420O32537874520.420O33684383613.420O34031148413.420O34604356221.420O34897012705.420O35068890308.420O35592798351.420O3580528580.420 O36460395570.420O36879657853.420O37141200340.417O37526595730.418O3800868605.420 O39730636868.420O4013719057.420 O40348445053.420O40463046306.420O40784651972.420O41843596285.420O43344705661.420O4520256088.420 O45345472452.420O46784099837.420O49059365629.420O4949261181.420 O50434075901.420O50702732434.417O50817538813.420O5162933373.420 O52246202948.420O5312795005.420 O53955549892.420O54023336829.420O55959105092.420O56414299794.417O58965929341.420O59625529265.417O59806459332.420O60340604797.420O60687394173.420O62603269117.420O62615880829.420O62937682575.420O63760603389.420O63904362034.420O64128366333.420O66180450116.420O68536837775.420O7239741565.420 O7590719101.420 O862033604.420  P10189109219.420P10397283939.420P10761204579.420P10761940190.420P1621609754.420 P16981335242.417P17685179107.420P18674428118.420P20501893078.416P21212095580.417P24620663395.420P25154843674.420P25196956131.420P3282951267.420 P32977370405.420P33810555850.417P35896658902.416P39214275427.420P4031765091.420 P41419110342.417P41905122341.418P43151870819.420P47286321445.420P50266205539.420P52940256805.417P54777977059.420P55088519473.420P57202738403.420P59281600714.417P60050384933.417P61334894435.420P63670608154.420P64680999907.420P6480458454.416 P8754630693.420 Q12557789047.385Q12561180017.420Q12919288279.386Q15766564435.420Q16472810971.420Q19546672262.385Q19546885610.387Q19561563123.386Q21832736479.420Q24582061175.386Q25433616535.420Q25805880151.385Q25805880151.386Q26479650234.374Q26479650234.407Q2686142842.386 Q30616888669.386Q30617628407.385Q30617628407.386Q30772847459.387Q33854476887.385Q34337489304.420Q34964382778.420Q35717135063.385Q39439682456.420Q42439168719.420Q42637231095.385Q44587234302.420Q46654714335.420Q47957748593.420Q48099058160.420Q48118064779.420Q48360113622.420Q49746198710.420Q50244178959.385Q53792986711.385Q56701219185.420Q57390211327.420Q58032317.420   Q58743871165.420Q58743905100.385Q58743905100.386Q5938316251.420 Q59916857.386   Q60045073559.420Q60701509658.374Q60701509658.407Q62200790424.420Q63205285879.385Q67038703949.420Q68121507803.420Q7095191584.387 Q7095698621.420 Q8194583007.420 Q8362820247.420 Q8699324297.420 Q9356887981.390 Q9634015756.386 Q9644499989.387 Q9644549497.385 Q9644583048.420 00000400500900=01C02I04:05@06F07L08R09X0:^0;m0=<0>B0?H0@N0AT0BW0CZ0D]0E`0Fc0Gf0Hi0J90K<0LL0MO0NR0OU0PX0Q[0R^0Sa0Td0Ug0Vj0Wm0Y00Z30[60\90]<0^?0_B0`E0aH0bK0cN0dQ0eT0fW0gZ0h]0i`0jc0kf0li0ml0no10211512E13H14K15N16Q17T17U17V17h17i17j17k17l17m18118518=18N18O19]19^19_19`19a19b19c1;>1;?1;@1<01<11<21=81=T1=U1=V1=W1=b1=c1=d1=e1=f1=g1>W1?41?51?G1?H1?I1?M1?N1?O1?P1?T1?U1@71@81A<1A@1CM1Co1E81E<1E@1EA1EL1EM1EN1EO1EP1F`1Fa1Fe1Ff1Gl1ID1IE1IF1IG1IK1IO1IP1IT1IU1IV1IW1IX1K=1K>1K?1KY1KZ1L<1L=1L>1L?1LY1M_1M`1Md1Me1Mf1Mg1Mh1Mi1Mj1O01O41P\1P]1P^1Ql1Qm1Qn1Qo1R01RJ1RK1RL1RM1RQ1RU1RV1RW1S41S51ST1SX1SY1SZ1Sm1Sn1So1T51T61T71T81T91T:1U@1UA1UB1UC1UG1UH1Vo1W71W81W91W:1W;1XF1ZS1ZW1\N1\R1\W1\X1\\1^W1^X1`X1`Y1`Z1a31aP1b^1b_1cg1dh1ei1g81hO1hP1hQ1hR1hS1hT1hU1hV1hW1hX1hY1hZ1h[1h\1h]1h^1h_1h`1ha1hb1hc1hd1he1hf1hg1hh1hi1hj1hk1hl1hm1hn1ho1i01i11i21i31i41i51i61i71i81i91i:1i;1i<1i=1i>1i?1i@1iA1iB1iC1iD1iE1iF1iG1iH1iI1iJ1iK1iL1iM1iN1iO1iP1iQ1iR1iS1iT1iU1iV1iW1iX1iY1iZ1i[1i\1i]1i^1i_1i`1ia1ib1ic1id1ie1if1k21l>1mJ1nk20Y21`22l24825`25a26m28U29a2:m2<M2=T2?B2@N2AZ2Ba2Ch2E42FT2G`2Hg2J32K<2LH2MO2NV2Ob2QJ2RV2TD2Ud2WK2WL2Xd2Yl2Ym2[=2\M2]]2^X2`?2`@2aX2c02dH2e`2f[2gV2i=2jd2k_2m72n22oU30m31h32n34U34V35Q35R35S37638?39S3:N3;f3;g3<o3=j3>e3?`3@[3@\3AW3AX3C?3Df3Ea3GH3Ho3I03Ik3Jf3Ka3Kb3M>3NB3O@3P>3Q<3R:S2FBFS2FBS2FBS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkFFS2sp3CRT2bs2FB3sp1FFFFFS2FBS2FBS2lo3sp1S2rk3Hrk1r2Kr1q1HFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFFFFFFS1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFFS4END14END26rawlen4rawp3Hp32p23x393pp24Hp2r4HPP2FFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS4END14END24rawp3Hp12p24Hp2rFFFS6rawlen2RSFFFFFS4END14END26rawlen4rawp3Hp32p23x353ap24Hp2r4HA2'S2sp3CRT2bs2FB3sp12F07rawjunkFS2sp3CRT2bs2FB3sp1FSS2FBFFFS2FBFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1RS2FBS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END26rawlen4rawp7rawjunk2RP3Hp13Hp24Hp2'3Hp33RA4S2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkS1R3NS14STKc5STKc12sp3CRT2lo3slo2bs4CRT04SLOL2FB3sp13SP13SPR2F04SLOu4SP1RS2FBS2FBFS2sp2lo3sp1FFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS2FBFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcFFFS2FBS2loFS2FBFFSFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END26rawlen4rawp7rawjunk3Hp34RLENFFS2sp3CRT2bs2FB3sp17rawjunkFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFFFS2sp3CRT2bs2FB3sp17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS2FBFFFFFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBS1R3NS14STKc5STKc22sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFFFFS2sp3CRT2bs2FB3sp17rawjunkSFFS2FBS2FBFFS2sp3CRT2bs2FB3sp12F07rawjunkFS1R3HIA2sp3sp13SP12hc4OSAt4OSApS2FBFFS4END14END22p24Hp2rFFS1i2HiFFSFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFFS2FBFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S2rk3HrkFFFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk1i2HiS1R2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT02FB3sp13SPR3ACV2F04SP1R4LFB36LFB5126LFB5114LFB71p4END14END26rawlen4rawp7rawjunk2RP3Hp13Hp24Hp2'3Hp33RA4S2FBS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBS3CRTFS2FBS1R3NS14STKc5STKc12sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13SP14SP1M3APC3SPR3ALO3ACV2F03APB4SLOu4SP1RFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND1a2DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkFS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3x411CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x411CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x411CS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x411CS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x411CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13ALO4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA4S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R2LF4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 ABCMP NA1 DIMG HMND XALG GETSIG STKcf CRTFREE STKc1 STKc2 STKc3 STKcfr CNTj0 CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPH TPV LOS DCD BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_END : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) (k32 : word)
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word) (eo : ext_own) (ej : ext_junk)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k24 k80 s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v s7v s11v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 k32 (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) k80 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
    chunks asegs mm CRT ob h1 h2 h3 rawlen rawp tbt tbd tbl tbp ver verpad stg spd slen sq so1 so2 so3 (Z_to_bv 64 ap1) ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4
           ij48 inext img ipad sj48 snext smg spad dates pr1 pr2 pr3 pr4 pkinfo pkctx u1 u2 u3 u4 v1 v2 v3 v4 eo ej gtg gpd glen gq sigmd sigpk sigopts ->
    owns asegs PK mm (Lc ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts rawjunk ->
    Permutation Lc (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo sigopts)) ->
    (rawp = 0 \/ ob = Z_to_bv 64 1) ->
    0 < rawp -> 0 < rawlen -> rawlen < 2^30 -> rawp <= p -> p <= END1 -> END1 <= END2 -> END2 <= rawp + rawlen ->
    rawp <= ap1 -> ap1 + bv_unsigned so3 <= rawp + rawlen ->
    ((pp1 = 0 /\ bv_unsigned a3 = 0) \/ (rawp <= pp1 /\ pp1 + bv_unsigned a3 <= rawp + rawlen)) ->
    BUDE hc Lc -> cnt24 (Lc ++ LB) <= cnt24 LB + 2 * (blen / 5889) ->
    aevtA asegs (KF asegs R HIA hc mo0) POST
      (MS (mkR x1 (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) s5v (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 (FB + 96)) s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9d94) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 BE C24.
    open_cinv_mu INV hc. ch_open CH.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    assert (RINc : In (rawp, Z.of_nat (length rawjunk)) ((Lc ++ LB) ++ fdata LF')) by (apply in_app_iff; left; exact RIN).
    (* [comment removed for export] *)
    do 3 zstep.
    zstep. if_cases Ke; zify_cond Ke.
    2:{ idtac "END-MM". refold_mu INV2 OW2 hc Lc FSHB. to_free.
        eapply free_walk with (Lc := Lc) (r := -8678); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear; lia) | match goal with |- ?g => idtac "END-MM-LEFT:" g end ]. }
    assert (EP : p = END1).
    { clear - Ke Hp1 Hp2 Hp2' Hp3 RP RA4 ACV. rewrite ?Z.mod_small in Ke by lia. first [exact Ke | lia]. }
    clear Ke. subst p.
    (* [comment removed for export] *)
    do 5 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP. frame_aobj FSH (FB + 256) 3%nat as OALG. frame_aobj FSH (FB + 192) 3%nat as OPAR.
    pose proof XALG as SPA'. unfold x509_get_alg_stmtA, A_X509_GET_ALG in SPA'.
    idtac "END-CALL".
    assert (OSA : aobj asegs AL (hcs asegs R HIA hc) mm (sp1 - 88) 8).
    { pose proof (hm_top asegs R HIA hc _ _ _ HHc) as OSAt. pose proof (hcs_stack asegs R HIA hc) as OSAs.
      pose proof TOP as OSAp. rewrite <- HTc in OSAp.
      lazymatch goal with SSx : sshad _ _ mm slo sp1 |- _ => pose proof SSx as OSAy end.
      destruct OSAy as (_ & _ & OSAg).
      change 8 with (8 * Z.of_nat 1).
      eapply aobj_of_zero_shadow with (B := sp1 - 88) (g0 := 0%nat) (cs := [C1 (Z_to_bv 8 0)]);
        [ exact (hcs_ok asegs R HIA hc)
        | eapply crange_sub; [ exact OSAs | xl | first [ clear - SP1 OSAp OSAt; lia | match goal with |- ?g => idtac "OSA-HI-LEFT:" g end ] ]
        | xl | xl | apply OSAg; xl | intros i Hi; destruct i as [|i]; [reflexivity | lia] ]. }
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPA' with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (ALG := FB + 256) (PAR := FB + 192) (P := END1) (END := END2) (BUF := rawp) (bs := rawjunk) (lo := lo);
         rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc;
         first [ exact HHx | exact RBY | exact ORAW | exact OPP | exact OALG | exact OPAR | exact LOS | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
               | match goal with |- ?g => idtac "END-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "END-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -12288 < ?r <= 0 |- _ => subst x; rename r into rk; rename H0 into Hrk end.
    match goal with H : END1 <= ?q <= END2 |- _ => rename q into p2; rename H into Hp2r end.
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "END-ERR". refold_mu INV2 OW2 hc Lc FSHB. to_free.
      eapply free_walk with (Lc := Lc) (r := rk); first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | (clear - RS; lia) | (clear - Hrk; lia) | match goal with |- ?g => idtac "END-ERR-LEFT:" g end ]. }
    r_zero Kr Hrk. ddestruct (POST R0) as (ap2 & pp2 & -> & -> & HA2 & HA2' & HPP2). clear POST.
    idtac "END-OK". refold_mu INV2 OW2 hc Lc FSHB.
    eapply S_CMP with (Lc := Lc) (END2 := END2) (p := p2) (ap1 := ap1) (ap2 := ap2) (pp1 := pp1) (pp2 := pp2);
      first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact BE | exact C24 | eassumption
            | (clear - Hp2r Hp1 Hp2 Hp2' Hp3 HA2 HA2' HPP2; lia) | match goal with |- ?g => idtac "END-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation BUDK hc Lc a := (BUD hc Lc (KVc blen) (KFc blen d) (2 + CNTk) a).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03?0@D11881018327.389D20225638161.424D42945709401.389D43026960606.389D52045935499.422D53340075670.424D60136771218.389D6203691829.422 D64348882538.424L11183176311.1  L12629679261.2  L13471114893.1  L13545754800.13 L1408793817.2   L1540615640.71  L15522417010.89 L16600731020.1  L17401779853.1  L17570011486.89 L19979998541.89 L204253020.2    L20958157709.1  L21153814797.1  L21564613915.71 L21652623661.380L22969180879.3  L23119474137.2  L23513807686.2  L23766154372.402L24373605877.6  L24516627597.1  L24896682419.89 L25160623805.2  L26486612313.2  L26857285789.2  L26875616345.2  L26983613546.4  L27386516966.1  L27877486605.1  L28073013645.1  L28631860810.367L29345674871.1  L30042772057.2  L30431990105.2  L31388357250.2  L31863041268.89 L32145072831.2  L32327136116.1  L32454903270.1  L32698878355.1  L33597048665.2  L34359762549.89 L3482806040.89  L35560182413.1  L35655538583.72 L36408883172.89 L36449969418.89 L36460502135.1  L37622627047.5  L38235734261.1  L39080257185.0  L40281191306.3  L40711908697.2  L41103222873.2  L42300624269.1  L43026799353.1  L43139882429.11 L43571151479.1  L44053439528.3  L44466151385.2  L4572017369.2   L48950416541.2  L53733269133.1  L5436592646.13  L5519046301.2   L55224207780.3  L55225352820.2  L55704336417.89 L57096077837.1  L57798807159.1  L58885089625.2  L59256235615.13 L59257267289.2  L59308586248.2  L5942126123.2   L5969266061.1   L60136735925.1  L60754583113.0  L60915193550.89 L6162694925.1   L62589838554.11 L6487220337.3   L65828716141.89 L66267913757.71 L67123663005.2  L67534628802.2  L6899380056.1   L6906665613.1   L7382465640.1   L8113154630.89  L8742280115.2   L8896078297.2   L9080482849.71  L9241280651.89  L9721181197.1   L9887797032.3   P12631710506.422P1406761838.422 P14832636600.422P202219755.422  P22141058872.422P23121504878.422P26027241286.422P26484451054.422P26859319082.422P26873453550.422P29449378744.422P30040741358.422P30285671757.422P30429828846.422P33007851192.422P33142131014.422P33380158392.422P33599209710.422P34494421193.422P40714070766.422P41101062126.422P426298424.422  P44185674566.422P44463986798.422P4574049646.422 P46849744041.422P47607750584.422P47803276856.422P48948384554.422P51359649080.422P54467790662.422P5516882218.422 P58668067256.422P58887122670.422P59259429870.422P62226539704.422P62792325176.422P65782830008.422P67121501994.422P67532595317.422P7852092230.422 P8495984312.422 P8893916782.422 Q12631710506.422Q12933969670.380Q13195388474.374Q1406761838.422 Q1432898026.412 Q15985628819.424Q16952477917.375Q16956667493.374Q19561351767.380Q19561614678.422Q202219755.422  Q22969957449.422Q23121504878.422Q24592546470.380Q24852141958.380Q24980061172.374Q25161431099.422Q25389680632.375Q25816366470.380Q26481467398.380Q26484451054.422Q2676383091.424 Q26859319082.422Q26873453550.422Q27284014172.374Q30040741358.422Q30429828846.422Q30602946598.380Q32145059102.422Q33599209710.422Q3853027959.412 Q40714070766.422Q41101062126.422Q44463986798.422Q4574049646.422 Q48656971674.374Q48948384554.422Q50233692894.380Q53577456718.422Q54692961830.380Q5516882218.422 Q55613122833.375Q58746002845.380Q58887122670.422Q59259429870.422Q5941360813.422 Q60668056454.380Q60703362470.380Q6203691829.422 Q6486982391.422 Q6530085414.380 Q67121501994.422Q67532595317.422Q68266706017.422Q8744442884.422 Q8893916782.422 Q9633801385.422 Q9634063272.380 00001602E03K04Q05_06n08409>0:M0:Q0:R0:W0;K0;L0;b0=00=50=:0>a0@<0@=0@B0@G0@_0Ae0Af0Ag0B20B30BE0BJ0Bm0Bn0Bo0C00C10C>0CB0CG0CL0DJ0DN0DO0DP0DV0Ed0Ee0Ei0Em0F30F40FV0Gf0Gk0IC0Jj0L00L40LE0LI0LJ0LS0LT0LU0LZ0L_0Ln0M20M>0M?0M@0MA0MF0N:0N;0N<0ND0On0P30P70P80Ph0Pi0Po0Q00Q50Q:0Q;0Rj0Ro0SG0SH0Sf0T>0T?0T@0TD0TI0TM0Ug0Uh0Ui0VB0V_0Vd0Vl0X30Y:0Zk0\20]c0^j0`V0a]0bd0ck0e\0fc0h30i:0jk0lW0nH0oO11;12B13I15:16f17m1941:e1<V1>G1?N1A?1C11D81Ei1G01H71Ih1KY1MJ1NQ1OX1QD1S51T<1T=1UU1Ve1Vf1X31X41Xk1Yb1[21\F1\G1^81^91_`1a81ao1c[1dn1fF1g^1g_1hc1hd1he1i\1i]1i^1kE1ln1lo1nV1nW1nX1nY1nZ20920:21522823_23`24W25R25S25T27E28]2:D2;G2=92>`2>a2>b2@=2Aa2Ab2Bd2CbS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBe1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBe1x2HxS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBe1x2HxS2FBFS3CRTS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFS2sp3CRT2bs2FB3sp13SP1S2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS3CRTS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S1R3HIA1h2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3TOP2FB3sp13SP13APC3SPR2F03APB4SP1R7rawjunkFS3CRTS3CRTS1R2sp3CRT2bs2FB3sp13FDDS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFFS6rawlen2RSFS3CRT2FB1x1k2Y12Y2S3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkFFFFS1p1a4rawp2HAS2FBS3CRTS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2FBFFS4blenS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB3SPH2FB3sp13SP13APC3SPR2F03APB7rawjunkFS2FBS2FBS4CNTkFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkS3CRTS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2S1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S2FBS2FB1x2NF3CRT3Hx1S2loSS1R3HIA1hFFS3CRTS3CRTS1p4END12p43Hp4S2FBS1p4END13Hp2FFFS3CRTS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFFS2rc3Hr3S1R4STKc5STKxx5STKcx2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB2FB3sp13SP13APC3SPR2F03APB4SLOu4SP1R7rawjunkS3CRTS2FBFS4blen1p4END14END21a6rawlen4rawp3RBL4Hp2'3Hp32HAFS1i2HiFS3CRTS3CRTSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS3CRTS1p4END14rawp3Hp12p43Hp4FS2sp3CRT2bs2FB3sp13APC7rawjunkS1R2sp3CRT2bs3DCD2FB3sp1FFS2FBS3CRTS2FBS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen7rawjunk2RS4RLENFFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS3CRTS4blen1dS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunk3LBeFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcFS2LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3LBeFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunk3LBeFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcFS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3LBe1c2HcFFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeFFFFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7FS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFFS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB4LFB36LFB5126LFB5114LFB72hc7rawjunk3HSc5HTOPc3LBeS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk3LBeFS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk3LBeS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 ABCMP NA1 DIMG HMND XALG GETSIG PHIx FFRx CNTx STKxx CRTEXT STKcf CRTFREE STKc1 STKc2 STKc3 STKcx STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIx_le FFRx_le CNTx_le CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_EXT3 : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k24 k80 s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v s7v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) k80 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
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
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) s5v (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9d60) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 BK HA C24.
    pose proof INV as INV0. pose proof CH as CH0.
    open_cinv INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 5 zstep.
    idtac "EXT-V".
    zstep. if_cases Kv; zify_cond Kv.
    { idtac "EXT-SKIP".
      eapply S_END with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1);
        first [ exact INV0 | exact CH0 | exact OW | exact PERM | exact HOB | exact C24 | eassumption
              | (eapply BUD_E; [exact BK| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia])
              | match goal with |- ?g => idtac "EXT-SKIP-LEFT:" g end ]. }
    clear Kv INV0 CH0.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 6 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    frame_aobj FSH (FB + 96) 1%nat as OPP.
    pose proof (uwc_callee hc mg PRES HSc SAVE) as UWF.
    destruct (BUD_pre hc Lc _ _ _ a (END1 - p) PHIx FFRx BK ltac:(clear - HA; lia) ltac:(clear - Hp2; lia) ltac:(clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia)
                ltac:(clear; lia) ltac:(clear; lia) PHIx_le FFRx_le) as [BPV BPF].
    pose proof (HMND _ _ _ _ HHc) as NDLc.
    assert (XZ : rw_cells asegs mg (CRT + 424) [CB 272 (zeros 272)]).
    { eapply rw_cells_reshape; [exact K13| cbn; split; [reflexivity| exact I] | vm_compute; reflexivity]. }
    idtac "EXT-CALL".
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CRTEXT with (h := hc) (LB := Lc ++ LB) (LF := LF') (PP := FB + 96) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (CRT := CRT) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HTc, ?HSc; unfold EXT_SIZE;
        first [ exact HHc | exact HK1 | exact PC | exact XZ | exact UWF | exact BPV | exact BPF | exact NDLc | exact RBY | exact RIN | exact OPP | exact STlo | exact SS1 | exact MI | exact TPV
              | exact ALC | exact CRT0 | eassumption | reflexivity
              | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
              | match goal with |- ?g => idtac "EXT-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4' & q5' & q6' & m4 & mo4' & hq3 & rc & p4 & eo1 & ej1 & LBe
                    & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp4 & HEXT4 & EOK4 & PERMe & HH4).
    injection E4 as Ems Emo. subst ms4 mo4 qa0.
    replace (ret_pc (Z_to_bv 64 0xa9d90)) with (Z_to_bv 64 0xa9d90 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold EXT_SIZE in HP4.
    idtac "EXT-BACK".
    pose proof (owns_pres hc Lc mg m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc HP4 MI4
                  ltac:(intros x k Y1 Y2 Y3 Y4; cbn [disjoint_from]; clear - Y1 Y2; lia)) as OWt.
    assert (SIP4 : si_P SI m4).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|].
      intros x Hx. exact (si_outside2 L SI (FB + 96) 8 (CRT + 424) 272 x ltac:(xl) ltac:(xl) Hx). }
    pres_call HP4.
    pose proof (BUD_post hc hq3 Lc LBe _ _ _ a (END1 - p) PHIx FFRx CNTx BK ltac:(clear - HA; lia) ltac:(clear - Hp2; lia) PHIx_le FFRx_le CNTx_le HV3 HFR3 HCNT3) as BK3.
    clear OW HHc PC K13 XZ STlo SS1 MI SIP RBY ORAW OPP.
    presA_transport HP4.
    clear HP4.
    apply (aevtA_enter asegs (KF asegs R HIA hq3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
    switch_hm hc hq3 HCS3 HT3 HS3 HF3.
    rewrite app_assoc in HH4, EOK4.
    (* [comment removed for export] *)
    assert (PERM1 : Permutation (LBe ++ Lc) (crt_blocks (f_of ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo1 sigopts))).
    { rewrite crt_blocks_f_of. rewrite crt_blocks_f_of in PERM. change (ext_blocks ext_own_zero) with (@nil blk) in PERM. cbn [app] in PERM.
      eapply Permutation_trans; [apply Permutation_app; [exact PERMe| exact PERM]|]. perm_front. }
    assert (OW1 : owns asegs PK m4 ((LBe ++ Lc) ++ LB) CRT ob rawlen rawp inext inodes snext snodes pkinfo pkctx pkowned eo1 sigopts rawjunk).
    { pose proof (owns_grow hq3 LBe Lc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ OWt PERM HH4 MI4) as OWg.
      unfold owns, crt_own_ok in OWg |- *. ddestruct OWg as (C1 & C2 & _ & _ & _ & _ & C7 & C8 & C9 & C10). ddestruct EOK4 as (E1 & E2 & E3 & E4).
      cbn [f_of co_issuer_next co_issuer co_subject_next co_subject co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts co_rawp co_rawlen co_pkinfo co_pkctx co_pkowned cj_raw jraw] in C1, C2, C7, C8, C9 |- *.
      refine (conj C1 (conj C2 (conj E1 (conj E2 (conj E3 (conj E4 (conj C7 (conj C8 (conj C9 _))))))))).
      exact (nodup_of_perm hq3 (LBe ++ Lc) m4 _ HH4 PERM1). }
    assert (C241 : cnt24 ((LBe ++ Lc) ++ LB) <= cnt24 LB + 2 * (blen / 5889)).
    { rewrite <- app_assoc. rewrite cnt24_small_app; [exact C24|]. intros b Hb. apply (ext_blocks_small eo1). eapply Permutation_in; [exact PERMe| exact Hb]. }
    idtac "EXT-SWITCHED".
    rename HEXT4 into K13. unfold ext_cells in K13.
    fold_cinv INV2 m4 hq3 (LBe ++ Lc) FSHB. ch_close m4.
    assert (BE3 : BUDE hq3 (LBe ++ Lc)).
    { eapply BUD_E; [exact BK3| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia]. }
    (* [comment removed for export] *)
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "EXT-ERR". to_free.
      eapply free_walk with (Lc := LBe ++ Lc) (r := rc); first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | exact BE3 | (clear - RS; lia) | (clear - Hr3; lia) | match goal with |- ?g => idtac "EXT-ERR-LEFT:" g end ]. }
    idtac "EXT-OK".
    eapply S_END with (Lc := LBe ++ Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (p := p4);
      first [ exact INV2 | exact CH | exact OW1 | exact PERM1 | exact HOB | exact BE3 | exact C241 | eassumption
            | (clear - Hp4 Hp1 Hp2 Hp2' Hp3; lia) | match goal with |- ?g => idtac "EXT-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04V0@C18971418195.410C59323546451.411D11891817072.411D24582091142.411D42035635047.411D50542107472.411D55184611262.411D60109446735.411D61097333241.411K1396569935.410 K15263251979.409K216607946.410  K22861045682.411K23131760207.410K26482584271.410K26863261647.411K27685289972.411K30038940111.410K30419638991.410K33593216207.410K3386714708.409 K37350304267.410K40707548879.410K41090868175.411K44470506575.410K4568054095.410 K47637149195.410K51948751695.411K58872734415.410K59270213583.410K65803907595.410K8153105419.409 K8908368463.411 L11183176311.1  L12021763723.3  L12877562377.17 L13334634337.2  L1408793817.2   L14636542328.2  L14843011723.2  L15250961821.2  L15522417010.89 L15756043635.89 L16834993293.1  L18302214263.1  L19405001137.89 L20004373133.1  L20254488545.2  L204253020.2    L20570115853.1  L20821275233.2  L21652623661.384L22488405914.13 L22540039658.3  L22866772043.3  L23119474137.2  L23228218977.2  L23513807686.2  L23560763277.1  L24064924233.89 L25160623805.2  L26105897423.3  L26486612313.2  L26875616345.2  L26979598561.2  L27109749153.0  L27386516966.1  L27686821901.3  L27757775585.2  L28631860810.371L29345674871.1  L30042772057.2  L30288275819.89 L30431990105.2  L30997856181.1  L31047919757.1  L31388357250.2  L32327136116.1  L32454903270.1  L32698878355.1  L33597048665.2  L3373834690.2   L33817424237.3  L34799835917.1  L3482806040.89  L35455319922.2  L35655538583.72 L36460502135.1  L36946886283.2  L37354856861.2  L38235734261.1  L38356208653.1  L38412235745.2  L39377292028.89 L40711908697.2  L4086362840.2   L41103222873.2  L42087346475.2  L42810580084.371L43571151479.1  L44061217931.2  L44466151385.2  L4560340619.2   L4572017369.2   L46106660189.2  L47641050525.2  L48487939594.89 L49222980749.1  L49473083873.2  L49997672612.2  L51175623535.89 L51953172697.2  L52835511649.2  L5385571213.1   L54125586285.89 L5436592646.13  L55105288843.2  L55797076866.13 L56142302477.1  L56514611213.1  L56587419617.2  L56847218714.1  L57798807159.1  L58885089625.2  L59257267289.2  L59308586248.2  L59667213247.2  L59698691597.1  L59894218637.1  L60338798689.2  L6034077805.89  L60516634593.2  L60754583113.0  L60915193550.89 L61090796153.1  L63199674356.401L63822901133.1  L6414907617.2   L64418367100.89 L6487220337.3   L65302451596.1  L65816131997.2  L66992297357.1  L67367117072.89 L67825443681.2  L6899380056.1   L6906665613.1   L7382465640.1   L8140296093.2   L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.89  L9887797032.3   N21303764596.410N27801652866.410N34019712227.410N36552142280.410N55294634301.410N56057283471.410N59443058337.410N68652228778.410O10618990077.411O11746403965.411O11930563540.409O1261297262.411 O13663753544.410O14664926154.410O16350966909.410O17494624509.410O17765700477.409O18626760061.410O19357757918.408O19770425853.410O20935596669.411O2425934574.410 O24478127342.410O24929774920.410O27010744648.409O30013201006.410O30870739931.409O31079665533.410O31855893893.409O32537874520.410O33167277300.409O33655933768.409O337230152.410  O34031148413.410O3554426414.409 O35592798351.410O38971639320.408O40100927982.410O40463046306.410O41362955959.410O41843596285.410O44421954429.410O45540685474.410O46762886126.410O4700187630.410 O50817538813.410O5312795005.410 O54023336829.410O54362166638.411O57641632001.410O57733273469.410O58944732014.410O60110421998.410O60687394173.410O61237833838.410O61412920644.411O62187197422.410O63904362034.411O64128366333.411O65333132151.411O66476244349.409O66543996142.411O67704963438.410O7590719101.410 P12019129388.409P13323636166.411P14639119327.409P14837264428.410P20261250374.410P20835442886.410P22533188115.411P23226657990.411P25154843674.410P26120074088.408P26993807942.411P27759401030.410P33810555850.409P35461131733.409P36957875244.409P38409658694.410P42084672396.410P44067980844.409P4550399020.410 P46116577274.410P49463135046.410P50012824067.410P52845428678.410P55103662124.410P56576421190.410P59669588031.410P60340425414.410P60531825990.410P6420654662.410 P6480458454.408 P67819729350.410P8754630693.410 Q12933969670.384Q13193667714.378Q16018831318.411Q16472810971.411Q16950555869.378Q16952477917.379Q19561351767.384Q21832736479.411Q24582091142.411Q24592546470.384Q24965265740.378Q25389680632.379Q25816366470.384Q26481467398.384Q27290748644.378Q30602946598.384Q39439682456.411Q42439168719.411Q47957748593.411Q48118064779.411Q48667079970.378Q49746198710.411Q50233692894.384Q50542107472.411Q54386358946.411Q54938960857.411Q55408699622.411Q55613122833.379Q57139159520.411Q57426677977.411Q58743871165.411Q58746002845.384Q60703362470.384Q61097333241.411Q65188245677.411Q67038703949.411Q8362820247.411 Q8699324297.411 Q9356559673.386 Q9634063272.384 Q9640685903.411 Q9644583048.411 00000400901?03;04A05G07508D09J0:M0;P0<S0=c0>f0?i0@l0B@0CC0DF0EI0FL0GO0HR0IU0JX0K[0L^0Ma0Nd0Og0Pj0Qm0S00S40S50S60S70S80S90S:0S;0TI0Uk0V00V10W90W>0W?0W@0WE0WF0XL0Xe0Xf0Xg0Xh0Xi0Y40Y90YX0YY0YZ0Y[0Y\0Y]0Y^0Yb0Yc0Yd0Zb0Zf0Zg0[I0[J0[O0[P0[V0[Z0[^0[d0[e0[f0[g0[l0]<0]=0^U0^Y0^Z0^[0^_0^d0^e0`40`50`=0`>0`?0a=0aA0aB0aC0aD0aE0aF0aG0bM0bR0bS0bT0bn0bo0c00c50cX0dL0dM0dg0dl0e10e20e70e;0e<0e=0eC0eD0eI0eN0eO0em0en0eo0g^0gc0gd0gi0gj0iQ0iR0iW0iX0i]0kT0kU0kY0k^0kb0kc0kd0me0mf0mg0n@0n]0ne10111Z12[13\14a14b16X17]17^17_17`17a17b17c17d17e17f17g17h17i17j17k17l17m17n17o18018118218318418518618718818918:18;18<18=18>18?18@18A18B18C18D18E18F18G18H18I18J18K18L18M18N18O18P18Q18R18S18T18U19a1;N1=61>d1@Q1B>1D61Ec1GK1I81Je1LR1MY1MZ1OB1Po1R\1TD1V21W81Xe1ZR1\?1]g1_T1a91bf1dS1f@1gn1i[1k;1lS1mc1oP1oQ20H21?22O23J25126X27O28b2::2;R2<I2>02>k2@12@22AU2C42DH2EC2FB2Gm2Gn2I42Ik2Il2KD2L?2M:2Na2O`2P_2RF2RG2Sc2Tg2Ue2Vd2WbS2FBS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2FBFFFFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R7rawjunkS3CRTFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkS3CRTFFS3CRTFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1p4END14rawp3Hp12p24Hp2rFFFFS6rawlen2RSS3CRTS2sp3CRT2bs4CRT02FB3sp17rawjunkFFFFFSS2FBFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2FBFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFS3CRTFS4blenS2FBS2FBS4CNTkFFFS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2FBFFS2loS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkFS2sp3sp1FFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2FBFFFFFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4S3CRTFFS2sp3CRT2bs2FB3sp17rawjunkFFS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFS1p4END11a4rawp2HA2p24Hp2rS3CRTS3CRTFS3sp1S2FBFFS1i2HiFS3CRTS3CRTFS2sp3CRT2bs2FB3sp13APC7rawjunkFSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENS3CRTFS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FS3CRTFS3CRTS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4FS2FBS3CRTS2FBFFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS4blen1dS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x361CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x361CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 ABCMP NA1 DIMG HMND XALG UID GETSIG PHIx FFRx CNTx STKxx CRTEXT STKcf CRTFREE STKc1 STKc2 STKc3 STKcx STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIx_le FFRx_le CNTx_le CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_UID2 : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
      (a1 a2 a3 : word) (pp1 : Z) (b1 b2 b3 b4 c1 c2 c3 c4 : word) (w0 w1 w2 : word) (ja jb : list byte) 
      (ob h1 h2 h3 : word) (rawlen rawp : Z) (tbt tbd tbl tbp ver verpad : word)
      (stg spd : word) (slen sq : Z) (so1 so2 so3 : word) (ap1 : Z) (ir1 ir2 ir3 ir4 sr1 sr2 sr3 sr4 : word)
      (ij48 : list byte) (inext : Z) (img : byte) (ipad : list byte) (sj48 : list byte) (snext : Z) (smg : byte) (spad : list byte)
      (dates : list byte) (pr1 pr2 pr3 pr4 : word) (pkinfo pkctx : Z) (u1 u2 u3 u4 v1 v2 v3 v4 : word)
      (gtg gpd : word) (glen gq : Z) (sigmd sigpk : word) (sigopts : Z)
      (inodes snodes : list Z) (rawjunk : list byte) (pkowned : list blk)
      (k24 k80 s9v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5v s7v x28 x29 x30 x31 : word),
    cinv Lc mm hc FSHB lv len p a1 a2 a3 (Z_to_bv 64 pp1) b1 b2 b3 b4 c1 c2 c3 c4 w0 w1 w2 ja jb
         k24 (Z_to_bv 64 (CRT + 56)) (Z_to_bv 64 END2) (Z_to_bv 64 CRT) (Z_to_bv 64 0) (Z_to_bv 64 END1) (Z_to_bv 64 (FB + 128)) k80 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 CRT) (Z_to_bv 64 (FB + 192)) (Z_to_bv 64 (FB + 256)) (Z_to_bv 64 0) ->
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
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) (Z_to_bv 64 0) s5v (Z_to_bv 64 (al_sb AL)) s7v (Z_to_bv 64 FB) s9v (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (Z.shiftr (CRT + 56) 3 + al_sb AL)) x28 x29 x30 x31)
          F (Z_to_bv 64 0xa9d14) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 BK HA C24.
    pose proof INV as INV0. pose proof CH as CH0.
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 6 zstep.
    zstep. if_cases Kv; zify_cond Kv.
    { idtac "S_UID2-SKIP".
      eapply S_END with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1);
        first [ exact INV0 | exact CH0 | exact OW | exact PERM | exact HOB | exact C24 | eassumption
              | (eapply BUD_E; [exact BK| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia])
              | match goal with |- ?g => idtac "S_UID2-SKIP-LEFT:" g end ]. }
    clear Kv INV0 CH0.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 6 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP.
    pose proof UID as SPU. unfold x509_get_uid_stmtA, A_X509_GET_UID in SPU.
    idtac "S_UID2-CALL".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPU with (CS := hcs asegs R HIA hc) (PP := FB + 96) (UID := CRT + 400) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (lo := lo) (n := 2);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact K12 | exact RBY | exact ORAW | exact OPP | exact CSOKc | exact AB | exact (art_alwf asegs R HIA) | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
               | match goal with |- ?g => idtac "S_UID2-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "S_UID2-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -12288 < ?r <= 0 |- _ => subst x; rename r into rk; rename H0 into Hrk end.
    match goal with H : p <= ?q, H2 : ?q <= END1 |- _ => rename q into p2; pose proof (conj H H2) as Hp2r end.
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "S_UID2-OK". refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_EXT3 with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a) (p := p2);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact BK | eassumption
              | (clear - Hp2r Hp1 Hp2 Hp2' Hp3 HA; lia) | match goal with |- ?g => idtac "S_UID2-OK-LEFT:" g end ]. }
    idtac "S_UID2-ERR". refold_mu INV2 OW2 hc Lc FSHB.
      eapply f2f4_walk with (Lc := Lc) (rg := rk);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact Hrk | (clear - RS; lia) | eassumption
              | (eapply BUD_E; [exact BK| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia])
              | match goal with |- ?g => idtac "S_UID2-ERR-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04V0@C18971418195.405C64758305363.406D11891817072.406D24582091142.406D39200704208.406D42035635047.406D51568166521.406D55184611262.406D60109446735.406K1396569935.405 K216607946.405  K22861045682.406K23131760207.406K25139099531.405K26482584271.405K26863261647.406K30038940111.405K30419638991.405K3052034955.405 K33593216207.405K37201753716.406K40707548879.405K41090868175.406K43305857931.405K44470506575.405K4568054095.405 K47706125524.404K50419111307.404K51948751695.406K57529241483.404K58872734415.405K59270213583.405K8908368463.406 L11183176311.1  L12877562377.17 L13334634337.2  L1408793817.2   L14636542328.2  L14843011723.2  L15522417010.89 L15756043635.89 L1707825163.3   L18302214263.1  L19405001137.89 L20254488545.2  L20394493453.1  L204253020.2    L20643575009.2  L21652623661.379L22071858091.2  L2236094989.1   L22488405914.13 L22540039658.3  L22866772043.3  L23119474137.2  L23228218977.2  L23513807686.2  L24146528397.1  L25143655453.2  L25160623805.2  L26486612313.2  L26875616345.2  L26979598561.2  L27386516966.1  L27509357581.1  L27757775585.2  L27896347405.1  L28631860810.366L29345674871.1  L30042772057.2  L30288275819.89 L3039809565.2   L30431990105.2  L30497891469.1  L31065727245.1  L31388357250.2  L3210077857.0   L32327136116.1  L32454903270.1  L32698878355.1  L33597048665.2  L3373528639.2   L33817424237.3  L34249807629.1  L34622116365.1  L34817643405.1  L3482806040.89  L35455319922.2  L35655538583.72 L36460502135.1  L36946886283.2  L37195950477.3  L37922744956.89 L38235734261.1  L38412235745.2  L38569673229.1  L40711908697.2  L4086362840.2   L41103222873.2  L4137110255.89  L42810580084.366L43318736925.2  L43571151479.1  L44061217931.2  L44466151385.2  L4560340619.2   L4572017369.2   L45861190029.1  L46106660189.2  L47702097730.2  L48487939594.89 L49473083873.2  L49997672612.2  L50431467037.2  L51562087929.1  L51953172697.2  L52835511649.2  L53202815797.1  L54321112557.89 L5436592646.13  L55105288843.2  L55665652425.89 L55797076866.13 L56587419617.2  L56596426575.3  L56847218714.1  L57542116381.2  L57798807159.1  L58885089625.2  L59257267289.2  L59308586248.2  L60338798689.2  L60516634593.2  L60754583113.0  L60915193550.89 L63199674356.396L63337331468.1  L63647278733.1  L64036365709.1  L6414907617.2   L64418367100.89 L6487220337.3   L67367117072.89 L67825443681.2  L6899380056.1   L6906665613.1   L7382465640.1   L8742280115.2   L8793638983.75  L881835912.0    L8896078297.2   L9080482849.71  L9241280651.89  L9562685421.89  L9723264781.1   L9887797032.3   N21303764596.405N27801652866.405N34019712227.405N36552142280.405N55294634301.405N56057283471.405N59443058337.405N68652228778.405O10618990077.406O11486166702.404O11746403965.406O11930563540.404O1261297262.406 O13663753544.405O14664926154.405O16350966909.405O17494624509.405O17670128893.405O18626760061.405O19357757918.403O19770425853.406O20935596669.406O2425934574.405 O24478127342.405O24929774920.405O25065901508.406O27010744648.404O30013201006.405O30870739931.404O31855893893.404O32537874520.405O33655933768.404O337230152.405  O34031148413.405O35592798351.405O40100927982.405O40463046306.405O41362955959.405O41843596285.405O4359334141.405 O44326907133.405O46422032637.404O46518243480.403O46762886126.405O4700187630.405 O49919744372.404O50817538813.405O53069843197.404O5312795005.405 O54023336829.405O54305285249.405O54362166638.406O58944732014.405O5925312290.405 O60110421998.405O60687394173.405O61237833838.405O62187197422.405O63904362034.406O64128366333.406O64462498030.406O65333132151.406O66543996142.406O7590719101.405 P13323636166.406P14639119327.404P14837264428.405P1696828076.404 P20261250374.405P20646143558.406P22070231308.405P22533188115.406P23226657990.406P25154843674.405P26993807942.406P27759401030.405P33810555850.404P3388421567.405 P35461131733.404P36957875244.404P38409658694.405P44067980844.404P4550399020.405 P46116577274.405P49463135046.405P50012824067.405P52845428678.405P55103662124.405P56576421190.405P56597954024.403P60340425414.405P60531825990.405P6420654662.405 P6480458454.403 P67819729350.405P8754630693.405 Q12933969670.379Q13193667714.373Q16018831318.406Q16472810971.406Q16950555869.373Q16952477917.374Q19561351767.379Q21832736479.406Q24582091142.406Q24592546470.379Q24965265740.373Q25389680632.374Q25816366470.379Q26481467398.379Q27290748644.373Q30602946598.379Q39200704208.406Q39439682456.406Q42439168719.406Q47957748593.406Q48118064779.406Q48667079970.373Q49746198710.406Q50233692894.379Q51568166521.406Q54386358946.406Q54938960857.406Q55408699622.406Q55613122833.374Q57139159520.406Q57426677977.406Q58743871165.406Q58746002845.379Q60703362470.379Q65188245677.406Q67038703949.406Q7088984655.406 Q8362820247.406 Q8699324297.406 Q9356559673.381 Q9634063272.379 Q9644583048.406 00000400901?03;04A05G06M08;09J0:M0;P0<`0=c0>f0?i0@l0Ao0C20D50E80FL0GO0HR0IU0JX0K[0L^0Ma0Nd0Og0Pj0Qm0S00S40S50S60S70S80S90TG0Ui0Uj0Uk0W30W40W90W:0W;0XA0XB0XG0X`0Xa0Xb0Xc0Xd0Xo0Y00Y10Y20Y30Y40Y50Y90Y>0Y?0YD0ZB0ZF0ZG0Zi0Zj0Zk0[00[50[;0[<0[@0[D0[J0[K0[L0[M0[R0[W0[\0\l0\m0^E0^I0^J0^K0_Z0_^0__0_d0_e0_m0_n0`H0aF0aG0aK0aL0aM0aN0aO0aT0aU0aV0b\0b]0b^0b_0bd0be0bf0bk0cN0dB0dC0db0e<0e=0e>0eC0eD0eH0eI0eJ0eP0eQ0eR0eS0gB0gC0gH0gM0gR0gS0i:0i;0k20k30k70k<0k@0kA0mB0mC0mD0m]0n:0nX0n]0ne10111Z12[13\14a14b16X17]17^17_17`17a17b17c17d17e17f17g17h17i17j17k17l17m17n17o18018118218318418518618718818918:18;18<18=18>18?18@18A18B18C18D18E18F18G18H18I18J18K18L18M18N18O18P18Q18R18S18T18U1:B1;j1=X1>d1@Q1B>1Ck1Ec1GP1I81Je1LR1MY1O>1O?1Pg1RT1T<1Uj1W01X]1ZJ1\71]_1_L1a91bf1dS1f@1gn1i[1k;1lS1mc1oP1oQ20H21?22O23J25126X27O28b2::2;R2<I2>02>o2?j2A02A12BT2D32EG2FB2GA2Hl2Hm2J32Jj2Jk2LC2M>2N92O`2P_2RF2SE2SF2Tb2Uf2Vd2WbS2FBS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B24CRT03LOS2FB3sp13SP13SPR2F04SLOu4SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp3CRT4blen2bs4LFB23LFB2B24CRT03TOP2FB3sp13SP13SPR2F04SP1R4LFB36LFB5126LFB5114LFB72hc7rawjunk3HTcS1R2LF2sp3CRT4blen2lo2bs4LFB23LFB2B23LOS2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA2S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA1S2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB3APC4LFB36LFB5126LFB5114LFB77rawjunkS2FBFFFFFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F02F83APB4SP1R7rawjunkS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R7rawjunkFFS1R3NS14STKc5STKc12sp3CRT2lo2bs4CRT02FB3sp13SP13SPR2F04SLOu4SP1R7rawjunkFS3CRTFFS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkFS3CRTS1p4END14rawp3Hp12p24Hp2rFFFFS6rawlen2RSFFFFFFS2FBS3CRTFS3CRTS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7S2FBFS2sp3CRT2lo2bs2FB3sp14FBLO7rawjunkFFS3CRTS3CRTS4blenSS2FBS2FBS4CNTkFFFS3CRTS3CRTS3CRTS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp14SP1M3APC3SPR2F03APB4SP1R7rawjunkFS1R3HIA1h2sp3CRT1Q4blen3BUF2lo2bs2B12B22B34CRT03DXB3TOP2FB3sp13APC3SPR2F03APB4SP1R5HTOPcS2FBFFS2sp3CRT1Q4blen3BUF2bs2B12B22B33ALC4CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R7rawjunkS2loFS3CRTFS2sp3sp1FS2sp3CRT2bs2FB3sp17rawjunkS2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB7FS2FBFFFFS3CRTFFS1R2sp3CRT2bs4CRT02FB3sp13SPR3ACV2F04SP1R6rawlen4rawp7rawjunk4RLEN3RA4FFFS3CRTFFS3CRTS2sp3CRT2lo2bs5CRTLO2FB3sp17rawjunkS4blen1p4END14END21a6rawlen4rawp3RBL3Hp24Hp2'3Hp32HAFS2sp3CRT2bs4CRT02FB3sp17rawjunkS1p4END11a4rawp2HA2p24Hp2rFFS3sp1FS2FBFFS1i2HiFFSS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R4END14END26rawlen4rawp7rawjunk4Hp2'3Hp34RLENFS3CRTS3CRTS3CRTFS2sp3CRT1Q4blen3BUF2bs2B12B22B34CRT03DXB2FB3sp13APC3SPR2F03APB4SP1R6rawlen4rawp7rawjunk2RL4RLEN3RA13RA2FS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT03DXB4SLOS4SLOL2FB3sp13APC3SPR3ALO2F03APB4SP1R6rawlen4rawp7rawjunk4RLEN3RA4FS2FBS3CRTS2FBFS1R2sp3CRT1Q4blen3BUF2lo3slo2bs2B12B22B34CRT05CRTLO3DXB4SLOS4SLOL3DCD2FB3sp13APC5BUFLO3SPR3ALO2F02F14FBLO3APB3FDD4SP1R4SBND2a02DaSFS2sp3CRT2lo2bs2FB3sp13SP1S2sp3CRT2bs2FB3sp12F07rawjunkS2sp3CRT2bs2FB3sp13APC7rawjunkS3CRTS4blen1dS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk3x361CS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunk4SBND3x361CS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunk3x361CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB76rawlen4rawp7rawjunk4RLEN3RA3S1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2lo2bs4LFB23LFB2B22FB3sp14FBLO4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB3sp13SP14FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO2F14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B22FB4FBLO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB75HTOPcS1R3NS14STKc3NA15STKc22LF2sp3CRT4blen2lo2bs4LFB23LFB2B25CRTLO2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B22FB3sp13SPR2F02F84LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S2LF2sp3CRT4blen2bs4LFB23LFB2B23ALC4CRT02FB3sp13SPR2F04SP1R4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7S1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R2LF4blen3slo2bs4LFB23LFB2B24SLOS2FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB7S1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP13ALO4SLOu4LFB36LFB5126LFB5114LFB77rawjunkFS2LF2sp4blen2bs4LFB23LFB2B22FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB7FS1R3HIA1h2LF2sp4blen2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB3sp14LFB36LFB5126LFB5114LFB77rawjunkS1R3NS14STKc3NA15STKc22LF2sp4blen2lo2bs4LFB23LFB2B23LOS2FB3sp13SP14SLOu4LFB36LFB5126LFB5114LFB77rawjunkS2LF3CRT4blen2bs4LFB23LFB2B22FB4LFB36LFB5126LFB5114LFB77rawjunkFS1R3HIA1h2LF2sp4blen3slo2bs4LFB23LFB2B23TOP2FB3sp13SP14LFB36LFB5126LFB5114LFB77rawjunk5HTOPcS2LF4blen2bs4LFB23LFB2B22FB3sp14SP1R4LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunkS2LF4blen2bs4LFB23LFB2B22FB2F04LFB36LFB5126LFB5114LFB77rawjunk". (* [comment removed for export] *)
  #[using="IMG NS1 STKc STKc0 SF5 STKc4 ABCMP NA1 DIMG HMND XALG UID GETSIG PHIx FFRx CNTx STKxx CRTEXT STKcf CRTFREE STKc1 STKc2 STKc3 STKcx STKcfr CNTj0 PHIj_mono FFRj_mono CNTj_mono PHIj_sadd FFRj_sadd CNTj_sadd PHIx_le FFRx_le CNTx_le CNTk0 PHIcf0 FFRcf0 PHIcf_mono FFRcf_mono Q BUF bs LFB2 LFB BIN B1 B2 B3 ALC CRT0 CWX CRTLO DXB SLOS SLOL SLO TOP SPA SPH TPV LOS DCD UW BUDV BUDF SP1 SP1M F64 FRSH CFB APC BUFLO SPR ALO ACV F0 F1 FBLO F8 APB FDD SLOu SP1R LFB3 CRB LFB512 LFB511 LFB7"] Lemma S_UID1 : forall (hc : HST asegs R HIA) (mm : mem) (Lc : list blk) (lv len : word) (p END1 END2 a : Z)
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
  Proof.
    intros until x31. intros INV CH OW PERM HOB RP RL RS RBL Hp1 Hp2 Hp2' Hp3 HA1 HA1' HPP1 BK HA C24.
    pose proof INV as INV0. pose proof CH as CH0.
    open_cinv_mu INV hc. ch_open CH.
    (* [comment removed for export] *)
    do 6 zstep.
    zstep. if_cases Kv; zify_cond Kv.
    { idtac "S_UID1-SKIP".
      eapply S_UID2 with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a);
        first [ exact INV0 | exact CH0 | exact OW | exact PERM | exact HOB | exact C24 | exact BK | eassumption
              | match goal with |- ?g => idtac "S_UID1-SKIP-LEFT:" g end ]. }
    clear Kv INV0 CH0.
    destruct (raw_side hc Lc mm _ _ _ _ _ _ _ _ _ _ _ _ _ OW PERM HHc HCSc RP RL) as (RBY & RLEN & RIN & ORAW & RA1 & RA2 & RA3 & RA4).
    (* [comment removed for export] *)
    do 6 zstep.
    frame_aobj FSH (FB + 96) 1%nat as OPP.
    pose proof UID as SPU. unfold x509_get_uid_stmtA, A_X509_GET_UID in SPU.
    idtac "S_UID1-CALL".
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHx : HM _ _ _ hc _ _ mx |- _ =>
    acallxA_sp sp1
      (eapply SPU with (CS := hcs asegs R HIA hc) (PP := FB + 96) (UID := CRT + 376) (P := p) (END := END1) (BUF := rawp) (bs := rawjunk) (lo := lo) (n := 1);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact K11 | exact RBY | exact ORAW | exact OPP | exact CSOKc | exact AB | exact (art_alwf asegs R HIA) | eassumption | reflexivity
               | cside RLEN RA1 RA2 RA3 RA4 RP RL RS Hp1 Hp2 Hp2' Hp3
               | match goal with |- ?g => idtac "S_UID1-LEFT:" g end ]) end end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "S_UID1-POST-LEFT:" g end.
    match goal with H : ?x = Z_to_bv 64 ?r, H0 : -12288 < ?r <= 0 |- _ => subst x; rename r into rk; rename H0 into Hrk end.
    match goal with H : p <= ?q, H2 : ?q <= END1 |- _ => rename q into p2; pose proof (conj H H2) as Hp2r end.
    zstep. if_cases Kr; zify_cond Kr.
    { idtac "S_UID1-ERR". refold_mu INV2 OW2 hc Lc FSHB.
      eapply f2f4_walk with (Lc := Lc) (rg := rk);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact Hrk | (clear - RS; lia) | eassumption
              | (eapply BUD_E; [exact BK| clear; lia| clear; lia| clear; lia| clear - HA Hp1 Hp2 Hp2' Hp3 RBL; lia])
              | match goal with |- ?g => idtac "S_UID1-ERR-LEFT:" g end ]. }
    idtac "S_UID1-OK". refold_mu INV2 OW2 hc Lc FSHB.
      eapply S_UID2 with (Lc := Lc) (END1 := END1) (END2 := END2) (ap1 := ap1) (pp1 := pp1) (a := a) (p := p2);
        first [ exact INV2 | exact CH | exact OW2 | exact PERM | exact HOB | exact C24 | exact BK | eassumption
              | (clear - Hp2r Hp1 Hp2 Hp2' Hp3 HA; lia) | match goal with |- ?g => idtac "S_UID1-OK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.
  End Call.
End Walk.
