(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtStmts CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_crt_parse_stmts A_x509_get_name_stmt A_pkcs7_cinfo AImgGlobals A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_x509_parse_san_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0296726b1818238d 1 1 64 2 46 1 73 1 3 0 1 72 1 74 64P02f4769797544ad3 0 9 0 1 48 1 57 1 67 1 68 1 69 1 70 1 73 1 74 1P057f888fea6b5bce 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P066fe71df21ae743 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P06e34762f53ecc32 0 4 0 1 23 1 84 1 85 1P072100a1e1c4d1c4 1 1 64 2 0 1 72 1 3 2 1 73 1 74 64P07cb4660e7ea5e42 0 3 0 1 35 1 67 1P0ae981643ffa5d34 0 8 0 1 56 1 57 1 58 1 66 1 67 1 68 1 69 1P0b16c16007ad03dc 0 3 0 1 35 1 67 1P0b5cf99a23c090c0 0 3 0 1 35 1 67 1P0c971b02f67fe960 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P10f3a84ae83a161e 0 3 0 1 35 1 67 1P11d353ec765e4e20 0 3 0 1 35 1 67 1P143b1aeb84747d6f 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P14a052e7abac4aca 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P16fa3e9eac1e3a4e 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P1d29c4443e95f09e 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P1d4758ca3eb006e2 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P1f9e5fdafa58c36d 0 4 0 1 23 1 84 1 85 1P1fe749c66538369e 0 3 0 1 35 1 67 1P223a170867968c7b 0 3 0 1 35 1 67 1P2365b34d76b68879 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P25e2dd906e96b08d 0 3 0 1 35 1 67 1P27a0d8a7314322ec 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P29efd6c8b593e5d7 0 3 0 1 35 1 67 1P2a9b213710c8fec9 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P2bb6d34d6fd5803b 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P2f1efa0db2de96b5 0 3 0 1 35 1 67 1P2fe7eced5e05e2ef 0 3 0 1 35 1 67 1P3202cd6faebe91d5 1 1 64 2 1 1 72 1 3 0 1 73 1 74 64P34aa5ff1f4ae5788 0 3 0 1 35 1 67 1P36e1ce9d0e0d34fb 0 8 0 1 68 1 69 1 70 1 78 1 79 1 80 1 81 1P37da8a81b89636d4 0 9 0 1 24 1 68 1 78 1 79 1 80 1 81 1 84 1 85 1P3b2e4602f55c5b1b 0 3 0 1 35 1 67 1P3bfbff918e05fdef 0 3 0 1 35 1 55 1N00eba6a27d4c9141N010fb6d3b7d0f285N03644b770e55d4b7N03fd729eaf605fefN0494fac186d2d8eaN04fa2502ba978c23N05a8e54434f52653N0807a6873e04e80dN08fdafda56d6245fN0ce1f4ae0366c110N0d57733efeb25b77N1157b7e6416460c1N129e5adf81e910f8N142d971df02a436aN1667ab9081f5cd9fN1694814be5d401a5N172702e1558d3645N17664c19a1fe6c9bN18957cdbeb622d56N1924f796d8dd4652N19d14f7b2732cbadN1a86c3e48701c456N1a926ea9249d4e9dN1c55074cde14c600N1c56574379862d8bN1d1ff2686bf746f7N1d6b9905ab55ba9bN20e9ffc8b461f14fN214309c57c6f30c7N23d8cd88b2c21897N2895ea02ae12018aN28c5787146965734N294b8252b8666170N29b457b7ae9a0381N2a810a883811d7b8N2bd5df3625aba077N2c6d5446b69c767dN2f148d4ccc3d5d71N2f8070313f687e9bN312408414f782dd7N3194491223c61412N325eceb05530129fN356ae31573b10a99N3725d2405c53578dN3ccba55b880428d9N3ccf309d62324cf2N3d6b0f095a01aec0"%lxh.
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
Definition zchk_new : list Z := [0xaec44; 0xaec48; 0xaec4c; 0xaecd8; 0xaecdc; 0xaece0; 0xaece4; 0xaece8; 0xaecec; 0xaed24; 0xaed48; 0xaed4c; 0xaed50; 0xaee54; 0xaee58; 0xaee5c; 0xaee88; 0xaee8c; 0xaee90; 0xaeef0; 0xaeef4; 0xaeef8; 0xaef48; 0xaef4c; 0xaef50; 0xaef84; 0xaef88; 0xaef8c; 0xaef90; 0xaef94; 0xaef98; 0xaefd4; 0xaefd8; 0xaefdc; 0xaf160; 0xaf164; 0xaf168; 0xaf16c; 0xaf170; 0xaf1d8; 0xaf1dc; 0xaf1fc; 0xaf200; 0xaf204; 0xaf208; 0xaf20c; 0xaf220; 0xaf224; 0xaf228; 0xaf22c; 0xaf230; 0xaf268; 0xaf26c; 0xaf270; 0xaf274; 0xaf278; 0xaf2ac; 0xaf2b4; 0xaf2b8; 0xaf2bc; 0xaf2c0; 0xaf304; 0xaf308; 0xaf30c; 0xaf310; 0xaf314].
Lemma zchk_land1 x : Z.land x 1 = x mod 2. Proof. apply (Z.land_ones x 1); lia. Qed.
Lemma zchk_land3 x : Z.land x 3 = x mod 4. Proof. apply (Z.land_ones x 2); lia. Qed.
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
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
Local Ltac zlia := try lx_unpin; zchk_clear; lia.
Local Ltac zchk_false :=
  repeat match goal with H : context [Z.land ?x 7] |- _ => rewrite (zchk_land7 x) in H end;
  repeat match goal with H : context [Z.land ?x 3] |- _ => rewrite (zchk_land3 x) in H end;
  repeat match goal with H : context [Z.land ?x 1] |- _ => rewrite (zchk_land1 x) in H end;
  repeat match goal with H : context [Z.land ?x 15] |- _ => rewrite (zchk_land15 x) in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => unfold zlow in H; destruct (Z.eqb_spec a b); cbn in H end;
  repeat match goal with H : (if ?a =? ?b then _ else _) = _ |- _ => destruct (Z.eqb_spec a b); cbn in H end;
  try discriminate; unfold zlow in *; zlia.
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
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xaf32c else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  | |- _ (MS _ _ (if ?c then _ else Z_to_bv 64 0xaf32c) _ _ _ _) =>
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
Local Ltac shadow_merge_cut_at segs R F cnd slow fast fc rv m ro ::=
      let d1 := decode_at segs slow in
      lazymatch d1 with
      | Some (OpImm ALU_AND ?tmp _ _, _) =>
          let pt := eval vm_compute in (bv_key tmp) in
          let d2 := decode_at segs (slow + 4)%Z in
          let kr := lazymatch d2 with
                    | Some (Branch BC_LT _ ?kr _, _) => kr
                    | Some (OpImm ALU_ADD _ _ _, _) =>
                        lazymatch decode_at segs (slow + 8)%Z with
                        | Some (Branch BC_LT _ ?kr _, _) => kr
                        end
                    end in
          let pk := eval vm_compute in (bv_key kr) in
          merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
      | Some (OpImm ALU_ADD ?tmp _ _, _) =>
          let pt := eval vm_compute in (bv_key tmp) in
          let kr := lazymatch decode_at segs (slow + 4)%Z with
                    | Some (Branch BC_LT _ ?kr _, _) => kr
                    end in
          let pk := eval vm_compute in (bv_key kr) in
          merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R)) F (Z_to_bv 64 fast) fc rv m ro)
      | _ => fail "shadow_merge: no [andi t,c,7] or [addi t,a,n] at the slow-path target" slow
      end.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis GSBH : al_gsb AL = AGSB.
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z) (STKn : Z).
  Hypothesis STKn0 : 0 <= STKn.
  Hypothesis GETNAME : x509_get_name_stmtA asegs R HIA PHIn FFRn CNTn STKn A_X509_GET_NAME.
  Hypothesis PHIn_mono : forall n n', 0 <= n <= n' -> 0 <= PHIn n <= PHIn n'.
  Hypothesis FFRn_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRn n d <= FFRn n' d.
  Hypothesis CNTn_mono : forall n n', 0 <= n <= n' -> 0 <= CNTn n <= CNTn n'.

  Local Notation STKps := (A_x509_parse_san_A.STKps R STKn).
  Definition FFRps (n d : Z) : Z := FFRn n (d + 1).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (SB SAN BUF sp0 slen lo slo d : Z) (bs : list byte) (tgw pdw : word).
  Hypothesis ALB : SB mod 8 = 0. Hypothesis SB0 : 0 < SB.
  Hypothesis CRSB : client_range L (LB ++ fdata LF) lo SB 24.
  Hypothesis SBHI : bv_unsigned sp <= SB. Hypothesis SB47 : SB + 32 <= 2^47.
  Hypothesis BIN : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis W1 : BUF <= sp0. Hypothesis W2 : 0 <= slen. Hypothesis W3 : sp0 + slen <= BUF + Z.of_nat (length bs).
  Hypothesis B47 : BUF + Z.of_nat (length bs) < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BSMALL : Z.of_nat (length bs) < 2^30.
  Hypothesis ALS : SAN mod 8 = 0. Hypothesis SAN0 : 0 < SAN.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SAN 80.
  Hypothesis SANLO : SAN + 80 <= lo.
  Hypothesis DSS : SAN + 80 <= SB \/ SB + 24 <= SAN.
  Hypothesis DSB : SAN + 80 <= BUF \/ BUF + Z.of_nat (length bs) <= SAN.
  Hypothesis DBB : SB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SB.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKps.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 6)%nat.
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L61437265048.2000008S2LF3LFB". (* [comment removed for export] *)
  Let LFB' : (length LF < 511)%nat.
  Proof. clear - LFB. unfold LFMAX_CRT in LFB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_x509_parse_san_A.STKps in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(SAN, SAN + 80)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHI := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m2x : mem) (WA WB : list ivl) (r : Z) (cb : list byte)
      : machine_state -> Prop := fun ms =>
    exists (m' : mem) (h4 : HST asegs R HIA) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ sshad asegs AL m' slo (bv_unsigned sp)
      /\ presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m m'
      /\ presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x m'
      /\ hcs asegs R HIA h4 = hcs asegs R HIA h3 /\ htop asegs R HIA h4 = htop asegs R HIA h3
      /\ hstkhi asegs R HIA h4 = hstkhi asegs R HIA h3 /\ hflag asegs R HIA h4 = hflag asegs R HIA h3
      /\ havol asegs R HIA h4 = havol asegs R HIA h3 /\ hfr asegs R HIA h4 = hfr asegs R HIA h3
      /\ (forall mo, HK asegs R HIA h4 mo <-> HK asegs R HIA h3 mo)
      /\ HM asegs R HIA h4 (LBc ++ LB) LF m'
      /\ rw_cells asegs m' SAN [CB 80 cb].

  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DBB; try lx_pin1 DSB; try lx_pin1 DSS; try lx_pin1 ALS; try lx_pin1 BSMALL; try lx_pin1 BUF0; try lx_pin1 B47; try lx_pin1 BIN; try lx_pin1 SB47; try lx_pin1 CRSB; try lx_pin1 ALB; try lx_pin1 pdw; try lx_pin1 tgw; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 CNTn_mono; try lx_pin1 FFRn_mono; try lx_pin1 PHIn_mono; try lx_pin1 GETNAME; try lx_pin1 CNTn; try lx_pin1 FFRn; try lx_pin1 PHIn; try lx_pin1 GSBH; try lx_pin1 MCI; try lx_pin1 AMC; try lx_pin1 AMS; try lx_pin1 GT; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01V0@D2459793318.146 D32452690557.146D3374278032.145 D34676576366.147D40033284243.147D43016287773.147D45715803169.145D46050181056.147D60109265003.147D62011770188.147D66251787523.146D68405837779.145D6909504982.145 L18271036607.135L19546883927.128L19546883930.132L2333531081.124 L2333536794.122 L24876536089.178L26163319614.124L26163329773.122L30443668812.13 L35655538631.13 L39844638933.0  L39972639317.0  L40379729337.187L41486840212.2  L42411609006.0  L48117620902.129L48117620903.130L48117620904.126L48117620907.125L48911768491.1  L5070094962.128 L5070094975.132 L50790731766.13 L54488093861.188L59578101107.150L60098763854.6  L61745577556.11 L62018535662.1  L6302880071.124 L6302890132.122 L64850595401.0  L65276887188.129L65276887193.125L6912107235.129 L6912107246.125 L9356559676.18  P41479713552.184Q10592386204.151Q10592386207.155Q16178749881.151Q16178749882.155Q22358563588.154Q23684643745.152Q23925414039.161Q25138220955.182Q30147450662.152Q31314676345.150Q33624318679.156Q33624318682.152Q34676576359.156Q34676576362.152Q34796740410.155Q38250992820.160Q39028748170.182Q4125667684.181 Q42439443119.183Q42441479406.163Q4279611329.183 Q43878048872.160Q47740986937.159Q48117620905.155Q48117620906.151Q48132302223.154Q48132302231.150Q49293189221.152Q49293189224.156Q52350325690.159Q5935758158.183 Q59668625896.156Q60382659730.156Q60382659743.152Q62009673039.161Q64133651577.182Q64681502663.163Q64683667846.183Q65266402725.150Q65266402749.154Q65276887188.156Q65276887193.152Q65276888093.158Q66394042873.156Q67397950268.151Q6897428426.154 Q6897428434.150 Q6912107235.156 Q6912107246.152 Q6912108138.158 Q7917062807.156 Q7917062810.152 00000100H00I00J00K00k01B01C01c02<02S02T02k03S04004M04N04O05005105205Z06306406506T06U06V07Q08L09G0:B0:F0:h0;J0<20=90=U0=_0>K0>N0>O0>P0>Q0>d0?70?J0?]0@Y0@Z0@m0A@0AS0Af0Ag0Ah0B@0B]0B^0B_0B`0Ba0Bb0Bc0Bd0C70CT0Cn0DS0Dn0EH0E^0F20Fm0Gh0Hc0I^0I_0I`0J40JN0JO0JP0JQ0Jc0K=0Kf0LY0Ll0M?0MR0Me0N80N90N:0NM0N`0O30OF0OY0P50PQFS2LF2bs3LFB4LFB'2FB3sp1FFFS1R3HIA2LF2bs3LFB4LFB'2h32FB3sp1S2LF2bs3LFB4LFB'2FB3sp1FS1R2LF2lo2bs3LFB3LOS4LFB'2FB3sp1S1R2LF2bs3LFB4LFB'2FB3sp1S2LF2bs3LFB4LFB'2FB3sp1FS2LF2bs3LFB4LFB'2FB3sp1S1R2LF2sp3slo2bs4SLOS3LFB4LFB'2FB3ALO2F1S2LF2bs3LFB4LFB'2FB3sp12F82F0S2LF2bs3LFB4LFB'2FB3sp12F82F0FFS2LF2bs3LFB4LFB'2FB3sp14lxHn1p2PBFFS1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3LOSS1R3HIA1h2sp2lo3TOP5HTOP3SSS2LF2sp2bs3LFB4LFB'2FB3sp14lxHnFSS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS2FBS2LF2bs3LFB4LFB'2FB3sp14SP1R2F82F0S2LF2bs3LFB4LFB'2FB3sp14SP1R2F82F0S1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3LOSS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB4LFB'2FB3sp14SP1R2F04lxHnS2LF2bs3LFB4LFB'2FB3sp11c2HcS1R2lo3LOSS1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3sp13SP1S1RFFSS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBFFS1R3HIA1h2LF2bs3LFB4LFB'S2LF2bs3LFB4LFB'2FB4lxHn1p2PBFFFFFFFS2LF2lo2bs3LFB4LFB'S2LF2bs3LFB4LFB'2FB4lxHn1p2PBS2LF2bs3LFB4LFB'4lxHn1p2PBS1R2LF3slo2bs4SLOS3LFB4LFB'4lxHn1p2PBS1R2LF3slo2bs4SLOS3LFB4LFB'S2LF2bs3LFB4LFB'4lxHn1p2PBS2LF2sp2lo2bs3LFB4LFB'S2LF3SAN2bs3LFB4LFB'S1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'3ALOFFS2LF3SAN2bs3LFB4LFB'S2LF2bs3LFB4LFB'4lxHn1p2PBFFFS1R2LF2bs3LFB4LFB'S2LF2bs3LFB4LFB'4lxHn1p2PBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4LFB'5HTOP3S1R3HIA1h2LF2sp3slo2bs3TOP3LFB4LFB'5HTOP34lxHn1p2PBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBFFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R2LF2bs3LFB4LFB'2FB3ALO2F1S1R2LF2bs3LFB4LFB'2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LFB' LOS LFB SPH TOP SLO SLOL SLOS SANLO CWS SAN0 W3 W2 W1 SBHI SB0 bs slen sp0 BUF SB STKn0 STKn NB1 NA1 NS1 IMG"]
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (LBc : list blk) (m2x mm : mem) (WA WB : list ivl) (FB sp1 : Z)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v s10v s11v x28 x29 x30 x31 w0 w1 w2 : word)
      (r : Z) (cb : list byte),
    HM asegs R HIA h3 (LBc ++ LB) ((FB, 256) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h -> hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 256 -> fresh_apart R (LBc ++ LB) LF FB 256 -> crange CS FB 256 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHI ->
    rw_cells asegs mm (bv_unsigned sp + -104) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -104) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m mm ->
    presW asegs R HIA h3 (LBc ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm ->
    sshad asegs AL mm slo (bv_unsigned sp) ->
    rw_cells asegs mm SAN [CB 80 cb] -> crange CS SAN 80 ->
    (FB + 256 <= SAN \/ SAN + 80 <= FB) ->
    evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 LBc m2x WA WB r cb)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xaf00c) fc None mm (seg_rom asegs)).
  Proof.
  intros until cb.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB FHD FSH SAVE STK2 STlo MI PRES PRES2 SS HSAN CRS APS0.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NB1 STKn0; lia).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (CRS3 : crange (hcs asegs R HIA h3) SAN 80) by (eapply crange_mono; [exact HCS3| exact CRS]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NA1 NB1 STKn0 TOP HTOP3; lia]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & AP3 & _ & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaf0a0] [] 525%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 256) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ lo (arl_stklo R) p SAN 80 NCp (client_range_of_w L _ _ _ _ _ CWS) SUB1 LOS ltac:(clear; lia)) as NP1.
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS NS1 NA1 NB1 STKn0; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NS1 NA1 NB1 STKn0; lia]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NS1 NA1 NB1 STKn0; lia]).
  clear HHe NCp NSp.
  repeat match goal with H : rw_cells _ me FB _ |- _ => clear H end.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  idtac "EPI-DONE".
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  try (lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (bv_unsigned sp + -104), SV : rw_cells _ mf (bv_unsigned sp + -104) _ |- _ =>
          pose proof (stk_merge asegs mf lo sp1 _ ST0 STA ltac:(clear - SP1 SLO NS1 NA1 NB1 STKn0; lia)) as ST3;
          release_frame SV ST3 (bv_unsigned sp); exact ST3 end).
  }
  split; [assumption|].
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  split; [exact HM4|].
  assumption.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L26892418956.1L36673055490.2L40228640085.0L9873114841.1300000400>00?014S2spS4rest3SZRSS1R3NS13NA13NB14STKn5STKn02sp2lo3slo4SLOL3SLO3sp13SP1". (* [comment removed for export] *)
  Lemma san_fin : forall (hq : HST asegs R HIA) (nodes : list Z) (FB sp1 : Z) (m2x mm : mem) (r t dn : Z) (rest : list cell) (w0 w1 w2 : word)
      (xra x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s3v s4v s5v s6v s7v s10v s11v x28 x29 x30 x31 : word),
    HM asegs R HIA hq (SNAME (rev nodes) ++ LB) ((FB, 256) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA hq x) ->
    htop asegs R HIA hq = htop asegs R HIA h -> hstkhi asegs R HIA hq = hstkhi asegs R HIA h -> hflag asegs R HIA hq = hflag asegs R HIA h ->
    havol asegs R HIA hq <= havol asegs R HIA h + PHIn slen -> hfr asegs R HIA hq <= hfr asegs R HIA h + FFRps slen d ->
    Z.of_nat (length nodes) <= CNTn slen ->
    bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 256 -> crange CS FB 256 ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) FSHI ->
    rw_cells asegs mm (bv_unsigned sp + -104) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -104) -> stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m mm ->
    presW asegs R HIA hq (SNAME (rev nodes) ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) [] m2x mm ->
    sshad asegs AL mm slo sp1 -> sshad asegs AL mm sp1 (bv_unsigned sp) ->
    rw_cells asegs mm SAN (C4 (Z_to_bv 64 t) :: rest) -> Z.of_nat (cells_size rest) = 76 -> 0 <= t <= 7 ->
    (t = 4 -> exists p4 j48 mg pad7 j8, rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
    (t = 4 -> name_chain asegs (fun _ => True) m2x (SNAME (rev nodes) ++ LB) dn nodes) ->
    (t <> 4 -> nodes = []) -> (r <> 0 -> nodes = []) ->
    List.NoDup nodes -> (forall x, In x nodes -> forall B k, In (B, k) LB -> x + NAME_SIZE <= B \/ B + k <= x) ->
    -0x3000 < r <= 0 -> crange CS SAN 80 -> (FB + 256 <= SAN \/ SAN + 80 <= FB) ->
    aevtA asegs (KF asegs R HIA hq mo0)
      (x509_parse_san_postA asegs R HIA PHIn FFRps CNTn h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SAN slen lo slo d m mo0)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 FB) s3v s4v s5v s6v s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s10v s11v x28 x29 x30 x31)
          F (Z_to_bv 64 0xaf00c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros HHq HCSq ETq ESq EFq EVq EFRq ECNT SP1 SP1M F64 FRSH CFB FHD FSH SAVE STK2 STlo MI PRES PRES2 SS1 SS2 HSAN SZR TR T4 NC TN4 RN ND APN RR CRS APSAN.
    rt_facts.
    pose proof (fresh_apart_grow R HIA hq (SNAME (rev nodes)) LB LF mm FB 256 FRSH HHq) as FRSHq.
    pose proof (presW_hmono R HIA h hq LB LF _ _ _ m mm PRES HCSq ESq) as PRESq.
    pose proof (sshad_merge asegs AL mm slo sp1 (bv_unsigned sp) SS1 SS2 ltac:(clear - SP1 SLOL SLO NS1 NA1 NB1 STKn0; lia)) as SSm.
    (* [comment removed for export] *)
    assert (SZC : cells_size (C4 (Z_to_bv 64 t) :: rest) = 80%nat) by (cbn [cells_size csize]; clear - SZR; lia).
    pose proof (conj HSAN I) as HSANw (* [comment removed for export] *).
    pose proof HSAN as HSANb. apply rw_cells_blob in HSANb. rewrite SZC in HSANb.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBc := SNAME (rev nodes)) (WA := W) (WB := @nil ivl);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact HSANb | exact SSm
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4 & HSAN9).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold x509_parse_san_postA.
    do 15 eexists. exists m9, mo9, h4, r, t, dn, rest, nodes.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES9) as HPF; rewrite ESq in HPF; exact HPF|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact ECNT|].
    split; [exact (rw_cells_unblob _ _ _ _ _ _ (proj1 HSANw) SZC HSAN9)|].
    split; [exact SZR|]. split; [exact TR|]. split; [exact T4|].
    split.
    { intros E4. specialize (NC E4).
      eapply chain_presx with (L2 := SNAME (rev nodes) ++ LB) (X := @nil ivl) (SP := bv_unsigned sp);
        [exact NC| | | unfold NAME_SIZE; clear; lia| intros x Hx; exact I].
      - intros x Hx. apply in_app_iff. left. unfold SNAME. apply (in_map (fun a => (a, NAME_SIZE))). apply -> in_rev. exact Hx.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29))| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx]. }
    split; [exact TN4|]. split; [exact RN|]. split; [exact ND|]. split; [exact APN|]. exact HH4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02<0@L10113460364.3  L10334857496.15 L10472354596.288L12274638935.1  L12800369225.7  L13024568983.7  L14247179949.7  L15346700995.4  L1540877545.3   L1584823699.1   L1685717371.0   L17698505472.5  L19980016842.7  L20127584852.11 L22271096388.7  L22706556809.3  L2385107540.3   L24023900370.0  L24128180555.1  L25073696145.3  L26527621680.7  L26892418956.1  L27470824284.2  L27650499371.1  L27817441514.295L27817441514.296L2799126802.9   L28464376784.5  L29320938059.296L31021792691.6  L31165845516.5  L31543112400.8  L31663171622.6  L31863022963.4  L32847017047.1  L33740837294.0  L34603895532.0  L35653326811.13 L39281820463.1  L40281191306.3  L40447431146.1  L41329737543.3  L41731051468.295L42411609006.0  L43767695367.3  L4449834141.18  L44631927050.8  L47738694412.1  L48996498219.3  L49508988902.1  L49799904432.3  L50796875722.13 L51580320287.234L52045659405.3  L531410120.6    L53709460955.2  L53886137103.4  L55536219297.0  L55660970509.2  L55978685711.1  L56658999053.1  L5667565037.3   L57333296984.295L57333296984.296L59308586248.2  L59578101107.3  L60098763854.6  L60991706347.10 L61352941097.1  L62030920048.14 L6203936179.1   L62246953235.1  L62586290822.10 L64850595401.0  L66149329551.25 L66151427842.16 L6899380056.1   L696052593.2    L7490251809.9   L8464427966.16  L9356559645.18  L9631767084.2   P324046647.301  P324046647.302  P7903954312.301 P7903954312.302 Q12274903248.295Q1584559380.295 Q16867461576.296Q19561400165.234Q20966008300.234Q26314584654.301Q26314584654.302Q26316671538.291Q26316671538.297Q27652910767.234Q30441621866.297Q31716083380.296Q32025723328.297Q32834282797.294Q33422860542.297Q38114887359.297Q40437208276.296Q40584667657.296Q42441548847.301Q42441548847.302Q43187820115.296Q44298944140.291Q44298944140.297Q44301027056.301Q44301027056.302Q44840736200.296Q46195023504.296Q47741054514.296Q48119910507.301Q48119910507.302Q49748522582.301Q49748522582.302Q51959565845.297Q53464363711.297Q55256112523.297Q5596578838.301 Q5596578838.302 Q58668049481.290Q58972088534.298Q59619599049.296Q62259458153.294Q63435846322.297Q63614823517.296Q64228675114.300Q64228675114.301Q67041068973.301Q67041068973.302Q67125645257.290Q67140652361.296Q67892150791.297Q6912043752.298 Q8701202793.301 Q8701202793.302 Q9634180762.234 00000>01801901>01O01i02B02L02X02]02^03003H03o04?04I04R04S04W04e05605:05B05F06O07X08908E08l09A09O09l0:J0:Z0:_0:`0:a0;90;=0;F0;K0;Z0<A0<B0<P0=V0>40>90>G0>K0>W0?@0?a0?m0@D0@M0@T0@U0@[0@_0@c0A10A20A30A90AB0AL0B00B40Bk0C00C50CF0CG0D20DU0DY0Da0EB0F70G40G;0H?0IC0Jb0LA0Lo0M]0M^0NI0N\0OL0P<0PZ0Q80QK0R[0R\0R]0SK0SL0SM0T;0TT0UM0VF0VG0Ve0WC0X30Xc0Xd0Xe0YS0Zm0\G0]M0^S0_O0_P0_Q0_R0_S0_l0`V0`W0aE0aF0aG0b]0d30eQ0fo0gH0ga0gb0hL0iZ0jh0k>S3SAN2lo5SANLOS1R3HIA3NS13NA13NB14STKn5STKn01h2sp3SAN2lo5SANLO4SLO'1a2HaFS3SANS3SAN2bs2FB5APSANS3sp04slen1q2Lw3Hq13Hq22LRS1R3HIA4FFRn1h4slen1d3FF0S3SAN4SAN0S2sp3sp13SP1S3SANSS3BUF3sp02W11q3Hq1S1R3HIA1h2sp3TOP3sp13SP1S1R3NS13NA13NB14STKn2sp2lo4SLO'3sp13SP1S3SAN3BUF2bs3DSBS3SAN1x2HxS1q2Lw2LRSS2FBS3SAN2FB5APSANS3BUF2bs2FB5APBUFS2spS2LF3LFBS2FBS1R2LF2sp2SB3SAN2bs3LFB4LFB'2FB3sp15nodes2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2SB3SAN2bs3LFB4LFB'2FB3sp15nodes2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R3HIA4PHIn1h4slen2Lw3PHL2h33HV3S2lo2FB4FBLOS2LF2sp2SB3SAN2bs3LFB4LFB'2FB3sp15nodesS1R3HIA1h2sp3TOP4HTOPS3SAN2lo5SANLOS3BUF3sp04slen2bs2W31q2Lw3Hq2S4CNTn4slen2Lw3CNL5nodes5HCNT3S2sp3SPH3sp13SP1S3SANSSS1R3HIA1h2sp2lo3TOP4HTOPS2FBS1R3HIA1hS3SANS4CNTn4slen3CN0S2LF2sp2SB3SAN2bs3LFB4LFB'2FB3sp15nodesSS3SAN2FB5APSANS1R3NS13NA13NB14STKn5STKn02sp3SAN2lo5SANLO4SLO'2FB3sp13SP14FBLO1A1k2HAS1R3HIA4PHIn1h4slen3BUD2Lw3PHLS3SANS3SAN2FB5APSANS2FBS2sp3sp13SP1S1R3NS13NA13NB14STKn5STKn02sp2lo3LOS4SLO'S2LF2sp2SB3SAN2bs3LFB4LFB'2FB3sp1S2sp3sp13SP1S1R3HIA4PHIn1h4slen3PH0S4slen2W2S2FB2F0SS1q2LwS2FBS2spS3SAN2lo5SANLOFFS1i2HiS2FB1c2HcS1R2lo3LOSS1R3HIA4FFRn1h4slen1d2Lw3FFL2h34HFR3S2FBS1R3NS13NA13NB14STKn5STKn02sp2lo3slo4SLOS4SLOL3SPR4SLO'S3sp1S3SANS2r33Hr31r2KR1q1HSS2FB2r03F641q1r1H2H02q02H43SAN2r13ALS2q12H9S2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS2FBS2sp3SPRS1R3HIA4FFRn1h4slen1d4BUDF2Lw3FFLS1R3NS13NA13NB14STKn5STKn02sp2lo3LOS3ALO4SLO'3sp13SP1S1R3NS13NA13NB14STKn5STKn02sp2lo3LOS3ALO3ACV3SPR4SLO'3sp13SP1S2FB2F0S1R2LF3slo2bs4SLOS3LFB4LFB'3ALO2FB3sp12F15nodes2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4SLOS3LFB4LFB'3ALO2FB3sp12F15nodes2HB5Ha_st5Hl_st5SAEstS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB4LFB'4SLO'2FB3sp13SP14FBLO5nodes2HB5Ha_st5Hl_st5SAEstS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB4LFB'4SLO'2FB3sp13SP14FBLO5nodes2HB5Ha_st5Hl_st5SAEstS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stFS2LF2sp2SB3SAN2bs3LFB4LFB'3SPR2FB3sp12F02F8S2LF2bs3LFB4LFB'2FBS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB4LFB'2FB5nodes2HBS1R2LF2bs3LFB4LFB'2FB5nodes2HBS2LF2bs3LFB4LFB'2FBS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB3LOS4LFB'4SLO'2FB5nodes2HB5Ha_st5Hl_stFFS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stFFS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stS2LF2bs3LFB4LFB'2FB5nodesS1R2LF3slo2bs4SLOS3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R2LF3slo2bs4SLOS3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstFS1R2LF2bs3LFB4LFB'2FB5nodes2HBS1R2LF2bs3LFB4LFB'2FB5nodes2HBS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_st5SAEstFFS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB3LOS4LFB'3ALO4SLO'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB3LOS4LFB'3ALO4SLO'2FB5nodes2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs3TOP3LFB4LFB'4HTOP2FB3sp15nodes2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs3TOP3LFB4LFB'4HTOP2FB3sp15nodes2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp2bs3TOP3LFB4LFB'4HTOP2FB5nodes2HB5Ha_st5Hl_stFFFFS2LF2bs3LFB4LFB'2FB5nodesS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stFS1R2LF3SAN2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stFFS1R2LF2sp2SB3SAN2bs3SB04SAN03LFB4LFB'3SPR2FB3sp14SP1R2F02F85nodes2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2SB3SAN2bs3SB04SAN03LFB4LFB'3SPR2FB3sp14SP1R2F02F85nodes2HB5Ha_st5Hl_st5SAEstS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB3LOS4LFB'4SLO'2FB3sp13SP15nodes2HB5Ha_st5Hl_st5SAEstS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3LFB3LOS4LFB'4SLO'2FB3sp13SP15nodes2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB4LFB'2FB5nodesS2LF2bs3LFB4LFB'2FB5nodesFS1R2LF2bs3LFB4LFB'2FB5nodes2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4LFB'4HTOP2FB3sp13SP15nodes2HB5Ha_st5Hl_st5SAEstS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4LFB'4HTOP2FB3sp13SP15nodes2HB5Ha_st5Hl_st5SAEstS2LF2bs3LFB4LFB'2FB2F0". (* [comment removed for export] *)
  Lemma main_call : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m -> HK asegs R HIA h mo0 ->
    rw_cells asegs m SB [C4 tgw; C4 pdw; C8 (Z_to_bv 64 slen); C8 (Z_to_bv 64 sp0)] ->
    rw_cells asegs m SAN [CB 80 (repeat (Z_to_bv 8 0) 80)] -> bytes_at asegs m BUF bs ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m SB 24 -> aobj asegs AL CS m SAN 80 ->
    havol asegs R HIA h + PHIn slen <= AVOL_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    hfr asegs R HIA h + FFRps slen d <= FR_MAX ->
    aevtS asegs (x509_parse_san_postA asegs R HIA PHIn FFRps CNTn h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SAN slen lo slo d m mo0)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 SAN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 A_X509_PARSE_SAN) fc None m (seg_rom asegs)) mo0).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 HSB HSAN HBUF ST SS MI OSB OSAN BUD UW BUDF.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof SLO as SLO'.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO' STKn0 NS1 NA1 NB1 TOP HTOP; lia]).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    pose proof OSAN as CRS; apply aobj_crange in CRS.
    pose proof (PHIn_mono 0 slen ltac:(clear - W2; lia)) as PH0.
    pose proof (FFRn_mono 0 slen (d + 1) ltac:(clear - W2; lia)) as FF0.
    pose proof (CNTn_mono 0 slen ltac:(clear - W2; lia)) as CN0.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk with (STKn := STKn) (lo := lo) (slo := slo) (BUF := BUF) (bs := bs) (sp0 := sp0) (slen := slen) (tgw := tgw) (pdw := pdw); first [ eassumption | match goal with |- ?g => idtac "PRO-PRE-LEFT:" g end ]. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31
                   & junk1 & l1 & l2 & l3 & l4 & j16 & j24 & j48
                   & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FH & HL1 & HL2 & HL3 & HL4 & FSH
                   & SAVE & SL16 & SL24 & SL48 & STK2 & ST1 & MI1 & HSB1 & HSAN1 & HBUF1 & OSB1 & OSAN1 & APSB & APSAN & PRES0 & SS1 & SS2).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 NA1 NB1 STKn0; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & _ & _).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply mid_walk with (STKn := STKn) (lo := lo) (slo := slo) (BUF := BUF) (bs := bs) (sp0 := sp0) (slen := slen) (tgw := tgw) (pdw := pdw) (SB := SB) (h1 := h1); first [ eassumption | match goal with |- ?g => idtac "MID-PRE-LEFT:" g end ]. }
    clear FH HL1 HL2 HL3 HL4 FSH SAVE SL16 SL24 SL48 STK2 ST1 MI1 HSB1 HSAN1 HBUF1 OSB1 OSAN1 PRES0 SS1 SS2 HH1. intros ms2 P2.
    destruct P2 as [EQ | CQ].
    - (* [comment removed for export] *)
      destruct EQ as (m2 & r & t & rest & w0 & w1 & w2 & xra & u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & s3v & s4v & s5v & s6v & s7v & s10v & s11v
                      & u28 & u29 & u30 & u31
                      & -> & Hr & HH2 & MI2 & FH2 & FSH2 & SAVE2 & STK22 & ST12 & HSAN2 & SZR & TR & T4 & OSAN2 & PRES & SS12 & SS22).
      pose proof (presW_init_at R HIA h1 _ _ (SNAME (rev []) ++ LB) LF m2 (bv_unsigned sp) (bv_unsigned sp) [] h HH2
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; rewrite Ehcs; exact Hx) Estk ltac:(clear - LOS SLO' NS1 NA1 NB1 STKn0; lia)) as PRES2.
      intros mo1 [HK1 MF1].
      apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
      eapply san_fin with (hq := h1) (nodes := @nil Z) (dn := 0) (t := t) (rest := rest) (m2x := m2);
        first [ exact HH2 | exact PRES | exact PRES2 | exact T4 | exact Hr | exact CRS | exact CFB | eassumption | reflexivity
              | lazymatch goal with
                | |- forall x, _ -> hcs _ _ _ _ x => intros x Hx; rewrite Ehcs; exact Hx
                | |- havol _ _ _ _ <= _ => rewrite Evol; clear - PH0; lia
                | |- hfr _ _ _ _ <= _ => rewrite Efr; unfold FFRps; clear - FF0; lia
                | |- Z.of_nat (length _) <= _ => cbn [length Z.of_nat]; clear - CN0; lia
                | |- _ -> name_chain _ _ _ _ _ _ => intros _; apply chain_nil
                | |- _ -> [] = [] => intros _; reflexivity
                | |- List.NoDup [] => constructor
                | |- forall x, In x [] -> _ => intros x []
                end
              | match goal with |- ?g => idtac "FIN-A-PRE-LEFT:" g end ].
    - (* [comment removed for export] *)
      destruct CQ as (m3 & q & Lw & w0 & w1 & w2 & z4 & z8 & xra & u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & s6v & s7v & s11v & u28 & u29 & u30 & u31
                      & -> & Hq1 & Hq2 & HH3 & MI3 & FH3 & FSH3 & HLw & HQ & SAVE3 & STK23 & ST13 & HSa & HSn & HSz & HB3 & OSAN3 & PRES & SSlo & SShi).
      pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
      assert (LWS : 0 <= bv_unsigned Lw <= slen) by (clear - LR Hq1 Hq2; lia).
      pose proof (PHIn_mono (bv_unsigned Lw) slen LWS) as PHL.
      pose proof (FFRn_mono (bv_unsigned Lw) slen (d + 1) LWS) as FFL.
      pose proof (CNTn_mono (bv_unsigned Lw) slen LWS) as CNL.
      assert (CWS1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) SAN 80).
      { eapply client_wrange_mono; [exact CWS| intros b Hb; apply fdata_cons_sub; exact Hb]. }
      assert (CWN1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) (SAN + 8) 64).
      { eapply client_wrange_inside; [exact CWS1| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) (FB + 128) 8).
      { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m3 PRES) as HP13.
      assert (UW3 : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply uwc_presA; [exact HP13| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO' SPR NS1 NA1 NB1 STKn0; lia].
        intros a Ha. cbn [outside]. split; [| exact I]. clear - Ha SANLO SLO' NS1 NA1 NB1 STKn0; lia. }
      assert (UWF : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
      { pose proof SAVE3 as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
        replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
        eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW3| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
      clear HP13 UW3.
      frame_aobj FSH3 (FB + 128) 1%nat as OPL3.
      assert (ONM3 : aobj asegs AL CS m3 (SAN + 8) 64) by (eapply aobj_sub; [exact OSAN3| clear; lia| clear; lia]).
      pose proof (F3 _ _ ltac:(apply in_app_iff; left; exact BIN)) as APBUF.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
      (* [comment removed for export] *)
      zstep.
      idtac "GETNAME-CALL".
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply GETNAME with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (PP := FB + 128) (CUR := SAN + 8) (P := q) (END := q + bv_unsigned Lw)
                            (BUF := BUF) (bs := bs) (lo := lo) (slo := slo) (d := d + 1)
                            (j48 := repeat (Z_to_bv 8 0) 48) (mg := Z_to_bv 8 0) (pad7 := repeat (Z_to_bv 8 0) 7);
          rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr; unfold NAME_SIZE;
          replace (q + bv_unsigned Lw - q) with (bv_unsigned Lw) by (clear; lia);
          first [ exact HH3 | exact HB3 | exact BIN | exact HQ | exact HSn | exact OPL3 | exact ONM3 | exact CWN1 | exact CWP1 | exact ST13 | exact SSlo | exact SLOS | exact SLOL | exact MI3 | exact TPV | exact NDL | exact UWF | exact B47 | exact BUF0 | exact BSMALL | reflexivity
                | lazymatch goal with
                  | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                  | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                  | |- BUF <= q => clear - W1 Hq1; lia
                  | |- q <= q + _ => clear - LR; lia
                  | |- q + _ <= BUF + _ => clear - Hq2 W3; lia
                  | |- lo <= sp1 - STKn => clear - SLO' SP1 NS1 NA1 NB1 STKn0; lia
                  | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                  | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                  | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD PHL; lia
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRps in BUDF; clear - BUDF FFL; lia
                  | |- _ mod 8 = 0 => clear - F64 ALS; Z.div_mod_to_equations; lia
                  | |- 0 < _ => clear - F0 SAN0; lia
                  | |- _ + _ <= lo => clear - FBLO SANLO; lia
                  | |- _ \/ _ => clear - APBUF DSB APSAN; cbn [fst snd] in *; lia
                  end
                | match goal with |- ?g => idtac "GETNAME-PRE-LEFT:" g end ]. }
      cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
      idtac "GETNAME-POST".
      destruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo4' & h3 & r3 & p' & j48' & mg' & pad7' & nodes
                      & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HPP4 & Hp' & HCUR4 & NC4 & ND4 & APN4 & HH4 & RN4).
      injection E4 as Ems Emo. subst ms4 mo4 qa0.
      replace (ret_pc (Z_to_bv 64 0xaf180)) with (Z_to_bv 64 0xaf180 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
      replace (q + bv_unsigned Lw - q) with (bv_unsigned Lw) in HV3, HFR3, HCNT3 by (clear; lia).
      rewrite Ehtop in HT3. rewrite Estk in HS3, HP4. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3. unfold NAME_SIZE in HP4.
      assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
      pose proof (hcs_ok asegs R HIA h3) as CSOK3.
      (* [comment removed for export] *)
      assert (HP4' : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) [(SAN + 8, SAN + 8 + 64)] m3 m4).
      { eapply (presA_drop_fresh_gen R LB LF _ _ _ [(SAN + 8, SAN + 8 + 64)] FB 256 (FB + 128) (FB + 128 + 8)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO' SP1 NS1 NA1 NB1 STKn0; lia].
        eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      (* [comment removed for export] *)
      assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m4).
      { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
        eapply presA_trans; [exact P0|].
        eapply presA_weaken; [exact HP4'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
      (* [comment removed for export] *)
      pose proof (fresh_apart_grow R HIA h3 (SNAME (rev nodes)) LB LF m4 FB 256 FRSH HH4) as FRSH3.
      pose proof (presW_init_at R HIA h3 _ _ (SNAME (rev nodes) ++ LB) LF m4 (bv_unsigned sp) (bv_unsigned sp) [] h HH4
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSh3 HS3 ltac:(clear - LOS SLO' NS1 NA1 NB1 STKn0; lia)) as PRES2.
      (* [comment removed for export] *)
      assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
      { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
      apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(FB + 128, FB + 128 + 8); (SAN + 8, SAN + 8 + 64)] m3 m4 FB _ CSOK) in FSH3;
        [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
      apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) _ m3 m4 FB _ HP4) in FH3;
        [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
         | cbn [disjoint_from cells_size csize Nat.add]; clear - APSAN; lia ].
      assert (DJ : forall A k, sp1 <= A -> disjoint_from [(FB + 128, FB + 128 + 8); (SAN + 8, SAN + 8 + 64)] A k).
      { intros A k HA. cbn [disjoint_from]. clear - HA FBLO SANLO SLO' NS1 NA1 NB1 STKn0 SP1. lia. }
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SAVE3; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
      apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in STK23; [| clear; lia| apply DJ; clear; lia].
      apply (presA_sshad asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SShi; [| clear; lia| clear - HTOP TOP; lia].
      (* [comment removed for export] *)
      assert (CWSa : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) SAN 8).
      { eapply client_wrange_inside; [exact CWS1| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      assert (CWSz : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h) (SAN + 72) 8).
      { eapply client_wrange_inside; [exact CWS1| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      pose proof (client_range_lower L _ lo sp1 SAN 8 (client_range_of_w L _ _ _ _ _ CWSa) ltac:(clear - SANLO; lia)) as CRSa.
      pose proof (client_range_lower L _ lo sp1 (SAN + 72) 8 (client_range_of_w L _ _ _ _ _ CWSz) ltac:(clear - SANLO; lia)) as CRSz.
      apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) _ m3 m4 SAN _ HP4) in HSa;
        [| exact CRSa | cbn [disjoint_from cells_size csize Nat.add]; clear - APSAN; lia ].
      apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) _ m3 m4 (SAN + 72) _ HP4) in HSz;
        [| exact CRSz | cbn [disjoint_from cells_size csize Nat.add]; clear - APSAN; lia ].
      unfold name_blob in HCUR4.
      clear HP4 HP4' DJ OSAN3 OPL3 ONM3 HB3 MI3 ST13 SSlo PRES HH3 HLw HQ HSn HPP4.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
      clear HK1 MF1 MF4 mo1.
      assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCSh3| exact CFB]).
      assert (CRS3 : crange (hcs asegs R HIA h3) SAN 80) by (eapply crange_mono; [exact HCSh3| exact CRS]).
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSh3| exact SCS]).
      assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSh3| exact SCS0]).
      destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (SNAME (rev nodes) ++ LB) LF m4 FB 256 lo HH4 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (_ & _ & INH3 & IND3 & AP3 & _ & _ & _ & SBND & APS). change (256 / 8) with 32 in SBND, APS.
      pose proof (art_stk_high asegs R HIA) as STKH.
      pose proof (hm_wlow asegs R HIA h3 _ _ _ HH4) as WL3.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
      idtac "RET-STORES-DONE".
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m5 end.
      lazymatch goal with A1 : rw_cells _ m5 SAN _, A2 : rw_cells _ m5 (SAN + 8) _, A3 : rw_cells _ m5 (SAN + 72) _ |- _ =>
        chunk_join A1 A2 A12; chunk_join A12 A3 HSAN5 end.
      assert (SZR : Z.of_nat (cells_size (CB 4 z4 :: name_blob j48' (hd 0 nodes) mg' pad7' ++ [CB 8 z8])) = 76) by reflexivity.
      (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        idtac "RET-ERR".
        eapply san_fin with (hq := h3) (nodes := nodes) (dn := hd 0 nodes) (t := 4) (r := r3) (m2x := m4)
                            (rest := CB 4 z4 :: name_blob j48' (hd 0 nodes) mg' pad7' ++ [CB 8 z8]);
          first [ exact HH4 | exact HCSh3 | exact HT3 | exact HS3 | exact HF3 | exact PRES2 | exact CFB | exact CRS | exact SZR | exact ND4 | exact APN4 | exact RN4 | exact Hr3
                | (unfold name_blob; cbn [app]; eassumption) | eassumption | reflexivity
                | lazymatch goal with
                  | |- havol _ _ _ _ <= _ => clear - HV3 PHL; lia
                  | |- hfr _ _ _ _ <= _ => unfold FFRps; clear - HFR3 FFL; lia
                  | |- Z.of_nat (length _) <= _ => clear - HCNT3 CNL; lia
                  | |- _ -> name_chain _ _ _ _ _ _ => intros _; exact NC4
                  | |- _ -> exists _, _ => intros _; exists z4, j48', mg', pad7', z8; reflexivity
                  | |- 4 <> 4 -> _ => intros X; exfalso; apply X; reflexivity
                  | |- 0 <= 4 <= 7 => clear; lia
                  end
                | match goal with |- ?g => idtac "FIN-B1-PRE-LEFT:" g end ].
      + (* [comment removed for export] *)
        idtac "RET-OK".
        assert (R30 : r3 = 0).
        { try (change 18446744073709551615 with (Z.ones 64) in KR; rewrite Z.land_ones in KR by (clear; lia)).
          rewrite ?Z_to_bv_unsigned in KR. unfold bv_wrap, bv_modulus in KR. cbn [Z.pow Z.of_N Pos.pow] in KR.
          clear - KR Hr3. Z.div_mod_to_equations. lia. }
        zstep. zstep.
        eapply san_fin with (hq := h3) (nodes := nodes) (dn := hd 0 nodes) (t := 4) (r := 0) (m2x := m4)
                            (rest := CB 4 z4 :: name_blob j48' (hd 0 nodes) mg' pad7' ++ [CB 8 z8]);
          first [ exact HH4 | exact HCSh3 | exact HT3 | exact HS3 | exact HF3 | exact PRES2 | exact CFB | exact CRS | exact SZR | exact ND4 | exact APN4
                | (unfold name_blob; cbn [app]; eassumption) | eassumption | reflexivity
                | lazymatch goal with
                  | |- havol _ _ _ _ <= _ => clear - HV3 PHL; lia
                  | |- hfr _ _ _ _ <= _ => unfold FFRps; clear - HFR3 FFL; lia
                  | |- Z.of_nat (length _) <= _ => clear - HCNT3 CNL; lia
                  | |- _ -> name_chain _ _ _ _ _ _ => intros _; exact NC4
                  | |- _ -> exists _, _ => intros _; exists z4, j48', mg', pad7', z8; reflexivity
                  | |- 4 <> 4 -> _ => intros X; exfalso; apply X; reflexivity
                  | |- 0 <> 0 -> _ => intros X; exfalso; apply X; reflexivity
                  | |- 0 <= 4 <= 7 => clear; lia
                  | |- _ < 0 <= 0 => clear; lia
                  end
                | match goal with |- ?g => idtac "FIN-B2-PRE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Theorem A_x509_parse_san_spec : x509_parse_san_stmtA asegs R HIA PHIn FFRps CNTn STKps (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Proof.
    unfold x509_parse_san_stmtA. intros until pdw. intros; subst. unfold buf_cells in *. eapply main_call; first [eassumption | reflexivity].
  Qed.
End Walk.

(* [comment removed for export] *)
