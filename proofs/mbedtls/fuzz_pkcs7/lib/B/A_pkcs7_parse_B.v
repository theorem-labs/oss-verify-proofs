(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_asn1_get_alg_null_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_parse_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01058bed7b173478 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P013c27b525298c75 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P022be7761bafd124 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P06f1605d653af67c 0 3 0 1 37 1 145 1P072b17ed445a1a05 0 3 0 1 37 1 145 1P07bb071c7f5f1039 0 3 0 1 37 1 145 1P08abafc943582465 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P0ad3c6eddc990e4a 0 3 0 1 37 1 145 1P0d1db0352f39540f 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P0fb39e995652f468 0 2 0 1 26 1P10ef7ebdf4edc8de 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P13d626ea299cfa53 0 3 0 1 37 1 133 1P1503d88b375680e4 0 3 0 1 37 1 145 1P1827db32dc491618 0 3 0 1 37 1 145 1P1a8ed55b61f9d0ed 0 2 0 1 25 1P1d81667b7045c9d3 1 1 64 2 0 1 145 1 3 2 1 146 1 147 64P1f3321eaf45e6b20 0 12 0 1 111 1 114 1 116 1 121 1 123 1 127 1 135 1 136 1 137 1 146 1 147 1P1f85f8b97249ade8 0 4 0 1 23 1 157 1 158 1P23f94d318acf3da3 0 3 0 1 37 1 145 1P246e5f88c2a8edff 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P24d5e2a0bcf97de0 1 1 64 2 1 1 145 1 3 0 1 146 1 147 64P27a3fcc10339666b 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P27e8233019fd151e 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P2de01cda676f5ac2 0 3 0 1 37 1 145 1P30c7c4c18da8400b 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P31e0c6f49f6d796e 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P327d87eef93c8fd8 0 8 0 1 110 1 113 1 115 1 120 1 134 1 135 1 136 1P32b54ebd43c1549d 0 3 0 1 37 1 145 1P370d6b3853a6c3cd 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P3778b24adec23e7b 0 3 0 1 37 1 145 1P39308e78ffa58fe8 0 4 0 1 23 1 157 1 158 1P3a2c7130756f6e1d 0 8 0 1 122 1 125 1 127 1 132 1 146 1 147 1 148 1P3cf71ed112f9de2d 0 3 0 1 37 1 145 1P3ddfaf2babc2fa64 0 3 0 1 37 1 145 1P3e36e78c5f6df956 0 3 0 1 37 1 145 1P3f7892ce589a11dd 1 1 64 2 123 1 146 1 3 0 1 145 1 147 64P3fa1fb072611244b 0 9 0 1 24 1 122 1 125 1 127 1 132 1 146 1 157 1 158 1N00e294bf3ddda1ffN057746ee0d695eeeN08c06178a29d9316N0931c80682f460fbN09f5e2a47909d8eaN0a1f4d755aa2834aN0aa324bf07706948N0ba3a85b46231711N0f21b0807543487fN0ff53de174e8b962N133a292cdf44264cN142c4ae76f360f9fN14ace42fbcd96301N14f6001f77a548b9N1695bff2f292801cN1878c12d7df46b25N18c2a9f49151fa47N19a9259160b67e8bN1ab2df62e2240786N1acb658abdf1d482N1f4361549965e986N2019d2cad4357a5fN28750d8341790071N29d90f2e390196bdN2a586829785990acN2a7ef426c44bf04dN2b4d54b3ba661d19N2d974d0488897ee1N2e9eff24348d015bN34cd88db4795e65dN360f8c4cee49b80bN3716b44acc2dff62N393d50679f17e933N398828e22b1c4d11N39b40ad6dad89c82N3a734440384633c0N3d6ba025912fffd0N3e2bc1741600ad3aN3e824dbc004328c9"%lxh.
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
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable PK : pk_class asegs.
  Variable SI : sinv (arl_L R).
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIg : Z -> Z) (FFRg : Z -> Z -> Z) (CNTg : Z -> Z) (STKg : Z).
  Hypothesis GETCERTS : pkcs7_get_certs_stmtA_c asegs R HIA PK SI PHIg FFRg CNTg STKg A_PKCS7_GETCERTS.   (* [comment removed for export] *)
  Variables (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z) (STKs : Z).
  Hypothesis GETSIGNERS : pkcs7_getsigners_stmtA asegs R HIA PHIs FFRs CNTs STKs A_PKCS7_GETSIGNERS.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Variables (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PKFREE : pkcs7_free_stmtA asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIg_mono : forall n n', 0 <= n <= n' -> 0 <= PHIg n <= PHIg n'.
  Hypothesis FFRg_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRg n d <= FFRg n' d.
  Hypothesis CNTg_mono : forall n n', 0 <= n <= n' -> 0 <= CNTg n <= CNTg n'.
  Hypothesis PHIs_mono : forall n n', 0 <= n <= n' -> 0 <= PHIs n <= PHIs n'.
  Hypothesis FFRs_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRs n d <= FFRs n' d.
  Hypothesis CNTs_mono : forall n n', 0 <= n <= n' -> 0 <= CNTs n <= CNTs n'.
  Hypothesis PHIj_mono : forall n n', 0 <= n <= n' -> 0 <= PHIj n <= PHIj n'.
  Hypothesis FFRj_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRj n d <= FFRj n' d.
  Hypothesis CNTj_mono : forall n n', 0 <= n <= n' -> 0 <= CNTj n <= CNTj n'.
  Hypothesis PHIj_joint : forall a b, 0 <= a -> 0 <= b -> PHIg a + PHIs b <= PHIj (a + b).
  Hypothesis FFRj_joint : forall a b d, 0 <= a -> 0 <= b -> FFRg a d + FFRs b d <= FFRj (a + b) d.
  Hypothesis CNTj_joint : forall a b, 0 <= a -> 0 <= b -> CNTg a + CNTs b <= CNTj (a + b).
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis STKg0 : 0 <= STKg. Hypothesis STKs0 : 0 <= STKs. Hypothesis STKf0 : 0 <= STKf.
  (* [comment removed for export] *)
  Local Notation STKp := (STKp R STKg STKs STKf).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (A DATA n lo slo d : Z) (bs : list byte).
  Hypothesis P7Z : pkcs7_zero asegs m A.
  Hypothesis AAL : A mod 8 = 0.
  Hypothesis A0 : 0 < A.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A PKCS7_SIZE.
  Hypothesis ASTK : A + PKCS7_SIZE <= arl_stklo R.
  Hypothesis AOD : A + PKCS7_SIZE <= hl_data_lo L \/ hl_data_hi L <= A.
  Hypothesis HBY : bytes_at asegs m DATA bs.
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2 ^ 26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CRD : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis DA : n = 0 \/ A + PKCS7_SIZE <= DATA \/ DATA + n <= A.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKp.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 33)%nat.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L15273424461.9900000aS1R2LF2sp1A1n2lo3slo2bs2A03LEN4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
  Let ALO1 : A + PKCS7_SIZE <= lo. Proof. pose proof LOS. pose proof ASTK. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2 in SM2; unfold A_pkcs7_parse_A.STKp in SLO; unfold PKCS7_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBn : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z) (cb : list byte)
      : machine_state -> Prop := fun ms =>
    exists (m' : mem) (h4 : HST asegs R HIA) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ a0 = Z_to_bv 64 r
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ sshad asegs AL m' slo (bv_unsigned sp)
      /\ presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m0 m'
      /\ presW asegs R HIA h3 (LBn ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x m'
      /\ hcs asegs R HIA h4 = hcs asegs R HIA h3 /\ htop asegs R HIA h4 = htop asegs R HIA h3
      /\ hstkhi asegs R HIA h4 = hstkhi asegs R HIA h3 /\ hflag asegs R HIA h4 = hflag asegs R HIA h3
      /\ havol asegs R HIA h4 = havol asegs R HIA h3 /\ hfr asegs R HIA h4 = hfr asegs R HIA h3
      /\ (forall mo, HK asegs R HIA h4 mo <-> HK asegs R HIA h3 mo)
      /\ HM asegs R HIA h4 (LBn ++ LB) LF m'
      /\ rw_cells asegs m' A [CB 1440 cb].

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DA; try lx_pin1 DLO; try lx_pin1 CRD; try lx_pin1 HD; try lx_pin1 Hn; try lx_pin1 HBY; try lx_pin1 AOD; try lx_pin1 AAL; try lx_pin1 P7Z; try lx_pin1 d; try lx_pin1 DATA; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 STKf0; try lx_pin1 STKs0; try lx_pin1 FFRf_mono; try lx_pin1 PHIf_mono; try lx_pin1 CNTj_joint; try lx_pin1 FFRj_joint; try lx_pin1 PHIj_joint; try lx_pin1 CNTj_mono; try lx_pin1 FFRj_mono; try lx_pin1 PHIj_mono; try lx_pin1 CNTs_mono; try lx_pin1 FFRs_mono; try lx_pin1 PHIs_mono; try lx_pin1 CNTg_mono; try lx_pin1 FFRg_mono; try lx_pin1 PHIg_mono; try lx_pin1 PKFREE; try lx_pin1 FFRf; try lx_pin1 PHIf; try lx_pin1 CNTj; try lx_pin1 FFRj; try lx_pin1 PHIj; try lx_pin1 GETSIGNERS; try lx_pin1 CNTs; try lx_pin1 FFRs; try lx_pin1 PHIs; try lx_pin1 GETCERTS; try lx_pin1 CNTg; try lx_pin1 FFRg; try lx_pin1 PHIg; try lx_pin1 GETTAG; try lx_pin1 SI; try lx_pin1 PK; try lx_pin1 HMND; try lx_pin1 DIMG; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01V0@D16049649465.172D2459793318.171 D30009943146.172D31762839151.172D32452690557.171D3374278032.170 D43016287773.172D45715803169.170D60109265003.172D62011770188.172D66251787523.171D68405837779.170D6909504982.170 L18271036607.160L19546883927.153L19546883930.157L2333531081.147 L2333536794.147 L24876536089.278L26163319614.147L26163329773.147L30443668812.13 L35655538631.13 L38077847203.1  L39844638933.0  L41486840212.2  L42411609006.0  L48117620902.154L48117620903.155L48117620904.151L48117620907.150L48911768491.1  L5070094962.153 L5070094975.157 L50790731766.13 L57124690773.0  L59578101107.175L60098763854.6  L61745680213.291L61954813795.290L62018535662.1  L6302880071.147 L6302890132.147 L64850595401.0  L65276887188.154L65276887193.150L6912107235.154 L6912107246.150 L9356559676.18  P41479713552.284Q10592386204.176Q10592386207.180Q11450412596.177Q11450412601.181Q16178749881.176Q16178749882.180Q22358563588.179Q23925414039.186Q25138220955.282Q27881326168.177Q28177601872.181Q30147450662.177Q31314676345.175Q31762839142.181Q31762839147.177Q34796740410.180Q37704033339.184Q38250992820.185Q39028748170.282Q4125667684.281 Q42439443119.283Q42441479406.188Q4279611329.283 Q43878048872.185Q48117620905.180Q48117620906.176Q48132302223.179Q48132302231.175Q49293189221.177Q49293189224.181Q5935758158.283 Q59668625896.181Q60382659730.181Q60382659743.177Q62009673039.186Q64133651577.282Q64681502663.188Q64683667846.283Q65266402725.175Q65266402749.179Q65276887188.181Q65276887193.177Q65276888093.183Q67397950268.176Q6897428426.179 Q6897428434.175 Q6912107235.181 Q6912107246.177 Q6912108138.183 Q7917062807.181 Q7917062810.177 Q8425816089.184 00000100200300400W00X01B01e02O03203U03V04904k05T06=06>06?06g06h06i07W08?08C08D08E08F09>0:60:n0;f0;j0<X0=F0>40>50>]0>g0?_0@T0@W0@X0@Y0@Z0A90AX0B70BV0CT0CU0D40DS0DT0DU0E40ES0ET0F60FZ0F[0F\0F]0F^0F_0F`0Fa0G?0G^0HB0Hc0IM0J20JS0K50Km0Le0M]0NU0NV0NW0O80O90O:0O;0OW0P80Pk0Qc0RB0Ra0S@0S_0T>0T?0T^0U=0U\0V;0VZ0W@0Wf0XDFFFFS1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp1FS1R3HIA4STKg4STKs4STKf2LF2bs3LFB2h32FB3sp1S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp1S1R4STKg4STKs4STKf2LF2lo2bs3LFB3LOS2FB3sp1S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp1S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp1FS1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp1S1R4STKg4STKs4STKf2LF2sp3slo2bs4SLOS3LFB2FB3ALO2F1S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp12F82F0S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp12F82F0FFS1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp11p2PBFFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP5HTOP3S2spSFSS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp14SP1R2F82F0S1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp14SP1R2F82F0S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSSS1R4STKg4STKs4STKf2LF2bs3LFB2FB3sp11c2HcS1R2lo3LOSS1R4STKg4STKs4STKf2LF2sp2lo2bs3SLO3LFB2FB3sp13SP12F03H20S1R4STKg4STKs4STKf2LF2sp2lo2bs3SLO3LFB2FB3sp14SP1R2F0S1RFFSS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBFFS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBFS1R3HIA4STKg4STKs4STKf1h2LF2bs3LFBS1R4STKg4STKs4STKf2LF2bs3LFB2FB1p2PBFFFFFFFS1R4STKg4STKs4STKf2LF1A2bs3LFBS1R4STKg4STKs4STKf2LF2lo2bs3LFBS1R4STKg4STKs4STKf2LF2bs3LFB2FB1p2PBS1R4STKg4STKs4STKf2LF2bs3LFB1p2PBS1R4STKg4STKs4STKf2LF3slo2bs4SLOS3LFB1p2PBS1R4STKg4STKs4STKf2LF3slo2bs4SLOS3LFBS1R4STKg4STKs4STKf2LF2bs3LFB1p2PBS1R4STKg4STKs4STKf2LF2sp2lo2bs3LFBS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOFFS1R4STKg4STKs4STKf2LF2bs3LFB1p2PBFFFS1R4STKg4STKs4STKf2LF2bs3LFBS1R4STKg4STKs4STKf2LF2bs3LFB1p2PBS1R3HIA4STKg4STKs4STKf1h2LF2sp3slo2bs3TOP3LFB5HTOP3S1R3HIA4STKg4STKs4STKf1h2LF2sp3slo2bs3TOP3LFB5HTOP31p2PBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBFS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FBS1R4STKg4STKs4STKf2LF2bs3LFB2FB3ALO2F1S1R4STKg4STKs4STKf2LF2bs3LFB2FB3ALO2F1S1R4STKg4STKs4STKf2LF1A2bs3LFB". (* [comment removed for export] *)
  #[using="ALO1 LOS LFB SPH TOP SLO SLOL SLOS LEN ASTK CWA A0 bs n STKg0 STKf STKs STKg NS1 IMG"]
  Lemma epi_walk : forall (h3 : HST asegs R HIA) (LBn : list blk) (m0 m2x mm : mem) (WA WB : list ivl) (FB sp1 : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s5v s6v s8v s9v w0 w1 w2 : word)
      (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte)
      (r : Z) (cb : list byte),
    HM asegs R HIA h3 (LBn ++ LB) ((FB, 256) :: LF) mm ->
    (forall x, CS x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h -> hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 -> sp1 mod 32 = 0 ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 256 -> fresh_apart R (LBn ++ LB) LF FB 256 -> crange CS FB 256 ->
    (forall B j, In (B, j) LF -> FB + 256 <= B \/ B + j <= FB) ->
    rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL)
      [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
       C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31] ->
    rw_cells asegs mm (bv_unsigned sp + -104) SAVEL ->
    stk asegs mm sp1 (bv_unsigned sp + -104) ->
    stk asegs mm lo sp1 -> mem_inv asegs mm ->
    presW asegs R HIA h3 LB LF (bv_unsigned sp) (bv_unsigned sp) WA m0 mm ->
    presW asegs R HIA h3 (LBn ++ LB) LF (bv_unsigned sp) (bv_unsigned sp) WB m2x mm ->
    sshad asegs AL mm slo (bv_unsigned sp) ->
    rw_cells asegs mm A [CB 1440 cb] -> crange CS A 1440 -> (FB + 256 <= A \/ A + 1440 <= FB) ->
    -2^31 <= r < 2^31 ->
    evtA asegs AL (hcs asegs R HIA h3) (EPOST h3 LBn m0 m2x WA WB r cb)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               s2v (Z_to_bv 64 (-8)) (Z_to_bv 64 r) s5v s6v (Z_to_bv 64 FB) s8v s9v
               (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
          F (Z_to_bv 64 0x97ae8) fc None mm (seg_rom asegs)).
  Proof.
  intros until cb.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP FHD FSH SAVE ST1 STlo MI PRES PRES2 SS HA CRA APPA Hr.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 256) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (CRA3 : crange (hcs asegs R HIA h3) A 1440) by (eapply crange_mono; [exact HCS3| exact CRA]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKg0 TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBn ++ LB) LF mm FB 256 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x97b84] [] 557%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBn ++ LB) ((FB, 256) :: LF) me FB 256 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 256 - 8) with (FB + 248) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 256) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBn ++ LB) ++ fdata LF) -> In b ((LBn ++ LB) ++ fdata ((FB, 256) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ lo (arl_stklo R) p A 1440 NCp (client_range_of_w L _ _ _ _ _ CWA) SUB1 LOS ltac:(clear; lia)) as NP1.
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NS1 STKg0; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NS1 STKg0; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBn ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NS1 STKg0; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 15 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split.
  {
  (* [comment removed for export] *)
        first [ reflexivity
              | apply bv_eq; try (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia)); rewrite ?Z.add_0_r;
                rewrite ?Z_to_bv_unsigned; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
                change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648; change (2 ^ Z.of_N 64) with 18446744073709551616;
                clear - Hr; Z.div_mod_to_equations; lia
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SEXT-LEFT:" g end ].
  }
  split; [assumption|].
  split.
  {
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
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
  End Call.
End Walk.
