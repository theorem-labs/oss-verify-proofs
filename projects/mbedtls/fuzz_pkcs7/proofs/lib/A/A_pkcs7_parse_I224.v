(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int
     A_asn1_get_alg_null_A A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_asn1_get_int_loops.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_pkcs7_top24 A_pkcs7_getcerts_stmt24 A_pkcs7_parse_A A_pkcs7_parse_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24 A_pkcs7_parse_H24.
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
  Variable C24c : Z.   (* [comment removed for export] *)
  Hypothesis C24c0 : 0 <= C24c.
  Hypothesis GETCERTS : pkcs7_get_certs_stmtA24 asegs R HIA PK SI PHIg FFRg CNTg STKg C24c A_PKCS7_GETCERTS.
  Variables (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z) (STKs : Z).
  Hypothesis GETSIGNERS : pkcs7_getsigners_stmtA asegs R HIA PHIs FFRs CNTs STKs A_PKCS7_GETSIGNERS.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Variables (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PKFREE : pkcs7_free_stmtA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) PHIf FFRf STKf A_PKCS7_FREE.
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
  Hypothesis AMS : arl_amemset R = A_AMEMSET_F.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis CINFO : pkcs7_cinfo_stmtA asegs R HIA A_PKCS7_CINFO_G.
  Hypothesis ALGNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL_G.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG_G 48.
  Hypothesis GETINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT_G.
  Hypothesis NEXTLEN : pkcs7_nextlen_stmtA asegs AL A_PKCS7_NEXTLEN_G.
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.56000007S1R3NA0". (* [comment removed for export] *)
  Let NRT : arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R. Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
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
  Hypothesis C24H : cnt24 LB + 1 + 2 * (n / 5889) + C24c <= C24MAX.     (* [comment removed for export] *)
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.11200000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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

  Local Notation CNTp := (CNTp CNTj).
  Local Notation PHIp := (PHIp PHIj CNTj PHIf).
  Local Notation FFRp := (FFRp FFRj CNTj FFRf).
  Local Notation POST := (pkcs7_parse_der_postA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) SI PHIp FFRp CNTp
                            h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n lo slo d m mo0).
  Local Notation X0 := [(A, A + 1440)].
  Local Notation dvA := (dvA R HIA SI h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 A n lo slo).
  Local Notation tailP := (tailP R HIA PK SI PHIj FFRj CNTj PHIf FFRf h LB A n d).
  (* [comment removed for export] *)
  Local Notation FSHGL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Ltac dvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SIc & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & G8 & G12 & G16 & G18 & G22 & FSH & SAVE & RSL
                   & STa & STb & STlo & CELLS & SZC & OBJA & MIc & SSc & C24i).
  Ltac dvA_build :=
    cbv delta [A_pkcs7_parse_C24.dvA] beta;
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity
          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
          | match goal with HKI : forall mo, HK _ _ _ _ mo <-> HK _ _ _ _ mo |- HK _ _ _ _ _ => apply (proj2 (HKI _)); assumption end
          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA-LEFT:" g end ] ].
  (* [comment removed for export] *)
  Ltac tail_prep :=
    rt_facts;
    lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) ((?FB, 256) :: LF) ?mc |- _ =>
      pose proof (hcs_ok asegs R HIA hc) as CSOKc;
      pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT;
      lazymatch goal with HTc : htop _ _ _ hc = _, HSc : hstkhi _ _ _ hc = _, HCSc : forall x, CS x -> hcs _ _ _ hc x, CFB : crange CS FB 256, OBJA : aobj _ _ CS mc A 1440, FRSH : fresh_apart R LB LF FB 256, F64 : FB mod 64 = 0, SCS0 : crange CS (arl_stklo R) _ |- _ =>
        rewrite HTc, HSc in HT;
        pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc;
        pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c;
        pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJA) as OBJc;
        pose proof OBJA as CRA; apply aobj_crange in CRA;
        pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 256 FRSH HHc) as FRSH3;
        destruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 256 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
          as (_ & INF & INH & IND & AP & _ & F8 & FBLO & SBND & APS); change (256 / 8) with 32 in SBND, APS;
        pose proof FRSH as FRSH'; unfold fresh_apart in FRSH'; destruct FRSH' as (F0 & F1 & F2 & F3);
        pose proof (frame_apart_obj R HIA LB LF lo _ A 1440 FB 256 FRSH CWA ltac:(clear; lia) ltac:(clear; lia) LOS) as APPA;
        pose proof (art_stk_high asegs R HIA) as STKH;
        assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKg0 STKs0 STKf0 TOP HT; lia]);
        pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc
      end end.

  (* [comment removed for export] *)
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (S ?k)] => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by (clear; lia) end.
  Ltac joinr H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn [cells_size csize Nat.add length]; clear; lia);
      let Hj := fresh "J" in
      pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
      cbn [app] in H1
    end end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := eval cbv beta iota delta [firstn] in (firstn k cs) in
      let l2 := eval cbv beta iota delta [skipn] in (skipn k cs) in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
    end.

  Local Notation rep0_buildF := (rep0_build R PK STKg STKs STKf LB LF sp A n lo slo bs AAL A0 ASTK LEN Hn SLOS SLOL SLO LFB).
  Local Notation bytes_at_sliceF := (bytes_at_slice LF sp A n bs A0 Hn LFB).

  (* [comment removed for export] *)
  Ltac si_now :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      first [ match goal with SI0 : si_P SI mx |- _ => idtac end
            | match goal with P2 : presW _ _ _ _ _ _ _ _ [(A, A + 1440)] ?m0 mx, SI0 : si_P SI ?m0 |- _ =>
                let SIx := fresh "SIx" in
                assert (SIx : si_P SI mx)
                  by (eapply (si_heap_presx asegs L SI); [exact SI0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ P2))|];
                      intros a Ha; exact (si_outside1 L SI A 1440 a AOD Ha)) end
            | idtac "si_now: no bundle" ]
    end.

  (* [comment removed for export] *)
  Ltac blob8 H := apply rw_cells_blob in H; cbn [cells_size csize cells_bytes cbytes app Nat.add] in H; rewrite ?app_nil_r in H.
  Ltac dv_shapes :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      repeat match goal with
             | H : rw_cells _ mx (?FB + 32) [C8 _] |- _ => blob8 H
             | H : rw_cells _ mx (?FB + 64) [C8 _] |- _ => blob8 H
             | H : rw_cells _ mx (?FB + 96) [C8 _] |- _ => blob8 H
             | H : rw_cells _ mx (?FB + 144) [C8 _] |- _ => blob8 H
             | H : rw_cells _ mx (?FB + 176) [C8 _] |- _ => blob8 H
             end;
      try (lazymatch goal with E1 : rw_cells _ mx (?FB + 128) [C4 _], E2 : rw_cells _ mx (?FB' + 132) [CB 4 _] |- _ =>
             joinr E1 E2; apply rw_cells_blob in E1; cbn [cells_size csize Nat.add] in E1 end);
      try (lazymatch goal with CA : rw_cells _ mx (A + 32) (buf_cells _ _ _ _) |- _ => unfold buf_cells in CA end);
      try (lazymatch goal with CA : rw_cells _ mx (A + 32) [C4 _; C4 _; C8 ?w1; C8 ?w2], CT : rw_cells _ mx (A + 56) _, CP : rw_cells _ mx A _ |- _ =>
             (lazymatch w1 with Z_to_bv 64 _ => idtac | _ => rewrite <- (Z_to_bv_bv_unsigned w1) in CA end);
             (lazymatch w2 with Z_to_bv 64 _ => idtac | _ => rewrite <- (Z_to_bv_bv_unsigned w2) in CA end);
             joinr CP CA; joinr CP CT end)
    end.

  (* [comment removed for export] *)
  Ltac rawb_now :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      first [ match goal with RB : rw_cells _ mx ?rawp [CB (Z.to_nat n) bs] |- _ => idtac end
            | match goal with P2 : presW _ _ _ ?hq ?LBq LF _ _ [(A, A + 1440)] ?m0 mx, RBb : rw_cells _ ?m0 ?rawp [CB (Z.to_nat n) bs] /\ True,
                               RINq : In (?rawp, n) ?LBq, RAq : ?rawp + n <= A \/ A + 1440 <= ?rawp |- _ =>
                let RBx := fresh "RAWBx" in
                pose proof (presA_rw_cells asegs R LBq LF _ _ _ [(A, A + 1440)] m0 mx rawp [CB (Z.to_nat n) bs] (presW_presA asegs R HIA _ _ _ _ _ _ _ _ P2) (proj1 RBb)
                              ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia);
                                    eapply client_range_block; [apply in_or_app; left; exact RINq| clear; lia| clear; lia])
                              ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); cbn; split; [clear - RAq; lia| exact I])) as RBx end
            | idtac "rawb_now: failed" ]
    end.

  (* [comment removed for export] *)
  Ltac exitG TL rr TPX SM0 HKc MFc Hr RP :=
    dv_shapes; si_now; rawb_now;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with CE : rw_cells _ mx A [C4 ?rt; C4 ?p0; C8 (Z_to_bv 64 _); C8 (Z_to_bv 64 ?rawp); C4 ?ver; C4 ?vp; C4 ?dtg; C4 ?dpad; C8 (Z_to_bv 64 ?dlen); C8 (Z_to_bv 64 ?dq);
                                        CB 8 ?j56; CB 744 (zeros 744); CB 8 ?q2; CB 416 (zeros 416); CB 8 ?q3; CB 80 (RepCrt.sj0 ?sj); C8 _; C1 _; CB 7 _; CB 96 _; C8 _],
                      RB : rw_cells _ mx ?rawp' [CB _ bs] |- _ =>
        let REPx := fresh "REPx" in
        assert (REPx : pkcs7_at asegs PK (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                               P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj bs)) mx [(rawp, n)] LB A)
          by (apply (rep0_buildF mx rt p0 ver vp dtg dpad rawp dlen dq j56 q2 q3 sj); [unfold buf_cells, signer_cells; cbn [app]; exact CE| exact RB| exact RP]);
        let mo9 := fresh "mo9" in let HK9 := fresh "HK9" in let MF9 := fresh "MF9" in
        intros mo9 [HK9 MF9]; pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'; clear HKc MFc;
        lazymatch goal with HHx : HM _ _ _ ?hcx _ _ mx, HVx : havol _ _ _ _ <= havol _ _ _ _ + ?PHIx, HFRx : hfr _ _ _ _ <= hfr _ _ _ _ + ?FFRx |- _ =>
        let stx := constr:(Some (P7O n rawp crt_own_zero 0 [] 0 [],
                               P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj bs)) in
        (* [comment removed for export] *)
        first [ eapply TL with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := [(A, A + 1440)]) (PHIa := PHIx) (FFRa := FFRx) (Lc := [(rawp, n)]) (hc := hcx) (r := rr) (st := stx)
              | eapply TL with (W := [(A, A + 1440)]) (PHIa := PHIx) (FFRa := FFRx) (Lc := [(rawp, n)]) (hc := hcx) (r := rr) (st := stx) ];
          first [ exact (TPX _ _ REPx SM0) | exact (TPX _ _ REPx (SM0 _ _ _ _)) | exact (TPX _ _ REPx (SM0 _ _ _ _ _ _)) | eassumption
                | lazymatch goal with |- _ <= rr < _ => first [clear; lia | clear - Hr; lia | lia] | |- _ < rr <= _ => first [clear; lia | clear - Hr; lia | lia] end
                | lazymatch goal with |- HK _ _ _ _ _ => lazymatch goal with HKI : forall mo, HK _ _ _ _ mo <-> HK _ _ _ _ mo |- _ => apply (proj2 (HKI _)); assumption end end
                | (cbv beta; dvA_build) ]
        end
      end end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB"] Lemma tail_97560 : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 g18 g22 j32 alg : list byte) (cs : list cell)
      (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte)
      Lc mc moc hc (st : option (p7_own * p7_junk)) (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s5v s6v s7v : word),
    dvA FB sp1 W PHIa FFRa w0 w1 w2 g4 g8 g12 g16 g18 g22
        [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
         C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]
        (Z_to_bv 64 A) (Z_to_bv 64 FB) j32 v48 alg v80 cs Lc mc moc hc ->
    tailP W PHIa FFRa Lc mc st -> -2^31 <= r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v (Z_to_bv 64 (-8)) (Z_to_bv 64 r) s5v s6v s7v (Z_to_bv 64 FB) (Z_to_bv 64 A)
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97530) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s7v. intros D TP Hr. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
      first [exact D | exact HW | exact HWX | eassumption].
  Qed.

  (* [comment removed for export] *)
  Ltac bcmpI K QBY :=
    zstep;
    replace (Z_to_bv 64 360848) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite MCI; reflexivity);
    let ROS := fresh "ROS" in let ORO := fresh "ORO" in let SPB := fresh "SPB" in
    ro_str K 9%nat as ROS; img_aobj K 9 as ORO;
    pose proof (artA_bcmp asegs R HIA) as SPB;
    lazymatch type of QBY with bytes_at _ _ ?q ?qqs =>
    lazymatch goal with |- aevtA _ (KF _ _ _ ?hcx _) _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with SP1' : bv_unsigned sp - 208 <= ?sp1 <= _ |- _ =>
    lazymatch goal with HH : HM _ _ _ hcx ?LBq _ mx, SP1R' : 0 <= sp1 < 2 ^ 64 |- _ =>
    acallxA_sp sp1
      (eapply SPB with (h := hcx) (LB := LBq) (P := K) (Q := q) (n := 9) (qs := qqs); clear SPB;
         rewrite ?(unsigned_lit sp1) by exact SP1R';
         first [ exact ROS | exact QBY | exact ORO | eassumption | reflexivity
               | lazymatch goal with
                 | |- Z.of_nat (length _) = 9 => first [reflexivity | assumption]
                 | |- aobj _ _ _ _ q 9 => lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hcx) _ ?rw n |- _ => eapply aobj_sub; [exact OB| qlia| qlia] end
                 | |- lo <= sp1 - arl_need_bcmp R => lazymatch goal with SLO' : lo <= bv_unsigned sp - _, SP1' : bv_unsigned sp - 208 <= sp1 <= _, NRT' : arl_need_amem R <= arl_need_rt R /\ _ |- _ => clear - SLO' SP1' NS1 NB0 NRT' STKg0 STKs0 STKf0; lia end
                 | |- crange _ lo _ => lazymatch goal with SC : crange (hcs asegs R HIA hcx) lo (bv_unsigned sp - lo) |- _ => eapply crange_sub; [exact SC| clear; lia| qlia] end
                 | |- K + 9 <= lo \/ _ => left; pose proof (alloc_ceiling_val R); qlia
                 | |- q + 9 <= lo \/ _ => left; pose proof (alloc_ceiling_val R); qlia
                 | |- 9 = 0 \/ K + 9 + 8 <= _ => right; clear; lia
                 | |- 9 = 0 \/ q + 9 + 8 <= _ => right; pose proof (alloc_ceiling_val R); qlia
                 | |- 9 < _ => clear; lia
                 | |- sp1 <= htop _ _ _ _ => lazymatch goal with HTc' : htop _ _ _ hcx = htop _ _ _ h |- _ => rewrite HTc'; qlia end
                 end
               | match goal with |- ?g => idtac "BCMPI-PRE-LEFT:" g end ])
    end end end end;
    [ .. | idtac ];
    try clear ROS ORO; try clear SPB.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0540@C17025492443.287C17027589626.360C17027589628.324C17027589629.342C17027589631.306D27847976046.287D27850073160.342D27850073161.324D27850073162.306D27850073167.360D60109446735.287D60111543912.324D60111543913.342D60111543915.306D60111543918.360K21212095580.287K21214192760.306K21214192762.342K21214192763.324K21214192765.360K55088519473.287K55090616592.360K55090616597.306K55090616598.324K55090616599.342L10370335306.1  L10894997063.3  L13176305223.2  L14381936434.337L14789452616.0  L16467427964.276L17660516633.258L17660516633.277L17660516633.295L17660516633.313L17660516633.331L18926779052.283L19769535484.2  L20166242178.3  L20303431496.0  L21007906567.2  L21218866939.2  L22658091809.0  L22774446881.0  L2424960062.2   L26016216788.4  L27287188104.264L31852292097.2  L34783991938.3  L35666023782.15 L36147666602.319L36961436047.276L37663591692.9  L37940357415.0  L38235734261.1  L38738405142.1  L39033942809.2  L39195156935.5  L39348637477.0  L407869768.0    L41269999385.2  L41409160545.3  L41898327682.3  L43300649301.0  L44681963691.301L4559764272.301 L46745494493.3  L48487994137.2  L48648552217.2  L49858401057.0  L50790731766.15 L52941874306.3  L55085943702.3  L55842747208.3  L57124690773.0  L57625944369.319L57951117045.3  L58790154276.15 L60056205954.3  L60098763854.6  L61340351799.283L61905472681.337L62718247713.0  L63573689121.0  L63613367624.0  L63613504898.3  L64850595401.0  L67246375.0     L68272074258.8  L7049614941.2   L7552373529.2   L8284639507.264 L881835912.0    L8884097352.0   L9356559676.20  O13918901974.324O1476819784.342 O1476819785.324 O1476819786.306 O1476819791.360 O1478916974.287 O17025492443.287O17027589626.360O17027589628.324O17027589629.342O17027589631.306O27349780176.360O28722692754.287O28724789939.360O28724789940.342O28724789941.324O28724789942.306O37048910896.324O37048910897.342O37048910899.306O37048910902.360O37051008023.287O37526595730.287O37528692915.360O37528692916.342O37528692917.324O37528692918.306O47761277330.287O47763374515.360O47763374516.342O47763374517.324O47763374518.306O47806715794.287O47808812979.360O47808812980.342O47808812981.324O47808812982.306O50702732434.287O50704829619.360O50704829620.342O50704829621.324O50704829622.306O56414299794.287O56416396979.360O56416396980.342O56416396981.324O56416396982.306O59623432080.360O59623432085.306O59623432086.324O59623432087.342O59625529265.287O62439622385.287O65049786608.324O65049786609.342O65049786611.306O65049786614.360O65051883735.287O68658995925.306O7712025303.342 P10897630432.287P10899727553.360P10899727556.306P10899727558.342P10899727559.324P20179369217.306P20179369218.324P20179369219.342P20179369220.360P20181466405.287P21212095580.287P21214192760.306P21214192762.342P21214192763.324P21214192765.360P34787641857.306P34787641858.324P34787641859.342P34787641860.360P34789739045.287P39029203359.360P39206163137.360P39206163140.306P39206163142.342P39206163143.324P39208260320.287P41257985432.342P41419110342.287P41421207520.342P41421207521.324P41421207522.306P41421207527.360P41903025153.306P41903025154.324P41903025155.342P41903025156.360P41905122341.287P48502194622.287P48643779994.306P52938159617.306P52938159618.324P52938159619.342P52938159620.360P52940256805.287P60050384933.287P60052482049.306P60052482050.324P60052482051.342P60052482052.360P63606742821.287P63608839937.306P63608839938.324P63608839939.342P63608839940.360P7564476825.324 Q12683804246.287Q12685901424.342Q12685901425.324Q12685901426.306Q12685901431.360Q15605514303.264Q15616001563.283Q15616001564.301Q15616001565.319Q15616001566.337Q15665829027.267Q15665829027.286Q15665829027.304Q15665829027.322Q15665829027.340Q15766564435.287Q15768661618.360Q15768661620.324Q15768661621.342Q15768661623.306Q16532388922.340Q19979689448.266Q19979689448.285Q19979689448.303Q19979689448.321Q19979689448.339Q20069466170.304Q21925303825.282Q2501392942.264 Q2516073482.283 Q2516073484.319 Q2516073485.301 Q2516073487.337 Q27942454161.282Q30368130106.267Q3125606468.267 Q3125606468.286 Q3125606468.304 Q3125606468.322 Q3125606468.340 Q34964382778.287Q34966479899.360Q34966479900.342Q34966479901.324Q34966479902.306Q35287842828.282Q36856420847.287Q36858517960.324Q36858517961.342Q36858517963.306Q36858517966.360Q38248387216.287Q38250484401.360Q38250484404.306Q38250484406.342Q38250484407.324Q42439168719.287Q42441265896.324Q42441265897.342Q42441265899.306Q42441265902.360Q48358016496.342Q48358016497.324Q48358016498.306Q48358016503.360Q48360113622.287Q49576767034.286Q56389205783.287Q56391302960.324Q56391302961.342Q56391302963.306Q56391302966.360Q58304474964.266Q58304474964.285Q58304474964.303Q58304474964.321Q58304474964.339Q59865603600.287Q59867700785.360Q59867700788.306Q59867700790.342Q59867700791.324Q64681845184.342Q64681845185.324Q64681845186.306Q64681845191.360Q64683942374.287Q7522020748.282 Q7893133882.322 Q9080548402.266 Q9080548402.285 Q9080548402.303 Q9080548402.321 Q9080548402.339 Q9090756535.287 Q9092853648.324 Q9092853649.342 Q9092853651.306 Q9092853654.360 Q9356559660.267 Q9356559660.286 Q9356559660.304 Q9356559660.322 Q9356559660.340 Q9644583048.287 Q9646680233.360 Q9646680236.306 Q9646680238.342 Q9646680239.324 Q9928249826.266 Q9928249826.285 Q9928249826.303 Q9928249826.321 Q9928249826.339 00000100200300400502S05107O09m0<K0>40?]0AF0Bo0DX0DY0DZ0D[0D\0D]0FA0Ge0II0Jm0LQ0LW0LX0L`0NB0NC0Oe0QG0Ri0TK0Um0WO0Y10Y90Y:0Y;0YA0YB0YC0YD0YJ0YW0[90[?0[@0[e0]G0^i0_O0_P0_T0_W0_X0_Y0_Z0_[0_\0_]0_^0__0aA0bc0bn0bo0c00c10c_0c`0ca0cm0cn0eP0e]0fO0fP0fZ0h<0i^0i_0i`0ia0ib0ic0id0jH0jP0jQ0l30l40l50m30m40m50m60m70m80m90m:0m;0m<0m=0m>0m?0m@0mA0mB0mC0mD0mE0mF0mG0mH0mI0mJ0mK0mL0mM0mN0mO0mP0mQ0mR0mS0mT0mU0mV0mW0mX0mY0mZ0m[0m\0m]0m^0m_0m`0ma0mb0mc0md0me0mf0mg0mh0mi0mj0mk0ml0mm0mn0mo0oS11712[14?15c17H18m1:R1<71=\1=]1=^1=_1=`1=a1?F1@k1BP1D51EZ1GF1IP1KZ1Md1On1R81Sd1UI1Vn1XS1Z81[]1]B1^g1`L1b11cV1eB1fn1hS1j81k]1mB1ng20L22123V25;26`28E29j2;O2=42>Y2@E2Ae2CE2De2FE2Ge2I>2JW2L02MI2Nb2Pc2Rd2Te2Vf2Xg2Z]2\S2^I2`?2b52c[2e[2g[2i[2k[2m[2oA31B32[34435M36f38?3:@3;f3=H3>j3@L3An3CP3EQ3GR3IS3KT3MU3O93O:3O;3O<3O=3O>3PW3R03SI3Tb3V;3WZ3Y93ZX3\73]V3_:3`^3bB3cf3eJ3g03g13g23g33g43g53hO3ii3kC3l]3n73n83n93n:3n;3n<40;42:44946848749[4;A4<e4>I4?m4AQ4C54DY4F=4Ga4IE4Ji4LH4Mg4OF4Pe4RD4S`4U<4VX4X44YP4Zi4\B4][4_44`MFFFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFFFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS4rawpFS2lo3sp1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1n4rawpFSS1n2HnFSSS1n2HnS1A1n4rawp2RAS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1n2HnFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmSS2loS1AFFSSFFFSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2sp2lo3sp1FFSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSFFS4CNTj1n3CJ0SS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4CNTj1n4CNT1S1R3NS14STKg4STKs4STKf5STKg03NRT2sp2lo3SLO3sp13SP1FS1R2lo3LOSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSSSFSSS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2lo3sp1FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSSS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOFFFFFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFFFFFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPFFFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9". (* [comment removed for export] *)
  #[using="IMG NS1 PHIg FFRg CNTg STKg PHIs FFRs CNTs STKs STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIf_mono FFRf_mono STKg0 MCI NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS ALO1"] Lemma from_976d0 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 j32 alg : list byte)
      (rawp p1 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 g8 g12 g16 (le8 (Z_to_bv 64 p1)) (le8 (Z_to_bv 64 9)) FSHXL (Z_to_bv 64 A) (Z_to_bv 64 FB) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= p1 -> p1 + 9 <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) (Z_to_bv 64 p1) (Z_to_bv 64 n) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (A + 16)) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (rawp + n))
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x976c0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D RAWB RP RA RLP P9 BPHI BFFR BUD BUDF.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    lazymatch type of HHc with HM _ _ _ _ ?LB2x _ _ => set (LB2 := LB2x) in * end.
    pose proof (blocks_below_hm R HIA hc _ _ mc LB2 HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) LB2) by (subst LB2; left; reflexivity).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc rawp n HHc RIN) as OBUF.
    pose proof (presW_init_at R HIA hc _ _ LB2 LF mc (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    assert (WL2 : wlow R LB2 LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]).
    assert (WCA2 : wcover R LB2 LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    pose proof (CNTg_mono 0 n ltac:(clear - Hn; lia)) as CG0. pose proof (CNTs_mono 0 n ltac:(clear - Hn; lia)) as CS0'.
    ddestruct (A_pkcs7_parse_C24.joint_0 PHIj FFRj CNTj PHIj_mono FFRj_mono CNTj_mono n ltac:(clear - Hn; lia)) as (PJ0 & FJ0' & CJ0). pose proof (FJ0' (d + 1)) as FJ0. clear FJ0'.   (* [comment removed for export] *)
    pose proof (PHIg_mono 0 n ltac:(clear - Hn; lia)) as PG0. pose proof (FFRg_mono 0 n (d + 1) ltac:(clear - Hn; lia)) as FG0.
    pose proof (PHIs_mono 0 n ltac:(clear - Hn; lia)) as PS0. pose proof (FFRs_mono 0 n (d + 1) ltac:(clear - Hn; lia)) as FS0.
    assert (TPX : forall mq st, pkcs7_at asegs PK st mq [(rawp, n)] LB A -> p7small st -> tailP X0 PHIa FFRa [(rawp, n)] mq st).
    { intros mq st REPq SMq.
      assert (CNT1 : 1 <= CNTp n) by (unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia).
      pose proof (PHIf_mono 1 (CNTp n) ltac:(clear - CNT1; lia)) as PFm. pose proof (FFRf_mono 1 (CNTp n) 0 ltac:(clear - CNT1; lia)) as FFm.
      split; [exact REPq|]. split; [exact SMq|]. cbn [length]. change (Z.of_nat 1) with 1.
      split; [exact CNT1|].
      split; [unfold A_pkcs7_parse_C.PHIp; clear - BPHI PFm PJ0; lia|].
      split; [unfold A_pkcs7_parse_C.FFRp; clear - BFFR FFm FJ0; lia|].
      split; [intros xq Hx; exact (proj1 (proj1 (outside_app _ _ xq) Hx))|]. split; [intros xq Hx; exact Hx|]. exact (conj BUD BUDF). }
    assert (SM0' : forall ver' vp' tg' pd' dl' dq', p7small (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                                 P7J rt p0 (cells_bytes ([C4 ver'; C4 vp'] ++ buf_cells tg' pd' dl' dq' ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs))).
    { intros. cbn. clear - Hn. lia. }
    pose proof (hcs_img_cs R HIA hc IMG (proj2 (proj2 (proj2 IMG')))) as ICS. pose proof (hm_img_shadow asegs R HIA) as ISH.
    cb8_to_c8 G18 (@nil cell). rewrite le_bytes_to_word_le8 in G18.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    destruct (bytes_at_sliceF mc rawp bs p1 9 (cb_bytes_at _ _ _ _ RAWB) RLP ltac:(clear; lia) ltac:(rewrite LEN; exact P9)) as [QBY QLEN].
    pose proof (conj RAWB I) as RAWBbox. clear RAWB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24be0 QBY.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KB2; zify_cond KB2.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24c00 QBY.
    zstep. if_cases KB3; zify_cond KB3.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24c20 QBY.
    zstep. zstep.
    zstep. if_cases KB4; zify_cond KB4.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24c40 QBY.
    zstep. if_cases KB5; zify_cond KB5.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24c60 QBY.
    zstep. if_cases KB6; zify_cond KB6.
    { (* [comment removed for export] *)
      zstep. zstep. zstep. exitG (tail_97768 R HIA) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. exitG (tail_97768 R HIA) (-22272) TPX SM0' HKc MFc RP RP.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
