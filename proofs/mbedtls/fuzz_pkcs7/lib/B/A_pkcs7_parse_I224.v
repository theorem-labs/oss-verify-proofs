(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int
     A_asn1_get_alg_null_A A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_asn1_get_int_loops.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_top24 A_pkcs7_getcerts_stmt24 A_pkcs7_parse_A A_pkcs7_parse_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24 A_pkcs7_parse_H24.
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
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG_G 64.
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
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s5v s6v s9v : word),
    dvA FB sp1 W PHIa FFRa w0 w1 w2 g4 g8 g12 g16 g18 g22
        [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
         C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]
        (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80 cs Lc mc moc hc ->
    tailP W PHIa FFRa Lc mc st -> -2^31 <= r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v (Z_to_bv 64 (-8)) (Z_to_bv 64 r) s5v s6v (Z_to_bv 64 FB) (Z_to_bv 64 A) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97ae0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D TP Hr. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    eapply (out_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (st := st) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc);
      first [exact D | exact HW | exact HWX | eassumption].
  Qed.

  (* [comment removed for export] *)
  Ltac bcmpI K QBY :=
    zstep;
    replace (Z_to_bv 64 362244) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite MCI; reflexivity);
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0540@C17025492443.292C17027589626.365C17027589628.329C17027589629.347C17027589631.311D27847976046.292D27850073160.347D27850073161.329D27850073162.311D27850073167.365D60109446735.292D60111543912.329D60111543913.347D60111543915.311D60111543918.365K21212095580.292K21214192760.311K21214192762.347K21214192763.329K21214192765.365K55088519473.292K55090616592.365K55090616597.311K55090616598.329K55090616599.347L10370335306.1  L10408980650.324L10894997063.3  L10945135920.306L1108809491.269 L12808385313.0  L13176305223.2  L16467427964.281L17660516633.263L17660516633.282L17660516633.300L17660516633.318L17660516633.336L1874667177.342 L19769535484.2  L20166242178.3  L21007906567.2  L21218866939.2  L22191044377.2  L22463785288.0  L22867772209.324L2424960062.2   L26016216788.4  L26598956855.288L27977764168.0  L3142354713.2   L31852292097.2  L32565125921.0  L32879090465.0  L34783991938.3  L35666023782.15 L36308969608.269L36961436047.281L37663591692.9  L37940357415.0  L38235734261.1  L38738405142.1  L39195156935.5  L39348637477.0  L41409160545.3  L41898327682.3  L42157884193.0  L42359347016.0  L43300649301.0  L46745494493.3  L47873325896.0  L50790731766.15 L52941874306.3  L53371159211.306L53387304776.0  L53559464729.2  L55085943702.3  L55842747208.3  L56126960409.2  L57124690773.0  L57951117045.3  L58790154276.15 L60056205954.3  L60098763854.6  L62074789036.288L62228589345.0  L6341746457.2   L63613504898.3  L64850595401.0  L67246375.0     L68272074258.8  L7049614941.2   L7216064818.342 L881835912.0    L9356559676.20  O1476819784.347 O1476819785.329 O1476819786.311 O1476819791.365 O1478916974.292 O17025492443.292O17027589626.365O17027589628.329O17027589629.347O17027589631.311O24219481815.347O28722692754.292O28724789939.365O28724789940.347O28724789941.329O28724789942.311O33812767446.329O37048910896.329O37048910897.347O37048910899.311O37048910902.365O37051008023.292O37526595730.292O37528692915.365O37528692916.347O37528692917.329O37528692918.311O47761277330.292O47763374515.365O47763374516.347O47763374517.329O47763374518.311O47806715794.292O47808812979.365O47808812980.347O47808812981.329O47808812982.311O50702732434.292O50704829619.365O50704829620.347O50704829621.329O50704829622.311O50713881329.292O50963634896.365O56414299794.292O56416396979.365O56416396980.347O56416396981.329O56416396982.311O59623432080.365O59623432085.311O59623432086.329O59623432087.347O59625529265.292O619292373.311  O65049786608.329O65049786609.347O65049786611.311O65049786614.365O65051883735.292P10897630432.292P10899727553.365P10899727556.311P10899727558.347P10899727559.329P20179369217.311P20179369218.329P20179369219.347P20179369220.365P20181466405.292P21212095580.292P21214192760.311P21214192762.347P21214192763.329P21214192765.365P22185289150.292P3146012063.365 P34787641857.311P34787641858.329P34787641859.347P34787641860.365P34789739045.292P39206163137.365P39206163140.311P39206163142.347P39206163143.329P39208260320.292P41419110342.292P41421207520.347P41421207521.329P41421207522.311P41421207527.365P41903025153.311P41903025154.329P41903025155.347P41903025156.365P41905122341.292P52938159617.311P52938159618.329P52938159619.347P52938159620.365P52940256805.292P53564162456.347P56130642330.311P60050384933.292P60052482049.311P60052482050.329P60052482051.347P60052482052.365P6328651161.329 P63606742821.292P63608839937.311P63608839938.329P63608839939.347P63608839940.365Q12683804246.292Q12685901424.347Q12685901425.329Q12685901426.311Q12685901431.365Q15605514303.269Q15616001563.288Q15616001564.306Q15616001565.324Q15616001566.342Q15665829027.272Q15665829027.291Q15665829027.309Q15665829027.327Q15665829027.345Q15766564435.292Q15768661618.365Q15768661620.329Q15768661621.347Q15768661623.311Q19979689448.271Q19979689448.290Q19979689448.308Q19979689448.326Q19979689448.344Q21925303825.287Q2501392942.269 Q2516073482.288 Q2516073484.324 Q2516073485.306 Q2516073487.342 Q27942454161.287Q3125606468.272 Q3125606468.291 Q3125606468.309 Q3125606468.327 Q3125606468.345 Q34964382778.292Q34966479899.365Q34966479900.347Q34966479901.329Q34966479902.311Q35287842828.287Q36464506426.309Q36856420847.292Q36858517960.329Q36858517961.347Q36858517963.311Q36858517966.365Q38248387216.292Q38250484401.365Q38250484404.311Q38250484406.347Q38250484407.329Q42439168719.292Q42441265896.329Q42441265897.347Q42441265899.311Q42441265902.365Q43945592890.327Q48358016496.347Q48358016497.329Q48358016498.311Q48358016503.365Q48360113622.292Q48640838714.291Q52577374778.345Q56389205783.292Q56391302960.329Q56391302961.347Q56391302963.311Q56391302966.365Q58304474964.271Q58304474964.290Q58304474964.308Q58304474964.326Q58304474964.344Q59865603600.292Q59867700785.365Q59867700788.311Q59867700790.347Q59867700791.329Q64681845184.347Q64681845185.329Q64681845186.311Q64681845191.365Q64683942374.292Q7522020748.287 Q8278899258.272 Q9080548402.271 Q9080548402.290 Q9080548402.308 Q9080548402.326 Q9080548402.344 Q9090756535.292 Q9092853648.329 Q9092853649.347 Q9092853651.311 Q9092853654.365 Q9356559660.272 Q9356559660.291 Q9356559660.309 Q9356559660.327 Q9356559660.345 Q9644583048.292 Q9646680233.365 Q9646680236.311 Q9646680238.347 Q9646680239.329 Q9928249826.271 Q9928249826.290 Q9928249826.308 Q9928249826.326 Q9928249826.344 00000100200300400502S05107O09m0<K0>40?]0AF0Bo0DX0DY0DZ0D[0D\0D]0FA0Ge0II0Jm0LQ0LW0N90N:0O\0Q>0Q?0QG0Ri0TK0Um0WO0Y10ZS0\50\=0\>0\D0\E0\F0\G0]i0]o0^<0_^0__0_`0_f0_g0_h0_i0`N0b00cR0d80d90d=0d@0dA0dB0dC0dD0dE0dF0dG0dR0dS0eA0eB0fd0fe0ff0fg0g30g40g50gB0h40h50h?0ia0ib0ic0id0ie0if0jJ0jR0l40l50m30m40m50m60m70m80m90m:0m;0m<0m=0m>0m?0m@0mA0mB0mC0mD0mE0mF0mG0mH0mI0mJ0mK0mL0mM0mN0mO0mP0mQ0mR0mS0mT0mU0mV0mW0mX0mY0mZ0m[0m\0m]0m^0m_0m`0ma0mb0mc0md0me0mf0mg0mh0mi0mj0mk0ml0mm0mn0mo0oS11712[14?15c17H18m1:R1<71=\1=]1=^1=_1=`1=a1?M1A91B^1DC1Eh1GM1I21K<1MF1OP1QZ1Sd1UI1Vn1XS1Z81[]1]B1^g1`L1b11cV1e;1f`1hE1ij1kO1m;1ng20L22123V25;26`28L2:12;V2=;2>`2@E2Ae2CE2De2FE2Ge2I>2JW2L02MI2Nb2Pc2Rd2Te2Vf2Xg2Z]2\S2^I2`?2b52d52f52h52j52l52n62oO30h32A33Z35337438V3:83;Z3=<3>^3@_3B`3Da3Fb3Hc3JG3Km3Kn3Ko3L03L13L23MK3Nd3P=3QV3Ro3TN3Um3WL3Xk3ZJ3\03]T3_83`\3b@3cd3eJ3g03g13g23g33g43g53hO3ii3kC3l]3n73n83n93n:3n;3n<40;42:44946848749[4;A4<e4>I4?m4AQ4C54DY4F=4Ga4IE4Ji4LH4Mg4OF4Pe4RD4S`4U<4VX4X44YP4Zi4\B4][4_44`MFFFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFFFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS4rawpS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSS2lo3sp1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1n4rawpFS1n2HnFFSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1n2HnS1A1n4rawp2RAS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSFS1n2HnSSFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmSS2loS1AFSFFSSSS2sp2lo3sp1SS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSFFS4CNTj1n3CJ0FSS4CNTj1n4CNT1S1R3NS14STKg4STKs4STKf5STKg03NRT2sp2lo3SLO3sp13SP1FS1R2lo3LOSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSFFSSS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2lo3sp1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOFFFFFS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCE4QLENS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P93RCE1HS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HFFFFFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPS1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLPFFFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO1HS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9S1R4STKg4STKs4STKf2LF1n2bs3LFB4rawp2p12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2P9". (* [comment removed for export] *)
  #[using="IMG NS1 PHIg FFRg CNTg STKg PHIs FFRs CNTs STKs STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIf_mono FFRf_mono STKg0 MCI NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS ALO1"] Lemma from_976d0 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 j32 alg : list byte)
      (rawp p1 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s7v s8v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 g8 g12 g16 (le8 (Z_to_bv 64 p1)) (le8 (Z_to_bv 64 9)) FSHXL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= p1 -> p1 + 9 <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) s4v s5v (Z_to_bv 64 (FB + 144)) s7v s8v s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97c70) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA RLP P9 BPHI BFFR BUD BUDF.
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
    bcmpI 0x24d40 QBY.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KB2; zify_cond KB2.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24d60 QBY.
    zstep. if_cases KB3; zify_cond KB3.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24d80 QBY.
    zstep. zstep.
    zstep. if_cases KB4; zify_cond KB4.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24da0 QBY.
    zstep. if_cases KB5; zify_cond KB5.
    { exitG (tail_97560) (-21376) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24dc0 QBY.
    zstep. if_cases KB6; zify_cond KB6.
    { (* [comment removed for export] *)
      zstep. zstep. exitG (tail_97768 R HIA) (-22272) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. exitG (tail_97768 R HIA) (-21376) TPX SM0' HKc MFc RP RP.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
