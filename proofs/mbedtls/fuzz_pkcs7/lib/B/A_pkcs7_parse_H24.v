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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24.
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
Local Ltac zchk_fails ::= constr:([622680]).
Local Ltac zchk_new ::= constr:([621140; 621144; 621148; 621152; 621156; 621848; 621852; 621856; 621860; 621864]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
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
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.55000007S1R3NA0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.11100000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L29784547046.124L40624322454.124L57778074916.124L6203244158.123 00000G00^01901WS2LF2sp1A1n2bs3LFB1B2H0S2LF2sp1A1n2bs3LFB1B2H0S2LF2sp1A1n2bs3LFB3AL01B2H0S2LF2sp1A1n2bs3LFB3shi1B2H22H0". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma aobj8_sshad : forall (AL0 : asan_layout) (CS : Z -> Prop) mX slo' shi B,
    cs_ok AL0 CS -> sshad asegs AL0 mX slo' shi -> slo' <= B -> B + 8 <= shi -> B mod 8 = 0 -> 0 <= B ->
    crange CS B 8 -> aobj asegs AL0 CS mX B 8.
  Proof.
    intros AL0 CS mX slo' shi B OK SS H1 H2 HB H0 HC.
    pose proof (sshad_chunk asegs AL0 mX slo' shi 0 B SS H1 ltac:(simpl; lia) HB) as SH.
    replace (shadow_of AL0 B) with (Z.shiftr B 3 + al_sb AL0) in SH
      by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    eapply (aobj_of_zero_shadow_sh asegs AL0 CS mX B (zcells 1) B 0 1 OK SH HC HB H0 ltac:(lia)).
    intros i Hi. apply cell_at_zcells. exact Hi.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "08[0@C18971418195.308C23920765559.329C23922862675.307C24099492777.330D11198522282.284D11891817072.308D15171508883.284D16071854214.308D16901939902.308D21186518650.330D24579994018.330D31612153258.284D420007634.284  D45725426958.308D50628777899.308D50818716548.284D55186708378.330D55315757195.330D56536395888.308D56538493012.330D57793146470.284D5982099855.330 D5984197035.308 D60111543915.330D63494002835.284D6359981838.308 D6362079018.330 K13144954490.306K13147051614.329K16789546457.328K17011449322.328K2223526121.330 K22861045682.308K26733837602.330K34789121258.329K42267898858.328K49774593146.306K52938578154.328K54978542206.284K63418475926.330K63420573106.308K63990506218.328K66535893218.330L10370335306.1  L10380392304.273L10912730231.1  L11668897786.272L11670997362.174L11993255542.174L11995301697.294L11995379966.272L12266043405.1  L12267397436.2  L12982798282.215L13141122540.2  L131411225File  L13340048728.1  L13350887686.215L13353005350.2  L1386317440.316 L14218488609.0  L14382060412.1  L14636542328.2  L15278480665.262L15756354262.7  L15822417165.1  L15824827452.2  L16467427964.273L16467427964.316L16467427964.317L16783093355.2  L1685717371.0   L16996603480.2  L17660516633.262L18023395959.1  L18302214263.1  L18315423448.2  L18438251618.1  L18865000865.0  L18994339888.1  L19404986422.13 L1952346182.174 L19769535484.2  L21007906567.2  L21350629479.5  L21360130279.0  L21386098076.195L21644325741.3  L21653067913.282L21654730866.2  L21866712442.1  L21868500043.2  L22148744886.15 L2225129129.3   L22490511066.8  L22533749879.3  L22557285548.195L22559330187.2  L22860483030.3  L22939159100.2  L22941438733.1  L23430585573.3  L24023900370.0  L24193368077.3  L2424960062.2   L24349731194.2  L24817214193.2  L25160623805.2  L25190023391.273L25204003039.273L25405964754.2  L25623839320.1  L25789285751.1  L26016216788.4  L2621559066.1   L26640306226.2  L26735572624.2  L27024764863.294L27026909761.194L27026909761.293L27280244015.1  L27817441514.279L27817441514.280L27831285827.195L27940405558.13 L28336158701.174L29066840183.1  L29345674871.1  L31471780431.10 L31852292097.2  L32190953767.0  L32327136116.1  L32479045794.3  L32982411378.9  L33158667902.2  L33312313103.2  L33389980555.2  L33817424237.3  L33982705724.2  L33985112333.1  L34786662232.2  L35455319922.2  L35666023782.15 L36181700215.1  L36460502135.1  L36586500648.2  L37094442973.4  L37564631729.5  L37663591692.9  L38110372910.4  L38235734261.1  L38258338282.2  L38259476970.1  L3851328310.13  L38738405142.1  L38756097312.194L40228640085.0  L40253556363.2  L40301035635.20 L40312932152.194L41096910396.2  L41099742989.1  L41663468825.273L41663468825.294L42139611770.2  L42273962072.2  L42411609006.0  L42968013442.19 L43300649301.0  L43810982283.2  L43820989346.1  L44061217931.2  L44117523139.215L46106660189.2  L46290454573.5  L47046946167.3  L47270873095.174L47271036295.3  L47506635779.194L47531296990.1  L47870616696.2  L49053909112.315L49053909112.316L49739481329.2  L49761849324.2  L49794625442.1  L50790731766.15 L50798508407.1  L50925318027.2  L51074967415.1  L51680632988.4  L51691687676.273L52126274563.2  L52940968792.2  L53517061083.293L53519217050.272L53527181501.2  L54963599545.2  L54965870984.2  L55105288843.2  L55324390328.1  L55714664252.2  L55716550157.1  L55842747208.3  L56847218714.1  L57048425585.3  L57124690773.0  L57951117045.3  L58304396918.6  L58662063499.2  L59308579414.10 L59308586248.2  L59427880762.295L60098763854.6  L6031628760.2   L60448817524.1  L61004000883.20 L61175798280.4  L61366595865.273L61366595865.294L61567447895.194L61567447895.293L61603606271.2  L62182785790.3  L62219489419.2  L63373084206.4  L63420085206.3  L64001157464.2  L64513097329.3  L64526681523.2  L64829056059.1  L64830457019.2  L64850595401.0  L64906482804.317L65526290571.2  L65772578680.194L66151427842.16 L66298372189.2  L66525635408.2  L66572605252.10 L66925259772.281L66925259772.305L67600005951.174L68272074258.8  L7122685215.10  L7356357495.1   L7735748552.2   L7738195705.2   L7739236126.1   L8171953640.279 L8171953640.280 L8435076219.3   L8454980662.21  L8742280115.2   L881835912.0    L9080220944.4   L9243719951.2   L9356559676.20  O11530619742.307O11930563540.306O12262625500.328O13184142275.330O13661656428.328O14667023342.328O1473384442.327 O1475481566.305 O1594840904.306 O18910436060.328O20344069996.329O21802621976.306O21804719164.329O23296604124.328O3076189820.327 O3078286936.305 O30872837119.328O31857991073.328O32537874520.305O33647379806.307O33649476986.328O33658030956.328O33990841394.308O33992938518.330O35273916753.328O35592798351.306O36611613660.329O39692739631.328O41205856170.330O44709834348.328O44938202843.306O45818878097.327O45969540168.306O47710246713.327O50647672426.330O51357618284.328O53232207033.328O55209884805.306O55516142064.328O55518239188.306O5637591166.328 O56616354268.328O6012847582.305 O6122206744.306 O61464066679.308O63904362034.308O64474006218.306O65331034963.330O65961212488.306O66386380993.329O67168963243.328O67171060367.306O68170348345.330O8258902344.306 O8604748773.306 P12278670331.284P14641216507.328P15835051771.284P21656429038.328P21658526154.306P21870859916.284P22535285303.330P22945712379.284P24353422329.329P24827162710.307P24829259890.328P25154843674.305P25410704209.327P32466942497.328P32557674715.285P32557674715.286P33162382589.328P33403074824.328P33810555850.306P33980871419.284P36581761195.330P40259310636.306P41095599355.284P42133856477.306P43817786156.306P44065883656.328P46118674398.328P46121612802.285P46121612802.286P47047506707.308P47876372191.306P49733734998.307P50927926572.306P52117610288.328P53346601986.285P53346601986.286P53529750042.305P53531847230.327P54978542206.284P55101564936.328P55703916027.284P57054148310.305P58657398536.328P61592333368.284P62187556989.327P62215864840.329P64517795058.327P64519892182.305P64538971685.306P64541068801.328P65519421996.306P66292560634.306P7750690063.284 P8754630693.306 Q10592318623.281Q11069306946.330Q1107808484.283 Q1109727972.284 Q11523583503.324Q11523583503.325Q1164691603.283 Q11891817072.308Q12244091759.284Q125584537.279  Q15163850165.284Q15173423251.283Q15605514303.269Q15605646235.277Q16603059094.284Q17305642754.323Q17305642754.324Q17977530286.330Q17979627402.308Q18089162767.280Q18089495345.280Q18615590367.283Q18708024625.280Q18871769597.280Q19400776373.330Q19561563123.282Q19561597574.281Q19561597574.305Q19582148966.308Q19790690407.308Q20374939093.280Q20375130875.323Q20375130875.324Q21138708080.308Q21186518650.330Q21767670690.308Q21827169904.308Q21829267028.330Q21832736479.308Q22324126766.281Q22522126128.323Q22522126128.324Q22712450012.284Q23163703743.308Q23611221436.330Q23613318552.308Q2501392942.269 Q25511591557.284Q25615717220.323Q25615717220.324Q25615918154.280Q26314584654.285Q26314584654.286Q26316671538.270Q27663034012.278Q27940667404.274Q27942454161.308Q2803826605.308 Q29743073578.269Q29775981542.308Q30062081901.330Q3044533173.284 Q30943613269.280Q32435106995.330Q32437204119.308Q32900564402.283Q33137450695.308Q33264869686.284Q33642333799.308Q34357517860.275Q34359956804.330Q34362053984.308Q34362328320.284Q34667424921.330Q34669522109.308Q36940982659.280Q37706020980.273Q38272766294.281Q38802716827.281Q39285966488.278Q3933900710.274 Q39682685338.276Q39682816575.269Q40599412494.280Q41412201211.330Q41414298335.308Q42439168719.308Q42439443119.284Q42441265899.330Q42441548847.285Q42441548847.286Q44298944140.270Q44301027056.285Q44301027056.286Q45834431503.280Q45834608433.280Q4734575583.283 Q48117823211.284Q48118064779.308Q48119910507.285Q48119910507.286Q48120161967.330Q48234175664.283Q48469054232.308Q49413559012.283Q49415575780.284Q49487219347.283Q49698585326.282Q49768332285.280Q50231601566.276Q5119959285.284 Q51367027125.284Q51604307871.277Q52624729581.324Q52624729581.325Q52747231024.284Q52965940120.308Q53799182759.308Q54384261766.330Q54481541664.275Q55315757195.330Q55330458123.324Q55330458123.325Q55330585385.323Q55330585385.324Q55410796738.330Q5596578838.285 Q5596578838.286 Q56536395888.308Q56538493012.330Q57225807357.280Q58163209363.283Q58667968752.280Q58694915926.281Q58743871165.308Q58744150173.279Q58972088541.282Q59085271138.283Q5922230887.308 Q59262428827.330Q59581139423.283Q59617566670.280Q59617750256.280Q59698596367.280Q59698919729.280Q59865321072.284Q59865603600.308Q59867425008.285Q59867425008.286Q59867700788.330Q60296756014.324Q60296756014.325Q60746685720.308Q60748782908.330Q62052672131.330Q62382039619.330Q62384136807.308Q62425983022.269Q62624230794.308Q62639688579.280Q63496213139.283Q64228675114.284Q64228675114.285Q64681563910.285Q64681563910.286Q64681845186.330Q64683667846.284Q64683942374.308Q64908775830.284Q65190342793.330Q6575060355.280 Q66486953072.308Q67140783850.269Q67742133194.280Q67837007747.280Q67893080934.273Q6912043747.282 Q7533086823.308 Q7535183939.330 Q8362820247.308 Q9212259811.330 Q9356756743.285 Q9356757127.307 Q9633850233.281 Q9633850233.305 Q9634015756.282 Q9644583048.308 Q9646680236.330 00000400800<00?00@01_03M05m08E09d0<D0<E0?40@S0@T0C;0ES0G20HQ0J00K`0Ka0Kb0MH0O80PW0R60T70V=0XC0ZI0]30_K0aQ0cW0e]0g^0id0kR0n>10V12\14b14h16G16H18g1:S1<?1?01AO1AS1AT1B>1B?1B@1BE1Bo1C71C81C91C<1C=1D\1Dj1Dn1Do1FN1Gm1IL1IM1IN1IO1Jn1K21K31K;1K>1K?1KB1Kf1M?1MG1MM1M]1M^1NH1NI1Oh1Oi1Om1On1P[1P\1Q91Q:1Qd1Ql1Qm1Qn1R21R>1R?1RJ1RP1RQ1RR1RS1T21UQ1UR1UW1U[1Uh1Um1V31V41Xa1Z[1]H1]L1_K1aJ1b01bT1bU1bY1b]1bn1c41c51c91c:1cN1cO1cV1cW1cX1cY1c]1c^1c_1dD1dH1dL1dM1dZ1di1eO1e_1ec1ek1el1fP1fS1h41h51h61i61j]1j^1jb1lA1m`1ma1mb1mc1nk1nl1nm1o01o11oW1oX1oj1ok20W20a21M21N21O23f26=26>26?26B27027427527927H28g28h28i2:H2;g2;h2;i2;j2;k2;n2;o2<32<?2<D2<E2<F2<S2<i2<j2=;2=A2=B2=L2=T2=X2>X2>e2@D2Ac2CW2F>2F?2F@2FA2FQ2FR2FS2FT2FU2FV2F^2F_2F`2Fa2Fb2GK2GL2GM2G^2I=2J\2L<2L`2M92M=2M>2M?2MB2MC2MD2MO2NT2NU2NV2Ne2Nl2Oj2Ok2Ol2Om2On2Oo2P02P12P22P32P42P52P62P72P82P92P:2P;2P_2P`2Pa2Pb2Pc2Pd2Pe2Pf2Pg2Ph2Pi2Pj2Pk2Pl2Pm2Pn2Po2Q02Q12Q22QV2QW2QX2QY2QZ2Q[2Q\2Q]2Q^2Q_2Q`2Qa2Qb2Qc2Qd2Qe2Qf2Qg2TQ2Vl2YQ2[32\U2_:2am2dR2fe2i@2k[2n630I31j33\35N37a3:<3;^3>H3@`3C;3E`3H83JS3Ln3NL3P<3Ql3TU3Vk3YF3[a3^13`H3b_3e:3gU3j<3lW3oA41W44246^4914;L4=b4@84BK4D^4G94HW4KC4MV4O;4O<4Pc4RJ4S_4U44V[4X14ZS4\84\94]^4_44`Y4`Z4ao4cD4cE4cF4cG4cH4dm4fC4gY4iW4k@4li4nR4nS4nT4ok51B52Y53o55D57T58j5:@5;V5=55>J5?_5AL5C_5E55FK5Ga5IQ5Jh5L?5MV5OA5Pl5RE5Sj5V:5X85YO5Ze5\C5]X5]Y5_05_15_25`X5b95dX5en5gY5gZ5g[5g\5i25jH5k^5mE5na60F61k63^65C66Y67o69E6:[6<76=k6?G6A;6Bo6DH6F36G^6I46I56J\6M86O@6Q`6T@6VH6VI6VJ6Wo6YT6[96\\6^26_W6ad6ae6cJ6eU6g`6iG6j]6j^6ln6o670K71`73574J75_77=77>77?78U79k7;A7<f7><7?X7@n7BS7D87E^7E_7H27H37H47H57H67H77H87H97H:7H;7H<7H=7H>7H?7H@7HA7IW7Jm7LC7LD7MZ7OA7Q`7T?7VS7Xg7Zc7]77_37_47`K7aa7c77dM7ed7g:7ha7jF7jG7jH7jI7kj7mF7nb80;81T82m84F85_S2FBS2FBS2FBS1AFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC2RA3RLP3PLN2p14Hp1a3x173x303x313x325POST0S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APRF2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC3RLP3PLN4APRF2p14Hp1a3x173x303x313x325POST0S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APRF2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x293SZC4APPA2p13x173x303x313x325POST0S4rawpS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3LN03PLN3ACV3SPR2F04SP1R3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2LN2RP3RLP3LN03PLN3ACV3SPR2F04SP1R3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2LN2RP3RLP3LN03PLN3ACV3SPR2F04SP1R3RCES1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p12Lw3Hp12LR4Hp1a3HLwS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3LN03PLN3ACV3SPR2F04SP1R3RCES2FBFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r23Hr2FFS3sp1S1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r23Hr2S2r23Hr2FSS1AFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R2lo3LOS3ALOS2FBFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFSFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBFS2sp3sp1S1ASS1AS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2RP3RLP3SPR2F04SP1RS1n4rawpS1n2HnS1P2LN2p12p23Hp2SS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r13Hr1FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS2FBFS1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1FS4rawp1P2LN3RLP2p13Hp12p23Hp2FS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r13Hr1S2r13Hr1FFS2FBS2sp3sp13SP1SS1A2lo4ALO1S1n2HnFFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS3sp1S2FBS1A1n4rawp2RAS3sp1S1A2A0FS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2LN2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FS2FBS2FBS2r23Hr21r2KR1q1HS1n2HnSS2FBFS1R2lo3LOS2FB3ALO2F1FS2FB2F0FFFS2FBFFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS2FBS2FBFS1P2LN2p13Hp1S1P2LN2p12Lw2KES4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmS1n2FB4rawp4APRFS2loS2r23Hr2FS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1AS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2RP3RLP3SPR2F04SP1R2p14Hp1aSFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2RP3RLP3SPR2F04SP1R2p12Lw2LR4Hp1aFS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFSS1R3NS14STKg4STKs4STKf5STKg02sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALO3ACPSFS1AFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r2FS1R1n4rawp3ACV3RCEFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp11P2LN3LN0S1P2LN3LN0S1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12p12Lw2LRFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RFFS1AS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS2FBFS2FBS2sp2lo3sp13SP1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFFS1AFS2FBS4CNTj1n3CJ0S3sp1FSS4CNTj1n4CNT1S4rawp1P2LN3RLP2p13Hp1FS2r23Hr21r2KZ1q1HS1i2HiFS1R2lo3LOSS2sp3sp1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S1A1n4rawp2RAS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2LN2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p13Hp14Hp1aS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3PLN3ACV3SPR2F04SP1R3RCE2p13Hp14Hp1aFFFS1n2FB4rawp4APRFFFFFFS2r13Hr1SFFFS2FB2r03F641q1r1H2H02q02H43sp14SP1M1A3AALFFS2r13Hr11r2KT1q1HS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2LN2RP3RLP3LN03SPR2F04SP1RS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS1R1n2lo3LOS4rawp3ALO3RCES2FBFFS1AFFS1A2FB4APPAS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCEFSS2sp2lo3sp13SP1S2FB2F0S1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3RLP3PLN3ALO3RCE2p12Lw2LR4Hp1a3EQ1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APRF2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APRF2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1P2LN2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3RLP3LN03PLN3ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F12HB5Ha_st5Hl_st3sp13SP1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0FFS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2HBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st3sp1S1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st3sp1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F04SP1R2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F04SP1R2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp1P2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_st3sp1S1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTFS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI CINFO ALGNULL MDALG GETINT NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_974b0 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 j32 alg : list byte)
      (rawp P LN : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s5v s8v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 g8 g12 g16 (le8 (Z_to_bv 64 P)) (le8 (Z_to_bv 64 LN)) FSHXL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P -> 0 <= LN -> P + LN <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) s4v s5v (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (FB + 176)) s8v s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97a38) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA RLP LN0 PLN BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    lazymatch type of HHc with HM _ _ _ _ ?LB2x _ _ => set (LB2 := LB2x) in * end.
    assert (CWAc : client_wrange L (LB2 ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { subst LB2. rewrite HTc. eapply client_wrange_mono; [exact CWA|]. intros b Hb. apply fdata_cons_sub. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    pose proof (blocks_below_hm R HIA hc _ _ mc LB2 HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) LB2) by (subst LB2; left; reflexivity).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ BA].
    pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA RIN ltac:(left; reflexivity)) as APRF. cbn [fst snd] in APRF. clear BA.
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc rawp n HHc RIN) as OBUF.
    pose proof (presW_init_at R HIA hc _ _ LB2 LF mc (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    assert (WL2 : wlow R LB2 LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]).
    assert (WCA2 : wcover R LB2 LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    cb8_to_c8 G18 (@nil cell). rewrite le_bytes_to_word_le8 in G18.
    cb8_to_c8 G22 (@nil cell). rewrite le_bytes_to_word_le8 in G22.
    cb8_to_c8 G8 (@nil cell). cb8_to_c8 G12 (@nil cell).
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    pose proof (conj RAWB I) as RAWBbox. clear RAWB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 64) 1%nat as OPP. frame_aobj FSH (FB + 96) 1%nat as OL2.
    rawb_now.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    lazymatch goal with G12x : rw_cells _ _ (FB + 96) [C8 ?lw] |- _ =>
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := FB + 64) (LENP := FB + 96) (P := P) (END := P + LN) (BUF := rawp) (bs := bs) (tag := 48) (lo := lo) (lenv := lw);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact OL2 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact RLP | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 64) _ => eassumption
                 | |- rw_cells _ _ (FB + 96) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp [CB _ bs] |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- P <= P + LN => clear - LN0; lia
                 | |- P + LN <= rawp + _ => rewrite LEN; exact PLN
                 | |- rawp + _ < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                 | |- FB + 64 + 8 <= FB + 96 \/ _ => left; clear; lia
                 | |- _ = 0 \/ FB + 64 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- _ = 0 \/ FB + 96 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- (FB + 96) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 64 => clear - F0; lia
                 | |- 0 < FB + 96 => clear - F0; lia
                 | |- 0 < rawp => exact RP
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- FB + 64 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- FB + 96 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- _ = 0 \/ rawp + _ <= sp1 - 16 \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- _ = Z_to_bv 64 (P + LN) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A1P-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "GT3-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT3-LEFT:" g end.
    clear GT' ABc OPP OL2.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : P <= ?pp <= P + LN |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ _ (FB + 96) [C8 ?lw] |- _ => rename lw into Lw end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    2:{ (* [comment removed for export] *)
        zstep. zstep. zstep.
        match goal with |- context [bv_swrap 32 (Z.land r1 ?M + ?c)] => assert (EQX : (Z_to_bv 64 (bv_swrap 32 (Z.land r1 M + c)) : word) = Z_to_bv 64 (r1 + -21248)) by (apply addw_err; [vm_compute; reflexivity| vm_compute; reflexivity| clear - Hr1; lia| clear - Hr1; lia]) end.
        rewrite EQX. clear EQX.
        zstep. exitG (tail_97504 R HIA) (r1 + -21248) TPX SM0' HKc MFc Hr1 RP. }
    assert (R10 : r1 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw]. clear HOK1 KT Hr1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
        zstep. zstep. exitG (tail_977a0 R HIA) (-21350) TPX SM0' HKc MFc RP RP. }
    assert (EQ1 : p1 + bv_unsigned Lw = P + LN).
    { change 18446744073709551615 with (Z.ones 64) in KE. rewrite ?Z.land_ones in KE by (clear; lia).
      rewrite ?Z.mod_small in KE by (clear - Hp1 HLw LN0 PLN RLP RP RCE ACV LR; lia). first [exact KE | clear - KE; lia | clear - KE Hp1 HLw LN0 PLN RLP RP RCE ACV LR; Z.div_mod_to_equations; lia]. }
    clear KE.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    splitat CELLS 4%nat CV. splitat CV 1%nat CR.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 64) 1%nat as OPP.
    try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
    lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) _ A 1440 |- _ => rename OB into OBJx | _ => idtac "no OBJx" end.
    pose proof GETINT as GI'. unfold asn1_get_int_stmtA, A_ASN1_GET_INT_G in GI'.
    acallxA_sp sp1
      (eapply GI' with (CS := hcs asegs R HIA hc) (PP := FB + 64) (VALP := A + 24) (P := p1) (END := P + LN) (BUF := rawp) (bs := bs) (lo := lo) (valv := ver);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact CV | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 64) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp [CB _ bs] |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                 | |- aobj _ _ _ _ (A + 24) 4 => eapply aobj_sub; [exact OBJx| clear; lia| clear; lia]
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- rawp <= p1 => clear - Hp1 RLP; lia
                 | |- p1 <= P + LN => clear - Hp1; lia
                 | |- P + LN <= rawp + _ => rewrite LEN; exact PLN
                 | |- rawp + _ < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                 | |- FB + 64 + 8 <= A + 24 \/ _ => clear - APPA; lia
                 | |- _ = 0 \/ FB + 64 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- _ = 0 \/ A + 24 + 4 <= rawp \/ _ => right; rewrite LEN; clear - RA; lia
                 | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- (A + 24) mod 4 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 64 => clear - F0; lia
                 | |- 0 < A + 24 => clear - A0; lia
                 | |- 0 < rawp => exact RP
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- lo <= sp1 - 64 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- aobj _ _ _ ?mx (sp1 - 48) 8 =>
                     lazymatch goal with SSx : sshad _ _ mx ?slo' ?shi |- _ =>
                       apply (aobj8_sshad _ _ mx slo' shi (sp1 - 48) CSOKc SSx);
                       [ first [clear - SP1 SLO SLOL NS1 STKg0 STKs0 STKf0; lia | lia] | first [clear - SP1; lia | lia]
                       | clear - SP1M; Z.div_mod_to_equations; lia | first [clear - SP1 SLO LOS ALO ACP NS1 STKg0 STKs0 STKf0; lia | lia]
                       | eapply crange_sub; [exact SCSc| clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia| clear - SP1; lia] ] end
                 | |- alloc_ceiling <= lo => clear - ALO LOS; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- FB + 64 + 8 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                 | |- A + 24 + 4 <= lo \/ _ => left; clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                 | |- _ = 0 \/ rawp + _ <= lo \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS; lia
                 | |- _ = Z_to_bv 64 (P + LN) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A1Q-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "GI-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GI-LEFT:" g end.
    clear GI' ABc OPP.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r2 end.
    match goal with H : _ < r2 <= 0 |- _ => rename H into Hr2 end.
    match goal with H : p1 <= ?pp <= P + LN |- _ => rename H into Hp2; rename pp into p2 end.
    (* [comment removed for export] *)
    lazymatch goal with CVx : rw_cells _ ?mx (A + 24) [C4 _], CRx : rw_cells _ ?mx (A + 28) _, CPx : rw_cells _ ?mx A _ |- _ => joinr CPx CVx; joinr CPx CRx end.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    zstep. if_cases KR; zify_cond KR.
    - assert (R20 : r2 = 0) by (change 18446744073709551615 with (Z.ones 64) in KR; rewrite ?Z.land_ones in KR by (clear; lia); clear - KR Hr2; Z.div_mod_to_equations; lia).
      subst r2. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      clear ABc.
      (* [comment removed for export] *)
      zstep. if_cases KV; zify_cond KV.
      2:{ (* [comment removed for export] *)
          zstep. zstep. zstep.
          zstep. (* [comment removed for export] *)
          replace (Z_to_bv 64 18446744073709530112 : word) with (Z_to_bv 64 (-21504) : word) by (apply bv_eq; reflexivity).
          exitG (tail_97504 R HIA) (-21504) TPX SM0' HKc MFc Hr2 RP. }
      (* [comment removed for export] *)
      zstep. zstep. try (if_cases KZ; zify_cond KZ; [ exfalso; clear - KZ; cbn in KZ; lia |]).
      (* [comment removed for export] *)
      dv_shapes. si_now. try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      subst LB2.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
      eapply (from_97828 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (P := p2) (END2 := P + LN)
                                     (rt := rt) (p0 := p0) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
        first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW | exact PLN
              | lazymatch goal with
                | |- rawp <= p2 => clear - Hp2 Hp1 RLP; lia
                | |- p2 <= P + LN => clear - Hp2; lia
                | |- 0 < rawp => exact RP
                | |- rw_cells _ _ rawp _ => eassumption
                | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                    cbv delta [A_pkcs7_parse_C24.dvA] beta;
                    split; [eassumption|]; split; [exact HK9|]; split; [exact MF9'|];
                    split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [eassumption|]; split; [eassumption|];
                    split; [eassumption|]; split; [eassumption|];
                    repeat match goal with |- _ /\ _ => split end;
                    first [ eassumption | reflexivity
                          | lazymatch goal with |- rw_cells _ mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA530-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "F97530-LEFT:" g end ]
      end.
    - zstep. zstep. zstep.
      match goal with |- context [bv_swrap 32 (Z.land r2 ?M + ?c)] => assert (EQX : (Z_to_bv 64 (bv_swrap 32 (Z.land r2 M + c)) : word) = Z_to_bv 64 (r2 + -21504)) by (apply addw_err; [vm_compute; reflexivity| vm_compute; reflexivity| clear - Hr2; lia| clear - Hr2; lia]) end.
      rewrite EQX. clear EQX.
      zstep. lazymatch goal with |- _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv_concl_iota | symmetry; zchk_solve] end.
      zstep. zstep. zstep. zstep. zstep. zstep.
      clear ABc.
      zstep. if_cases KV; zify_cond KV.
      2:{ zstep. zstep. zstep. zstep.
          replace (Z_to_bv 64 18446744073709530112 : word) with (Z_to_bv 64 (-21504) : word) by (apply bv_eq; reflexivity).
          exitG (tail_97504 R HIA) (-21504) TPX SM0' HKc MFc Hr2 RP. }
      zstep. zstep. if_cases KZ; zify_cond KZ.
      2:{ exfalso. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite ?Z.land_ones in KZ by (clear; lia). clear - KZ Hr2. Z.div_mod_to_equations. lia. }
      exitG (tail_97504 R HIA) (r2 + -21504) TPX SM0' HKc MFc Hr2 RP.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
