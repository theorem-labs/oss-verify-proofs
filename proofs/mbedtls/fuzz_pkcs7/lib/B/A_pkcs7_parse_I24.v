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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24 A_pkcs7_parse_H24 A_pkcs7_parse_I224.
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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x98058]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.


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
  Local Ltac2 Set LiaOrc.tbl := fun () => "07d0@C1123566675.298 C1123566675.339 C17027589631.318C65802607699.297C65802607699.340D13927008426.300D16071854214.298D16901939902.298D16908881264.298D16908881264.340D19389307406.298D19389307406.340D19921221523.300D24582091142.340D27850073162.318D31548437675.298D31548437675.340D55184611262.340D55641685675.298D55641685675.340D57793146470.300D57793146470.317D60111543915.318D60128441358.298D60128441358.340D61549796208.298D61549796208.340D62232727210.300D62232727210.317D68243715475.300D68243715475.317K15777363634.298K15777363634.340K21214192760.318K48892179322.298K48892179322.338K54978542206.300K54978542206.317K55090616597.318K59095072946.298K59095072946.340K61291792132.300K61291792132.317K66449870202.298K66449870202.338L10127692146.230L10370335306.1  L10472357176.327L10762500794.4  L10894997063.3  L11838558071.1  L12266043405.1  L13176305223.2  L13340048728.1  L13554332448.6  L13587842953.272L13587842953.315L13829605693.4  L13917980321.0  L14636542328.2  L15226064563.2  L15278480665.262L15278480665.285L15278480665.289L15278480665.326L15756354262.7  L15777915094.3  L15822417165.1  L16467427964.288L16467427964.328L16762513803.295L1685717371.0   L16949806408.0  L17660516633.262L17660516633.286L17660516633.289L17660516633.306L17660516633.326L17762320911.2  L18315423448.2  L19228683634.9  L19404986422.13 L19769535484.2  L20166242178.3  L20410610330.4  L20956242213.2  L20958429861.1  L21007906567.2  L21218866939.2  L21360130279.0  L2149169966.4   L21586276920.261L21654730866.2  L21866712442.1  L22533749879.3  L22899008887.1  L22941438733.1  L2424960062.2   L24349731194.2  L25623839320.1  L25646285820.210L26016216788.4  L2621559066.1   L27230186771.5  L27270131831.1  L27940405558.13 L28624903391.289L28624903391.306L28916609826.262L29409929468.271L29409929468.314L29676255814.8  L30013901687.1  L30052271987.20 L30559254009.2  L31852292097.2  L32110924979.2  L32750658443.2  L33198169196.210L33202607681.326L33215189712.261L33437929969.2  L33570290807.1  L33985112333.1  L34166416106.230L34767689079.1  L34783991938.3  L3522534509.3   L35455319922.2  L35666023782.15 L36382048241.2  L36600485609.2  L36946886283.2  L36961436047.288L36961436047.328L37529397812.262L37663591692.9  L38034703759.230L38176978730.8  L38235734261.1  L38239941093.230L38239941093.325L38242088023.326L38246380909.6  L38738405142.1  L39195156935.5  L39348637477.0  L40062184381.2  L40228640085.0  L40746874225.3  L41099742989.1  L41409160545.3  L41837021199.2  L41869966199.1  L41898327682.3  L42139611770.2  L43298250349.3  L43300649301.0  L43690857329.3  L43810982283.2  L44061217931.2  L44165741571.230L44165741571.325L44434993010.9  L44855900688.295L45174768033.0  L45591255342.4  L46106660189.2  L46290454573.5  L46745494493.3  L47046946167.3  L4725827959.1   L47832818059.2  L47833956619.1  L47870616696.2  L48904993004.2  L48984809847.1  L50790731766.15 L50863131871.289L50925318027.2  L52541166199.1  L52941874306.3  L53517061015.325L53597055279.1  L54009320217.2  L54048688929.0  L54692181363.20 L54864364148.1  L54906310077.2  L54965870984.2  L55085943702.3  L55105288843.2  L55291398970.230L55296569868.4  L55716550157.1  L55842747208.3  L56847218714.1  L57124690773.0  L57951117045.3  L58039649675.2  L58304396918.6  L58790154276.15 L59095635670.3  L59308586248.2  L59427880633.287L59427880762.286L60045244279.1  L60056205954.3  L60098763854.6  L6031628760.2   L61292069120.3  L61567431709.210L61603606271.2  L62219489419.2  L62586290822.10 L63613504898.3  L64703788861.4  L64850595401.0  L66151427842.16 L66298372189.2  L66445969132.2  L66572605252.10 L67246375.0     L68272074258.8  L7049614941.2   L7122685215.10  L7738195705.2   L8060063860.1   L8454980662.21  L881835912.0    L9080220944.4   L9356559676.20  L9930401096.6   L9930401096.8   O10567734856.296O12408905496.298O12408905496.338O13663753544.338O14082152005.340O14664926154.338O1476819786.318 O15174400344.295O15174400344.337O16866295602.298O16866295602.340O17027589631.318O17217116232.296O17846813406.295O17846813406.337O20346167112.338O26475597711.298O26475597711.338O27010744648.338O28042800350.295O28042800350.337O28724789942.318O30870739931.338O31855893893.338O33655933768.338O33870522200.295O33870522200.337O35198608664.298O35198608664.338O37048910899.318O37528692918.318O4011621941.318 O42395367124.296O42395367124.338O44938202843.296O45969540168.296O4702012722.298 O4702012722.340 O47383255252.296O47383255252.338O47763374518.318O47808812982.318O48614297688.340O50022914142.298O50022914142.338O50704829622.318O55209884805.296O55584463448.340O56416396982.318O59623432085.318O60216801886.298O60216801886.338O61464066679.298O63650366863.298O63650366863.338O64096163541.318O64474006218.298O65049786611.318O65333132151.340O65961212488.296O66384283877.338O8604748773.298 P10759843066.318P10899727556.318P13833288218.340P14639119327.338P15222097189.298P15222097189.338P20179369217.318P20406927805.340P21214192760.318P22533188115.340P24355519453.338P32097984293.298P32097984293.338P32765882668.296P33452098390.298P33452098390.338P34787641857.318P3508358858.296 P3508358858.338 P36379372886.298P36379372886.338P36957875244.338P39206163140.318P40048048410.295P40048048410.337P40741054422.295P40741054422.337P41421207522.318P41903025153.318P42133856477.298P43288235210.296P43288235210.338P43700797910.295P43700797910.337P43817786156.296P44067980844.338P46116577274.338P47047506707.298P47876372191.296P50927926572.296P52938159617.318P54022373786.318P54899449626.295P54899449626.337P55103662124.338P55283175755.317P58041177900.296P60052482049.318P61592333368.300P61592333368.317P62217962028.338P63608839937.318P64700105754.340P66292560634.298P7750690063.300 P7750690063.317 Q12685901426.318Q12966218890.298Q12966218890.340Q13268124341.300Q15605514303.269Q15605927357.298Q15605927357.340Q15616001562.313Q15616016668.333Q15616165452.271Q15616165452.296Q15616165452.314Q15618062994.293Q15665829027.298Q15768661623.318Q18795003876.300Q18795003876.317Q18797180388.299Q18797180388.316Q19398679185.340Q19561563123.272Q19561563123.315Q19561597574.271Q19561597574.314Q19979689448.297Q21767670690.298Q21913098002.295Q21913099147.335Q23163703743.298Q2501392942.269 Q2514075779.293 Q2516073483.313 Q2516122381.333 Q2516237405.296 Q27441098135.298Q27441098135.340Q27938701970.295Q27938704907.335Q27942454161.298Q2803826605.298 Q28074340950.297Q29775981542.298Q31018323096.298Q31018323096.340Q3125606468.298 Q33137450695.298Q33681886389.300Q33681886389.317Q34362053984.298Q34362053984.340Q34362328320.300Q34362328320.317Q34966479902.318Q35292381455.295Q35292384662.335Q36313239610.298Q36858517963.318Q38250484404.318Q39682406333.298Q39682406333.340Q39682816575.269Q39688699802.296Q39689041209.272Q39689041209.315Q39689091868.333Q39689091920.292Q39922425103.271Q39922425103.314Q40509833325.297Q42439168719.298Q42439168719.340Q42439443119.300Q42439443119.317Q42441265899.318Q43929084639.298Q43929084639.340Q44569655930.272Q44569655930.315Q47223635094.300Q48117823211.300Q48117823211.317Q48118064779.298Q48118064779.340Q48358016498.318Q49300931806.296Q49303289227.297Q49698585326.298Q49698585326.315Q49962066831.297Q51518068631.298Q51518068631.340Q52744951088.299Q52744951088.316Q52747231024.300Q52747231024.317Q5278442951.296 Q53799182759.298Q54050590453.296Q54386358946.340Q55408699622.340Q56391302963.318Q57607133834.298Q57607133834.340Q58304474964.297Q58496806552.298Q58496806552.340Q59264526015.340Q59865321072.300Q59865321072.317Q59865603600.298Q59865603600.340Q59867700788.318Q62050575015.340Q62411254029.333Q62411254081.292Q62411648395.296Q62425983022.269Q6366768863.298 Q6366768863.340 Q64681845186.318Q64683667846.300Q64683667846.317Q64683942374.298Q64683942374.340Q65188245677.340Q66307672494.297Q67117497828.300Q67119445988.299Q67618520726.300Q67618520726.317Q7526555670.335 Q7526558863.295 Q7652195414.297 Q7652195414.314 Q9080548402.297 Q9092853651.318 Q9214356935.340 Q9356559660.298 Q9356756743.275 Q9356872455.317 Q9633850233.271 Q9633850233.314 Q9634015756.272 Q9634015756.315 Q9644583048.298 Q9644583048.340 Q9646680236.318 Q9928249826.297 00000400800900=00A00B02b05:06Y08;09Z0;<0<j0?M0Ak0Al0Am0DH0DI0DJ0F80Gi0IR0K10LS0N20OT0OU0OV0QD0S50UZ0XG0XH0ZG0\G0^30_b0aF0ck0fX0iI0ke0md0od11N11T11U11V11W11[11_11g11l12B13a15C15D15E15F15G16f18E19d1;F1;T1;U1;Y1=81>Z1@<1@=1@>1A]1C<1D[1F=1G_1Gf1Gn1HB1Hf1Hn1Ho1I01I81I91I?1I@1IA1IQ1L11L21L61L71L;1L?1LE1LF1LK1Mm1N:1N?1NQ1NR1O61PU1R71T:1UY1W;1WX1W\1X\1Xd1Xj1Xk1Xl1Z;1\k1_=1_>1_?1_C1_D1_H1_I1_J1_K1`01`11`81`91aX1c:1eO1f51fj1g?1gC1i@1l01n`1o61o91o:1o;1o<1o=1o>1oB1oC1oJ1oN1oO1oP1oQ1oR1oS1oT1oU21R24B24V26826926I26J26\26g26h26l27427527627727;27i29H29I29M29N2;02;42;52;62<62<:2<;2<<2<=2<>2=o2>02>42>@2>E2>F2>S2>T2>j2?\2?]2?c2?d2?e2?i2?j2@42@<2@=2B12B22B32BD2BE2BF2BG2Bj2Bk2Bl2C=2C>2Cb2Cj2DC2DD2DH2EM2EN2E]2F[2G02GE2GF2GG2GH2GI2GJ2GK2GL2GM2GN2GO2GP2GQ2GR2GS2GT2GU2GV2GW2GX2GY2GZ2G[2G\2H@2HA2HB2HC2HD2HE2HF2HG2HH2HI2HJ2HK2HL2HM2HN2HO2HP2HQ2HR2HS2HT2HU2HV2I:2I;2I<2I=2I>2I?2I@2IA2IB2IC2ID2IE2IF2IG2IH2II2Ka2ME2PA2R_2U22WH2Xm2[S2[T2^E2``2c32eI2gd2j?2l]2nB2od31I33d36B38`3;13=L3?j3BE3Dc3FH3Gm3JE3Kg3ML3Og3RE3T`3W>3X_3[I3]_3`:3a_3cK3ef3hD3jb3mM3oh41M44746d49B4:g4=c4?A4Ac4DH4Eh4Ei4Ej4Ek4GA4HW4J04KI4Lb4N84ON4Pg4R=4TE4V;4W`4YH4Zm4\U4^V4`?4ak4cT4e@4g@4iP4kN4mO4ob51852N53g55@56V56W56X58V5:W5<U5=l5?H5@f5B<5CU5E>5F_5F`5Fa5Fb5Fc5Fd5Fe5Hf5JG5Kk5MQ5MR5Nk5PA5QZ5S05TF5U\5W55XN5Yd5[:5\S5^^5`:5aY5cG5e85fW5gm5iF5j\5l55l65nP60m63565@66d68969N6:m6<O6=d6=e6=f6?K6A36BX6D@6EU6EV6Fk6I>6J_6J`6Ja6Jb6LY6Mo6OH6Q^6Q_6Q`6Qa6Qb6Qc6Qd6S=6TS6Ui6W?6XU6Yn6[m6^;6`L6bH6dG6ea6eb6gG6hl6hm6hn6jR6l36mO6nn70R72673Z75976U78479M7:i7<B7=^7?77@S7Ao7CdS2FBS2FBFS2FBS2FBFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2p1FFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc2p13HTc3SP13SZC3SPR2F04SP1RFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC3RLP3LN04APRF3EQL2x23x153x163x174POSTS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC3RLP4APRF2Lw4Hp1a3HLw2L93x313x443x453x464POSTFS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC4APPA3x313x443x453x464POSTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2p12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC3RLP3LN04APRF3EQL2x23x153x163x174POSTS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC3RLP4APRF2Lw4Hp1a3HLw2L93x313x443x453x464POSTS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2bs3LEN2Hn3LFB2FB4rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP3LN04APRF3EQL2r12p12Lw3Hr13Hp14HOK12KT2KU2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2bs3LEN2Hn3LFB2FB4rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP4APRF2p12Lw4Hp1a3HLw2L92HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC4APPA3x313x443x453x464POSTS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12p12RP3RLP3SPR2F04SP1R4Hp1a2p34Hp3aS4rawpFFFS2FBS2FBS2lo3sp1S3sp1S1n4rawp2P12L13LN03PLNS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCFSFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R2lo3LOS3ALOFS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1SSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS2FB2F0S2sp3sp1S1R2lo3LOS2FB3ALO2F1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1n4rawpFFS2r33Hr3FS1n2HnFSS1n2FB4rawp4APRFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3RLP3LN03PLN3ACV3SPR2F04SP1R3RCEFS2FBFS2FBS2FBS1n2HnFS3sp1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12RP3RLP3SPR2F04SP1R2p14Hp1aS1A1n4rawp2RAS3sp1S1n4rawp2p32L33HL3FS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP3LN03PLN3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1n4rawp2P12p13RLP3Hp12p33Hp3S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2L33LR3S1n2HnFFS1R4STKg4STKs4STKf2sp1A1n2bs2A02Hn2FB3sp14rawp3ACV3SPR2F04SP1R3RCE2p12Lw3HLw2L9S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A03LEN2Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3ACV3SPR2F04SP1R3RCEFFS2FBFS2FBFFFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTFS2Lw2K9FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP3LN03PLN3SPR2F04SP1RS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp14rawp2p12p32L33LR3S1n4rawp2P12L13PLN2KLS2loS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12p12RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1n4rawp2P12p13RLP3Hp1S1AFSFSFS2FBFS2FB2F0S2FBFFFSFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12p12RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2RP3RLP3ACV3SPR2F04SP1R3RCE4Hp1a2p32L33LR34Hp3a3HL3S1R2lo3LOS2FB3ALO2F1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1SS1n2FB4rawp4APRFFS1R1n4rawp3ACV3RCES2sp2lo3sp1FS2FBS2r13Hr1FFFS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS2FBFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS2FBFSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2FBFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12p12RP3RLP3SPR2F04SP1R4Hp1a2p32L33LR34Hp3aFS2FBS4CNTj1n3CJ0S3sp1SS4CNTj1n4CNT1FS1n4rawp2P13RLP2p13Hp1S1R3NS14STKg4STKs4STKf5STKg03NRT2sp2lo3SLO3sp13SP1FS1i2HiFFS2FBFS1R2lo3LOSS2sp3sp1FS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp2P12RP3RLP3ACV3SPR2F04SP1R3RCE2p12Lw4Hp1a3HLw2L9FFS2r33Hr31r2KN1q1HFFSS2FB2r03F641q1r1H2H02q02H43sp14SP1MFFS2r13Hr11r2KT1q1HSS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2lo3sp1S1R1n2lo3LOS4rawp3ALO3RCEFS2FBS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCESS2sp2lo3sp13SP1S1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1n4rawp2p12Lw3HLw2L9S1n4rawp2p12Lw3HLw2L9FFFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB3LOS3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP3ALO3RCE2p12Lw4Hp1a3HLw2L9S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC2RA3RLP4APPA4APRF2Lw4Hp1a3HLw2L94QLEN3x313x443x453x464POSTS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO3RCE2Lw3HLw2L94QLENFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3RLP3ALO3RCE2Lw4Hp1a3HLw2L9S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3RCE2p12Lw3HLw2L94QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2P12L12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3RLP3LN03ALO3RCE3EQLS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACV2p1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs3LEN2Hn3LFB2FB4rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RA3RLP4APPA4APRF2p12Lw4Hp1a3HLw2L94QLEN2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP12p13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2p1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13x433SZC2RA3RLP4APPA4APRF2Lw4Hp1a3HLw2L94QLEN3x313x443x453x464POSTS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1FFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3RCE2p12Lw3HLw2L9S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3SPR2F82F0S1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n2bs2Hn3TOP3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02HBS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs2Hn3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RCE2p12Lw3HLw2L91HS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2p11HFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3ALO2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC3ALOS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p12HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZC3ALOS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCFFFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2bs2Hn3LFB4rawp2P12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3RLP2p14Hp1aS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCFFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2p1S1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2HTS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02p12HBS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2p1S1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2p1S1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02p13SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02p1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2bs2Hn3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2p12Lw3HLw2L9". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI CINFO ALGNULL MDALG GETINT NEXTLEN NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_97468 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 j32 alg : list byte)
      (rawp P1 L1 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 g8 g12 g16 (le8 (Z_to_bv 64 P1)) (le8 (Z_to_bv 64 L1)) FSHXL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P1 -> 0 <= L1 -> P1 + L1 <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr (A + 16) 3 + al_sb AL)) s4v (Z_to_bv 64 n) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 (rawp + n)) (Z_to_bv 64 (A + 16))
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x979ec) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s4v. intros D RAWB RP RA RLP LN0 PLN BPHI BFFR BUD BUDF UW.
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
    (* [comment removed for export] *)
    cb8_to_c8 G18 (@nil cell). rewrite le_bytes_to_word_le8 in G18.
    cb8_to_c8 G22 (@nil cell). rewrite le_bytes_to_word_le8 in G22.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    pose proof (conj RAWB I) as RAWBbox. clear RAWB.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *)
      zstep. zstep. exitG (tail_97558 R HIA) (-21350) TPX SM0' HKc MFc RP RP. }
    assert (EQL : P1 + L1 = rawp + n).
    { change 18446744073709551615 with (Z.ones 64) in KL. rewrite ?Z.land_ones in KL by (clear; lia).
      rewrite ?Z.mod_small in KL by (clear - RLP LN0 PLN RP RCE ACV; lia). clear - KL RLP LN0 PLN. lia. }
    clear KL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 144) 1%nat as OPP. frame_aobj FSH (FB + 176) 1%nat as OL2.
    rawb_now.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := FB + 144) (LENP := FB + 176) (P := P1) (END := rawp + n) (BUF := rawp) (bs := bs) (tag := 6) (lo := lo) (lenv := Z_to_bv 64 L1);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact OL2 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact RLP | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 144) _ => eassumption
                 | |- rw_cells _ _ (FB + 176) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp [CB _ bs] |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- P1 <= rawp + n => clear - PLN LN0; lia
                 | |- rawp + n <= rawp + _ => rewrite LEN; clear; lia
                 | |- rawp + _ < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                 | |- FB + 144 + 8 <= FB + 176 \/ _ => left; clear; lia
                 | |- _ = 0 \/ FB + 144 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- _ = 0 \/ FB + 176 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- (FB + 144) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- (FB + 176) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 144 => clear - F0; lia
                 | |- 0 < FB + 176 => clear - F0; lia
                 | |- 0 < rawp => exact RP
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- FB + 144 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- FB + 176 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- _ = 0 \/ rawp + _ <= sp1 - 16 \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 end
               | match goal with |- ?g => idtac "GTO-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GTO-LEFT:" g end.
    clear GT' ABc OPP OL2.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : P1 <= ?pp <= rawp + n |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ _ (FB + 176) [C8 ?lw] |- _ => rename lw into Lw end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    2:{ (* [comment removed for export] *)
        zstep. zstep.
        zstep. if_cases KU; zify_cond KU.
        { (* [comment removed for export] *) zstep. zstep. zstep. exitG (tail_97460 R HIA) r1 TPX SM0' HKc MFc Hr1 RP. }
        (* [comment removed for export] *)
        lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep.
        clear ABc.
        dv_shapes. si_now. try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
        intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
        subst LB2.
        lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
        eapply (from_974b0 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (P := rawp) (LN := n)
                                     (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
          first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW
                | lazymatch goal with
                  | |- rawp <= rawp => clear; lia
                  | |- 0 <= n => clear - Hn; lia
                  | |- rawp + n <= rawp + n => clear; lia
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
                            | first [ c24_dva Hn | match goal with |- ?g => idtac "DVAabs-LEFT:" g end ] ]
                  end
                | assumption
                | match goal with |- ?g => idtac "F971abs-LEFT:" g end ]
        end. }
    (* [comment removed for export] *)
    assert (R10 : r1 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw]. clear HOK1 KT Hr1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases K9; zify_cond K9.
    { (* [comment removed for export] *)
      zstep. zstep. exitG (tail_97768 R HIA) (-22272) TPX SM0' HKc MFc RP RP. }
    assert (L9 : bv_unsigned Lw = 9).
    { change 18446744073709551615 with (Z.ones 64) in K9. rewrite ?Z.land_ones in K9 by (clear; lia). rewrite ?Z.mod_small in K9 by (clear - LR; lia). clear - K9. lia. }
    clear K9.
    (* [comment removed for export] *)
    zstep.
    rawb_now.
    lazymatch goal with RB : rw_cells _ ?mx rawp [CB _ bs] |- _ =>
      destruct (bytes_at_sliceF mx rawp bs p1 9 (cb_bytes_at _ _ _ _ RB) ltac:(clear - Hp1 RLP; lia) ltac:(clear; lia) ltac:(rewrite LEN; clear - HLw L9 Hp1; lia)) as [QBY QLEN] end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmpI 0x24d20 QBY.
    zstep. if_cases KB1; zify_cond KB1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
      frame_aobj FSH (FB + 144) 1%nat as OPP. frame_aobj FSH (FB + 176) 1%nat as OL2.
      try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
      pose proof NEXTLEN as NL'. unfold pkcs7_nextlen_stmtA, A_PKCS7_NEXTLEN_G in NL'.
      acallxA_sp sp1
        (eapply NL' with (CS := hcs asegs R HIA hc) (PP := FB + 144) (LENP := FB + 176) (P := p1 + 9) (END := rawp + n) (BUF := rawp) (bs := bs) (lo := lo) (lenv := Lw);
           rewrite ?(unsigned_lit sp1) by exact SP1R;
           first [ exact OPP | exact OL2 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | reflexivity
                 | lazymatch goal with
                   | |- rw_cells _ _ (FB + 144) _ => eassumption
                   | |- rw_cells _ _ (FB + 176) _ => eassumption
                   | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp [CB _ bs] |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                   | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                   | |- stk _ _ lo _ => assumption
                   | |- mem_inv _ _ => assumption
                   | |- rawp <= p1 + 9 => clear - Hp1 RLP; lia
                   | |- p1 + 9 <= rawp + n => clear - HLw L9; lia
                   | |- rawp + n <= rawp + _ => rewrite LEN; clear; lia
                   | |- rawp + _ < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                   | |- FB + 144 + 8 <= FB + 176 \/ _ => left; clear; lia
                   | |- _ = 0 \/ FB + 144 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                   | |- _ = 0 \/ FB + 176 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                   | |- (FB + 144) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                   | |- (FB + 176) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                   | |- 0 < FB + 144 => clear - F0; lia
                   | |- 0 < FB + 176 => clear - F0; lia
                   | |- 0 < rawp => exact RP
                   | |- lo <= sp1 - 64 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                   | |- alloc_ceiling <= lo => clear - ALO LOS; lia
                   | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                   | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                   | |- FB + 144 + 8 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                   | |- FB + 176 + 8 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                   | |- _ = 0 \/ rawp + _ <= lo \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS; lia
                   | |- _ = Z_to_bv 64 (p1 + 9) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A09-FORM:" g end]
                   end
                 | match goal with |- ?g => idtac "NL-PRE-LEFT:" g end ]).
      all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "NL-LEFT:" g end.
      clear NL' ABc OPP OL2.
      match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r3 end.
      match goal with H : _ < r3 <= 0 |- _ => rename H into Hr3 end.
      match goal with H : r3 = 0 -> _ |- _ => rename H into HOK3 end.
      match goal with H : p1 + 9 <= ?pp <= rawp + n |- _ => rename H into Hp3; rename pp into p3 end.
      lazymatch goal with H : rw_cells _ _ (FB + 176) [C8 ?lw] |- _ => rename lw into L3 end.
      pose proof (bv_unsigned_in_range 64 L3) as LR3. unfold bv_modulus in LR3. cbn [Z.pow Z.of_N Pos.pow] in LR3.
      (* [comment removed for export] *)
      zstep. if_cases KN; zify_cond KN.
      2:{ (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. exitG (tail_97460 R HIA) r3 TPX SM0' HKc MFc Hr3 RP. }
      assert (R30 : r3 = 0).
      { change 18446744073709551615 with (Z.ones 64) in KN. rewrite ?Z.land_ones in KN by (clear; lia). clear - KN Hr3. Z.div_mod_to_equations. lia. }
      subst r3. destruct (HOK3 eq_refl) as [Hp3a HL3]. clear HOK3 KN Hr3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KE; zify_cond KE.
      2:{ (* [comment removed for export] *)
          zstep. zstep. exitG (tail_97768 R HIA) (-22272) TPX SM0' HKc MFc RP RP. }
      dv_shapes. si_now. try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      subst LB2.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
      eapply (from_974b0 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (P := p3) (LN := bv_unsigned L3)
                                   (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
        first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW
              | lazymatch goal with
                | |- rawp <= p3 => clear - Hp3 Hp1 RLP; lia
                | |- 0 <= bv_unsigned L3 => clear - LR3; lia
                | |- p3 + bv_unsigned L3 <= rawp + n => clear - HL3; lia
                | |- 0 < rawp => exact RP
                | |- rw_cells _ _ rawp _ => eassumption
                | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                    cbv delta [A_pkcs7_parse_C24.dvA] beta;
                    split; [eassumption|]; split; [exact HK9|]; split; [exact MF9'|];
                    split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [eassumption|]; split; [eassumption|];
                    split; [eassumption|]; split; [eassumption|];
                    repeat match goal with |- _ /\ _ => split end;
                    first [ eassumption | reflexivity
                          | lazymatch goal with |- rw_cells _ mx (FB + 176) [CB 8 (le8 (Z_to_bv 64 (bv_unsigned L3)))] => rewrite Z_to_bv_bv_unsigned; eassumption end
                          | lazymatch goal with |- rw_cells _ mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVAdat-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "F971dat-LEFT:" g end ]
      end.
    - (* [comment removed for export] *)
      dv_shapes. si_now. try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
      lazymatch goal with G22x : rw_cells _ ?mx (FB + 176) [CB 8 (le8 ?lw)] |- _ =>
        replace lw with (Z_to_bv 64 9 : word) in G22x by (symmetry; apply bv_eq; rewrite L9; reflexivity) end.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      subst LB2.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
      eapply (from_976d0 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (p1 := p1)
                                   (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
        first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF
              | lazymatch goal with
                | |- rawp <= p1 => clear - Hp1 RLP; lia
                | |- p1 + 9 <= rawp + n => clear - HLw L9; lia
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
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA3e0-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "F973E0-LEFT:" g end ]
      end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
