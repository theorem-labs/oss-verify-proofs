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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24 A_pkcs7_parse_H24 A_pkcs7_parse_I224 A_pkcs7_parse_I24.
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
  Hypothesis AMC : arl_amemcpy R = A_AMEMCPY_F.            (* [comment removed for export] *)
  Hypothesis CINFO : pkcs7_cinfo_stmtA asegs R HIA A_PKCS7_CINFO_G.
  Hypothesis ALGNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL_G.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG_G 64.
  Hypothesis GETINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT_G.
  Hypothesis NEXTLEN : pkcs7_nextlen_stmtA asegs AL A_PKCS7_NEXTLEN_G.
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.57000007S1R3NA0". (* [comment removed for export] *)
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
  Hypothesis D47 : n = 0 \/ DATA + n + 8 <= 2 ^ 47.      (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.11400000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L42852043645.128L7241631773.128 00000X014S2LF2sp1A1n2bs2A02Hn3LFB1B2cs2H02H11i2HiS2LF2sp1A1n2bs3LFB1B2cs1i2Hi". (* [comment removed for export] *)
  #[using="LF sp A n bs A0 Hn LFB"] Lemma rw_cells_transport_pw : forall W mq mq' B cs,
    rw_cells asegs mq B cs -> munch W mq mq' -> wmono asegs mq mq' ->
    (forall x, B <= x < B + Z.of_nat (cells_size cs) -> outside W x) ->
    rw_cells asegs mq' B cs.
  Proof.
    intros W mq mq' B cs [[Hwf Hb] Hw] MU WM HO. split; [split; [exact Hwf|]|].
    - ddestruct Hb as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
      intros i Hi. unfold mrd. rewrite MU; [apply H2; exact Hi|].
      rewrite wa_unsigned by lia. apply HO. rewrite cells_bytes_length in Hi by exact Hwf. lia.
    - eapply wr_at_transport; eauto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rawb_via P2 RBb RIN RA0 :=
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
    lazymatch type of RBb with rw_cells _ ?m0 ?rawp [CB (Z.to_nat n) ?xs] /\ True =>
    lazymatch type of P2 with presW _ _ _ _ ?LBq LF _ _ _ m0 mx =>
      let RBx := fresh "RAWBx" in
      assert (RBx : rw_cells asegs mx rawp [CB (Z.to_nat n) xs]);
      [ let N0 := fresh "N0" in let RA := fresh "RA" in
        destruct RA0 as [N0|RA];
        [ generalize (proj1 RBb); rewrite N0; change (Z.to_nat 0) with 0%nat; intros H0; exact (rw_cells_CB0 _ _ _ _ _ H0)
        | eapply (presA_rw_cells asegs R LBq LF _ _ _ [(A, A + 1440)] m0 mx rawp [CB (Z.to_nat n) xs] (presW_presA asegs R HIA _ _ _ _ _ _ _ _ P2) (proj1 RBb));
          [ cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia);
            eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia]
          | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); cbn; split; [clear - RA; lia| exact I] ] ]
      | ]
    end end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05]0@C1123566675.321 C65802607699.320D16071854214.321D16116793040.297D16901939902.321D16908881264.321D19389307406.321D31548437675.321D420007634.296  D44450165448.297D50818716548.275D50818716548.296D55641685675.321D60109196847.297D60128441358.321D61549796208.321D64420321033.275K15777363634.321K16199997286.297K23293880678.297K30406640486.297K33965119078.297K41460675942.297K42064520925.297K48892179322.321K59095072946.321K66449870202.321K8704438374.297 L10370335306.1  L10596430123.1  L11838558071.1  L11879002598.1  L12267397436.2  L13340048728.1  L13587842953.295L1381922745.183 L15226064563.2  L1540877545.3   L15618147883.1  L15686577978.1  L15777915094.3  L15824827452.2  L16130444820.8  L16130444949.24 L16195849360.2  L16467427964.282L16467427964.306L1685717371.0   L16896526054.1  L17064006458.1  L17660516633.283L17762320911.2  L18404682370.6  L19769535484.2  L19959024712.1  L19980016842.7  L20354825767.3  L20367284705.183L21007906567.2  L21386098076.204L2149169966.4   L21654730866.2  L21710720070.6  L21868500043.2  L22557285548.204L22899008887.1  L22939159100.2  L23298126480.2  L23615739305.3  L24128180555.1  L2424960062.2   L2514189370.1   L26014119652.4  L26016216788.4  L2621559066.1   L26890104681.15 L27270131831.1  L27650499371.1  L27666008530.2  L27831285827.204L27940405558.13 L29409929468.294L29773715284.1  L29815110740.2  L30013901687.1  L30052271987.20 L30410922128.2  L30680958909.2  L31636313402.1  L31653556939.1  L31852292097.2  L32110924979.2  L32454903270.1  L32695321771.183L32750658443.2  L33202646768.183L33210864628.282L33437929969.2  L33532570708.1  L33570290807.1  L33969393040.2  L33982705724.2  L34673485611.1  L34767689079.1  L3522534509.3   L35336339085.16 L35666023782.15 L36382048241.2  L36961436047.261L36961436047.306L36963035632.282L37663591692.9  L37714553091.1  L38235734261.1  L38738405142.1  L39074667104.5  L39263166881.0  L39686831147.1  L40062184381.2  L40228640085.0  L40281191306.3  L40746874225.3  L41096910396.2  L41473207952.2  L41837021199.2  L41869966199.1  L42077060395.2  L42139611770.2  L42642555220.1  L43298250349.3  L43300649301.0  L43690857329.3  L43810982283.2  L44246411488.183L45591255342.4  L46290454573.5  L46541147848.1  L47046946167.3  L4725827959.1   L47443067297.0  L47870616696.2  L47882514004.1  L48904993004.2  L48984809847.1  L49495212411.2  L49508988902.1  L50790584144.17 L50790731766.15 L50925318027.2  L51382586950.5  L51382587079.8  L51857230996.2  L52045659405.3  L522420538.1    L52541166199.1  L53510884240.282L53597055279.1  L53792287453.6  L54246093652.1  L54692181363.20 L54864364148.1  L54906310077.2  L54963599545.2  L55059598703.261L55714664252.2  L55842747208.3  L56523586534.1  L57124690773.0  L57413703668.183L57421212400.282L57777299826.2  L57951117045.3  L58039649675.2  L58304396918.4  L58748427563.1  L58794466335.15 L59095635670.3  L59308586248.2  L59310685328.5  L59321161984.6  L59427880762.305L59578101107.3  L59579835366.282L60008840208.2  L60045244279.1  L60073096520.5  L60098763854.6  L6031628760.2   L61545304294.1  L62018535662.1  L6203936179.1   L62413581882.1  L64423694358.2  L64829056059.1  L64830457019.2  L64850595401.0  L66151427842.16 L66298372189.2  L66445969132.2  L66572605252.10 L67028235242.17 L67200924489.16 L67884573201.1  L68268705984.8  L68272074258.8  L6899380056.1   L7122685215.10  L7735748552.2   L8060063860.1   L8186173104.7   L8454980662.21  L8691805072.2   L881835912.0    L8935664980.1   L9080220944.4   L9356559676.20  L9631767084.2   O10567734856.319O12408905496.321O15174400344.318O16866295602.321O17217116232.319O17846813406.318O26475597711.321O28042800350.318O33870522200.318O35198608664.321O42395367124.319O44938202843.319O45969540168.319O4702012722.321 O47383255252.319O50022914142.321O55209884805.319O60216801886.321O61464066679.321O63650366863.321O64474006218.321O65961212488.319O8604748773.321 P12278670331.275P12278670331.296P15222097189.321P15835051771.275P15835051771.296P21870859916.275P21870859916.296P22945712379.275P22945712379.296P32097984293.321P32765882668.319P33452098390.321P33980871419.275P33980871419.296P3508358858.319 P36379372886.321P40048048410.318P40741054422.318P41095599355.275P41095599355.296P42133856477.321P43288235210.319P43700797910.318P43817786156.319P47047506707.321P47876372191.319P49501542924.297P50927926572.319P54899449626.318P54978542206.275P54978542206.296P55703916027.275P55703916027.296P58041177900.319P64409801425.297P66292560634.321P7750690063.275 P7750690063.296 Q11816400688.275Q11818319152.274Q12244091759.296Q12966218890.321Q15163850165.275Q15163850165.296Q15605927357.321Q15616165452.294Q15616380325.293Q16114545872.296Q16116793040.297Q19561563123.295Q19561597574.294Q21767670690.321Q21913097873.316Q21921356332.292Q22324126766.293Q22712450012.275Q22712450012.296Q23163703743.321Q2516481972.293 Q25511591557.275Q25511591557.296Q25513505925.274Q25513505925.295Q27441098135.321Q27938702097.316Q27942454161.321Q27942899219.271Q2803826605.321 Q29434492334.293Q29775981542.321Q30292865948.293Q31018323096.321Q31254590166.275Q31700828917.275Q33137450695.321Q33264869686.296Q34362053984.321Q34362328320.275Q34362328320.296Q34499416751.321Q35288190350.271Q35292381324.316Q39682406333.321Q39689041209.295Q39922425103.294Q40794887669.272Q42439168719.321Q42439443119.275Q42439443119.296Q42439443119.297Q42755330731.295Q43929084639.321Q44447922376.296Q44450165448.297Q44569655930.295Q48118064779.321Q49698585326.273Q49698585326.294Q5118012149.295 Q5119959285.296 Q51518068631.321Q53677133549.294Q53799182759.321Q57607133834.321Q58496806552.321Q58576929967.321Q59865321072.275Q59865321072.296Q59865321072.297Q59865603600.321Q6366768863.321 Q64683667846.275Q64683667846.296Q64683667846.297Q64683942374.321Q67364751287.293Q67366860043.294Q7292257039.294 Q7518036401.292 Q7526558988.316 Q8041752945.294 Q9356756743.298 Q9633850233.294 Q9634015756.295 Q9644583048.321 00000400802[04L06g08I09k09l0<^0>O0A90Cc0Cd0E\0G>0H`0KR0Mh0OW0QF0S50Td0VS0XB0ZA0\W0^V0`E0`K0`O0`S0`W0`X0`]0b?0cV0cW0cc0cg0ck0cl0cm0dG0eS0eT0g60hX0hY0h]0ha0jC0jJ0j`0jh0jm0kE0kP0l;0lA0lk0m;0m<0mS0mT0n>0nB0nC0nD0nN0nR0nX0n\0nj0o70o<0oQ0oR0oV0o^10D10h12J12N12V12Z13Z13[13a13e13i13o14014414514615U17j17k17o18018118218618:18;18T19919:1:\1<>1=`1>F1>I1>M1>P1>b1>c1>g1>h1>i1?21?31?41?51?<1?@1?A1?B1?F1?G1?H1?I1?J1@51@E1@W1@\1@]1@a1@b1@c1@g1@h1@l1@m1A11A_1BM1BN1B]1C41C:1CF1CJ1CN1E01E41EF1EJ1FJ1FN1FO1FP1H21H31H?1HC1HD1IM1KP1KW1Kd1Ke1L41L81L^1L_1Le1M81MO1MP1MY1P31P41P81PK1PU1P]1Pa1Pd1Pi1Pm1Pn1Po1Q71Q81Q[1Q\1Q]1Qn1Rd1S@1SC1S]1TA1TE1T^1T_1Tc1U:1V?1V@1VA1VE1VT1WR1WY1WZ1W[1W\1W]1W^1W_1W`1Wa1Wb1Wc1Wd1We1Wf1Wg1Wh1Wi1XM1XN1XO1XP1XQ1XR1XS1[@1]o1`E1c21e\1hD1jn1mV20@22V25427R2:?2<n2>S2A12CO2Em2HZ2KI2Md2OI2Qg2TE2V`2Y92[[2^92`W2cD2en2h[2kJ2mh30M31n33a35S37f3:93<^3<_3<`3<a3>:3?S3@l3BS3D:3Ef3GR3Ie3Kf3Mg3OI3Q<3Rn3UD3V]3XS3ZH3\>3^33^43`53b63d73eQ3fi3hJ3ib3k;3mc40H41l44P44Q44R44S44T46847\4954:N4;g4=I4>h4@]4BQ4DA4Eb4G;4Hb4JI4Kb4Mm4OP4Q34SE4UW4UX4Wf4Wg4Wh4YA4YB4YC4YD4YE4YF4Z_4]44_H4aX4cW4do4fG4g_4iC4jg4lE4md4o@50\528S2FBS2FBS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APRF2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APRF2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS4rawpS2FBS2FBS2FBFS3sp1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A03LEN2Hn2FB3sp14rawp2RP3SPR2F04SP1RFS2sp3sp13SP1S2FBS2FBFFS1n2FB4rawp4APRF1a1k2H12H2S1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCE1a1k2H1FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSS2FBS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FB2F0S1A2lo4ALO13sp12xq3HxqS1n4rawpS3sp1S1R3HIA1h2sp3TOP3sp13SP1S1n2Hn4rawpS1R4STKg4STKs4STKf2sp1A1n2bs2Hn2FB3sp14rawpS1n2HnS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r13Hr1S1n2FB4rawp4APRFFS1A1n4rawp2N02xq3Hxq2RAFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r13Hr1S2FBFFS1R3HIA2hcS2FBS1n2HnS2FBS1A1n4rawp3RA1S1A1n4rawp2RAS3sp1S1R4STKg4STKs4STKf2spFS2FBS2r13Hr1S1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12r1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS1n4rawpS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1FS1n2HnS2FBS2FBS1n2HnFS2FBFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A03LEN2Hn2FB3sp14rawp2RP3ACV3SPR2F04SP1R3RCES1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A03LEN2Hn3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3ACV3SPR2F04SP1R3RCEFS2FBFFFS2FBS2FBFS1R4DIMG1n4rawp4RIMG1a2DaS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmS1AS2loS1AS1R1n4rawp3ACV3RCESS2FBFSS1R3HIA1hFFFS2FB2F0S2FBFFS2FBFSFFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp14rawp2RPS1n2FB4rawp4APRFS1R1n4rawp3ACV3RCES3sp1FS2FBSFS2FBFS2FBFS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSFS2lo3sp11a1k2H1S2lo2FB3sp14FBLO1a1k2H2S1n2HnS2sp3sp13SP1S2FBS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS1n4rawp2p12Lw3HLwS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2FBFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS4CNTj1n3CJ0S2FBSS1R4STKg4STKs4STKf2sp1A1n2bs2A03LEN2Hn2FB3sp14rawp2RP3ACV3SPR2F04SP1R3RCES1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LEN2Hn3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP3ACV3SPR2F04SP1R3RCES2Lw2LRS4CNTj1n4CNT1FS1n4rawp2p13Hp1S2FBS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP11HFS1i2HiS4DATA1n3Hn02xq3HxqS1n4rawp2N02p13Hp14Hp1aFS2FB1c2HcS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RSS2FBS2sp4DATA3sp13SP11XS1R2lo3LOSS2sp3sp1S2FBS1RS3sp1S2FBFFS2r13Hr1SS2FB2r03F641q1r1H2H02q02H43sp14SP1MFFS2r13Hr11r2KT1q1HS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP1S1R2lo3LOS3sp13ALO1a2Da4DLOxS1AS1R3HIA1h2sp3TOP2hc3HSc2HTS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2FBS1R1n2lo3LOS4rawp3ALO3RCEFS2FBS1A4DATA1n2bs3LEN2DA2NES1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCEFSS2FBS2sp2lo3sp13SP1S1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2FB2F0FFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO12FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2HBS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2HB5Ha_st5Hl_stFFFFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2HBS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F04SP1RFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p02w83ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI AMC CINFO ALGNULL MDALG GETINT NEXTLEN NA0 NB0 NRT bs AAL A0 CWA ASTK AOD HBY LEN Hn CRD DLO DA D47 SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_97404 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v16 v24 v80 : word) (g4 g8 g12 g16 j32 alg : list byte)
      (rawp : Z) (rt p0 w8 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 g8 g12 g16 (le8 (Z_to_bv 64 rawp)) (le8 (Z_to_bv 64 0)) FSHXL v16 v24 j32 (Z_to_bv 64 FB) alg v80
        ([C4 rt; C4 p0; C8 w8; C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] -> 0 < rawp ->
    (n = 0 \/ (rawp + n <= A \/ A + 1440 <= rawp)) ->
    (n = 0 \/ rawp + n <= DATA \/ DATA + n <= rawp) ->
    fresh_apart R LB LF rawp n ->
    (1 <= n -> aobj asegs AL CS mc DATA n) ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rawp) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr (A + 16) 3 + al_sb AL)) (Z_to_bv 64 DATA) (Z_to_bv 64 n) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 FB) (Z_to_bv 64 A) (Z_to_bv 64 (A + 16))
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97948) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D RAWZ RP RA0 SEP RFR ODc BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    lazymatch type of HHc with HM _ _ _ _ ?LB2x _ _ => set (LB2 := LB2x) in * end.
    change (In (FB, 24) (LB2 ++ fdata ((FB, 256) :: LF))) in INH.
    change (In (FB + 32, 256 - 40) (LB2 ++ fdata ((FB, 256) :: LF))) in IND.
    assert (CWAc : client_wrange L (LB2 ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { subst LB2. rewrite HTc. eapply client_wrange_mono; [exact CWA|]. intros b Hb. apply fdata_cons_sub. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    pose proof (blocks_below_hm R HIA hc _ _ mc LB2 HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) LB2) by (subst LB2; left; reflexivity).
    assert (RINF : In (rawp, n) (LB2 ++ fdata ((FB, 256) :: LF))) by (apply in_or_app; left; exact RIN).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [BR BA].
    pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA RIN ltac:(left; reflexivity)) as APRF. cbn [fst snd] in APRF.
    rewrite Forall_forall in BR. ddestruct (BR (rawp, n) ltac:(apply in_or_app; left; exact RIN)) as (_ & _ & _ & RIMG). cbn [fst snd] in RIMG. clear BR BA.
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
    (* [comment removed for export] *)
    assert (CRDs : client_range L (LB ++ fdata LF) (bv_unsigned sp) DATA n) by (eapply client_range_sep; [exact CRD| intros b Hb; exact Hb| exact DLO]).
    assert (CRD2 : client_range L (LB2 ++ fdata LF) (bv_unsigned sp) DATA n).
    { eapply client_range_incl; [exact CRDs|]. subst LB2. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
    assert (CRA2 : forall SPq, client_range L (LB2 ++ fdata ((FB, 256) :: LF)) SPq A 1440).
    { intros SPq. apply (client_range_lower L _ lo SPq A 1440); [| exact ALO1]. eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    (* [comment removed for export] *)
    cb8_to_c8 G18 (@nil cell). rewrite le_bytes_to_word_le8 in G18.
    cb8_to_c8 G22 (@nil cell). rewrite le_bytes_to_word_le8 in G22.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    pose proof (conj RAWZ I) as RAWZbox. clear RAWZ.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep.
    idtac "J-1".
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 425404) with (Z_to_bv 64 (arl_amemcpy R)) by (rewrite AMC; reflexivity).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    lazymatch goal with HH : HM _ _ _ hc _ _ m1 |- _ => rename HH into HH1 end.
    lazymatch goal with P2 : presW _ _ _ hc LB2 LF _ _ X0 mc m1 |- _ => rename P2 into PRES21 | _ => idtac "J: no PRES2 at m1" end.
    rawb_via PRES21 RAWZbox RIN RA0.
    lazymatch goal with RB : rw_cells _ m1 rawp [CB _ _] |- _ => apply (u8arr_of_rw_cells asegs) in RB; rename RB into RAWU end.
    assert (HBY1 : bytes_at asegs m1 DATA bs).
    { lazymatch goal with P1 : presW _ _ _ h LB LF _ _ X0 m m1 |- _ =>
        eapply presA_bytes_at0; [exact (presW_presA asegs R HIA _ _ _ _ _ _ _ _ P1)| exact HBY|] end.
      destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right]. rewrite LEN. split; [exact CRDs|].
      cbn. split; [| exact I]. clear - DA NE LEN. unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *. lia. }
    assert (ODX : aobj asegs AL (hcs asegs R HIA hc) m1 DATA n).
    { destruct (Z.lt_ge_cases n 1) as [Hn0|Hn1].
      - split; intros xq Hxq; exfalso; clear - Hxq Hn0; lia.
      - apply (aobj_cs_mono asegs AL _ _ _ _ _ HCSc). eapply presA_aobj0;
          [exact CSOK| exact (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PRES21)| exact (ODc Hn1)| intros xq Hxq; rewrite HSc; eapply hcs_below_top; exact Hxq|].
        right. split; [exact CRD2| clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia]. }
    pose proof (hm_aobj_block asegs R HIA hc _ _ m1 rawp n HH1 RIN) as OBUF1.
    assert (SI1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PRES21))|].
      intros a Ha. exact (si_outside1 L SI A 1440 a AOD Ha). }
    clear SIc.
    (* [comment removed for export] *)
    pose proof (conj PRES I) as PRESbox.
    lazymatch goal with P1 : presW _ _ _ h LB LF _ _ X0 m m1 |- _ => clear P1 end. clear PRES21.
    pose proof (artA_amemcpy asegs R HIA (arl_amemcpy R)) as SPC.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply SPC with (h := hc) (LB := LB2) (LF := (FB, 256) :: LF) (DST := rawp) (SRC := DATA) (n := n) (lo := lo) (ds := repeat (Z_to_bv 8 0) (Z.to_nat n)) (ss := bs); clear SPC;
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH1 | exact RAWU | exact HBY1 | exact LEN | exact OBUF1 | exact ODX | exact SEP | exact LOS | exact D47 | reflexivity
              | lazymatch goal with
                | |- _ = arl_amemcpy R \/ _ => left; reflexivity
                | |- Z.of_nat (length (repeat _ _)) = n => rewrite repeat_length; clear - Hn; lia
                | |- stk _ _ lo _ => assumption
                | |- mem_inv _ _ => assumption
                | |- lo <= sp1 - arl_need_amem R => pose proof NRT; clear - SLO SP1 NS1 NA0 H STKg0 STKs0 STKf0; lia
                | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                | |- rawp + n <= lo \/ _ => left; clear - RCE ALO LOS; lia
                | |- DATA + n <= lo \/ _ => destruct DLO as [X|X]; [left; exact X| right; clear - X SP1; lia]
                | |- n = 0 \/ rawp + n + 8 <= _ => destruct (Z.eq_dec n 0) as [E0|NE0]; [left; exact E0| right; clear - RCE ACV; lia]
                | |- n < _ => clear - Hn; lia
                | |- client_wrange _ _ _ _ rawp n => eapply client_wrange_block; [exact RINF| clear; lia| clear; lia]
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                end
              | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]. }
    all: match goal with |- forall _, _ -> aevtA _ _ _ _ => idtac | |- ?g => idtac "MEMCPY-LEFT:" g end.
    try clear SPC.
    cbv beta. intros ms2 PO. unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & E2 & MU & WM & MI2 & Ea0 & RAWU2 & ST2 & HH2).
    subst ms2. subst ua0.
    rewrite ?(unsigned_lit sp1) in MU by exact SP1R. rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0x97958)) with (Z_to_bv 64 0x97958 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    idtac "J-2".
    (* [comment removed for export] *)
    assert (HPm : presA asegs R LB2 ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [(rawp, rawp + n); (lo, sp1)] m1 m2).
    { eapply (presA_of_munch asegs R _ _ _ _ _ _ m1 m2 (hcs asegs R HIA hc) CSOKc); [| | exact MU| exact WM].
      - pose proof OBUF1 as CRr. apply aobj_crange in CRr.
        apply Forall_cons; [cbn [fst snd]; replace (rawp + n - rawp) with n by (clear; lia); exact CRr|].
        apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]|]. apply Forall_nil.
      - intros c Hc. eapply (cshd_hcs asegs R HIA hc); [exact HH1| apply Z.le_refl| exact Hc]. }
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJF : forall a k, FB <= a -> a + k <= FB + 256 -> disjoint_from [(rawp, rawp + n); (lo, sp1)] a k).
    { intros a k H1 H2. cbn. split; [clear - H1 H2 APRF; lia| split; [clear - H1 H2 FBLO; lia| exact I]]. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from [(rawp, rawp + n); (lo, sp1)] a k).
    { intros a k H1. cbn. split; [clear - H1 RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| split; [clear - H1; lia| exact I]]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) LB2 ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [(rawp, rawp + n); (lo, sp1)] m1 m2 FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add length]; exact CFBc | exact F8 | clear - F0; lia | exact HPm | cbn [cells_size csize Nat.add length]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G8; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    lazymatch goal with SV : rw_cells _ m1 (bv_unsigned sp + -104) _ |- _ =>
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in SV; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia] end.
    lazymatch goal with RS : rw_cells _ m1 (sp1 + 16) _ |- _ =>
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in RS; [| apply client_range_stack; clear; lia| apply DJs; clear; lia] end.
    lazymatch goal with SA : stk _ m1 sp1 (sp1 + 16) |- _ => apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in SA; [| clear; lia| apply DJs; clear; lia] end.
    lazymatch goal with SB : stk _ m1 (sp1 + 88) _ |- _ => apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in SB; [| clear; lia| apply DJs; clear; lia] end.
    lazymatch goal with SS : sshad _ _ m1 slo (bv_unsigned sp) |- _ => apply (presA_sshad asegs R _ _ _ _ _ _ m1 m2 _ _ HPm) in SS; [| exact SLOS| clear - HT TOP HSc; lia] | _ => idtac "J: no sshad at m1" end.
    lazymatch goal with OB : aobj _ _ CS m1 A 1440 |- _ =>
      apply (presA_aobj0 asegs R CS _ _ _ _ _ _ m1 m2 A 1440 CSOK HPm) in OB; [| intros xq Hxq; rewrite HSc; eapply hcs_below_top; exact Hxq| right; split; [exact (CRA2 sp1)| clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia]];
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OB) as OBJc2
    | _ => idtac "J: no OBJA at m1" end.
    lazymatch goal with CE : rw_cells _ m1 A _ |- _ =>
      apply (rw_cells_transport_pw _ m1 m2 _ _ CE MU) in WM as CELLS2;
      [ clear CE | cbn [cells_size csize Nat.add length]; intros xq Hxq; cbn [outside]; split; [| split; [clear - Hxq ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia| exact I]];
                   destruct RA0 as [N0|RA]; [clear - N0 Hxq; lia| clear - RA Hxq; lia] ] end.
    assert (SI2 : si_P SI m2).
    { eapply (si_munch_offdata L SI); [exact SI1| exact MU|]. intros a Da Wa. cbn [outside].
      pose proof (art_data_lo asegs R HIA) as DLOx. clear - Da Wa RIMG DIMG DLOx ALO LOS. split; [lia| split; [lia| exact I]]. }
    (* [comment removed for export] *)
    assert (PRES : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m2).
    { destruct PRESbox as [(P0 & C1' & C2' & C3') _]. split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (Q1 : presA asegs R LB2 ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [(lo, sp1); (rawp, rawp + n)] m1 m2).
      { eapply presA_weaken; [exact HPm| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
      pose proof (presA_drop_below asegs R HIA hc LB2 ((FB, 256) :: LF) [(rawp, rawp + n)] lo sp1 m1 m1 m2 sp1 HH1 Q1 ltac:(clear; lia) LOS) as Q2.
      assert (Q3 : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA hc) [(rawp, rawp + n)] m1 m2).
      { eapply presA_weaken; [exact Q2| subst LB2; intros b Hb; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      pose proof (presA_drop_fresh asegs R HIA hc LB LF [] rawp n m1 m2 sp1 Q3 RFR ltac:(clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia)) as Q4.
      rewrite HSc in Q4.
      eapply presA_weaken; [exact Q4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| clear; lia| intros x Hx; exact I]. }
    clear PRESbox HPm MU WM HH1 OBUF1 ODX HBY1 RAWU SI1 RINF.
    lazymatch goal with MI : mem_inv _ m1 |- _ => clear MI | _ => idtac end.
    lazymatch goal with SL : stk _ m1 lo sp1 |- _ => clear SL | _ => idtac end.
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA hc _ _ LB2 LF m2 (bv_unsigned sp) (bv_unsigned sp) X0 h HH2
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES3.
    apply (rw_cells_of_u8arr asegs) in RAWU2. replace (length bs) with (Z.to_nat n) in RAWU2 by (rewrite <- LEN, Nat2Z.id; reflexivity).
    pose proof (conj RAWU2 I) as RAWBbox. clear RAWU2.
    pose proof (hcs_ok asegs R HIA hc) as CSOKc'.
    idtac "J-3".
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    idtac "J-4".
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 144) 1%nat as OPP. frame_aobj FSH (FB + 176) 1%nat as OL2.
    lazymatch goal with P3 : presW _ _ _ hc LB2 LF _ _ X0 m2 ?mx |- context [MS _ _ _ _ _ ?mx _] => rawb_via P3 RAWBbox RIN RA0 | _ => idtac "J: no PRES3 before get_tag" end.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := FB + 144) (LENP := FB + 176) (P := rawp) (END := rawp + n) (BUF := rawp) (bs := bs) (tag := 48) (lo := lo) (lenv := Z_to_bv 64 0);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact OL2 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 144) _ => eassumption
                 | |- rw_cells _ _ (FB + 176) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp [CB _ bs] |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; lazymatch goal with HH : HM _ _ _ hc _ _ ?mx |- aobj _ _ _ ?mx _ _ => exact (hm_aobj_block asegs R HIA hc _ _ mx rawp n HH RIN) end
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- rawp <= rawp => clear; lia
                 | |- rawp <= rawp + n => clear - Hn; lia
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
                 | |- _ = Z_to_bv 64 (rawp + n) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "RPN-FORM:" g end]
                 end
               | match goal with |- ?g => idtac "GT1-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT1-LEFT:" g end.
    clear GT' ABc OPP OL2.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : rawp <= ?pp <= rawp + n |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ _ (FB + 176) [C8 ?lw] |- _ => rename lw into Lw end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    idtac "J-5".
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    2:{ (* [comment removed for export] *)
        zstep. zstep. zstep.
        first [ rewrite swrap32_errsum by (clear - Hr1; lia)
              | (change 18446744073709551616 with (2^64); rewrite swrap32_errsum by (clear - Hr1; lia))
              | (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); rewrite swrap32_errsum by (clear - Hr1; lia)) ].
        try change (18446744073709530368 - 2^64) with (-21248).
        zstep. zstep. zstep. zstep.
        try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end.
        lazymatch goal with P3 : presW _ _ _ hc LB2 LF _ _ X0 m2 ?mx |- context [MS _ _ _ _ _ ?mx _] => rawb_via P3 RAWBbox RIN RA0 | _ => idtac "J: no PRES3 at exit" end.
        exitG (tail_97460 R HIA) (r1 + -21248) TPX SM0' HKc MFc Hr1 RP. }
    assert (R10 : r1 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw]. clear HOK1 KT Hr1.
    assert (RA : rawp + n <= A \/ A + 1440 <= rawp) by (destruct RA0 as [N0|RA]; [exfalso; clear - N0 Hp1a Hp1; lia| exact RA]).
    (* [comment removed for export] *)
    dv_shapes. si_now.
    try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end.
    lazymatch goal with P3 : presW _ _ _ hc LB2 LF _ _ X0 m2 ?mx |- context [MS _ _ _ _ _ ?mx _] => rawb_via P3 RAWBbox RIN RA0 | _ => idtac "J: no PRES3 at 97180" end.
    lazymatch goal with H : rw_cells _ ?mx (FB + 176) [CB 8 (le8 Lw)] |- _ => rewrite <- (Z_to_bv_bv_unsigned Lw) in H end.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    subst LB2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
    eapply (from_97468 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (P1 := p1) (L1 := bv_unsigned Lw)
                                (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
      first [ exact RA | exact RP | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW
            | lazymatch goal with
              | |- rawp <= p1 => clear - Hp1; lia
              | |- 0 <= bv_unsigned Lw => clear - LR; lia
              | |- p1 + bv_unsigned Lw <= rawp + n => clear - HLw Hp1; lia
              | |- rw_cells _ _ rawp _ => eassumption
              | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  cbv delta [A_pkcs7_parse_C24.dvA] beta;
                  split; [eassumption|]; split; [exact HK9|]; split; [exact MF9'|];
                  split; [exact HTc|]; split; [exact HSc|]; split; [exact HFc|]; split; [exact HCSc|]; split; [eassumption|]; split; [eassumption|];
                  split; [exact PRES|]; split; [eassumption|];
                  repeat match goal with |- _ /\ _ => split end;
                  first [ eassumption | reflexivity
                        | lazymatch goal with |- rw_cells _ mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                        | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                        | first [ c24_dva Hn | match goal with |- ?g => idtac "DVAJ-LEFT:" g end ] ]
              end
            | assumption
            | match goal with |- ?g => idtac "F97180-LEFT:" g end ]
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
