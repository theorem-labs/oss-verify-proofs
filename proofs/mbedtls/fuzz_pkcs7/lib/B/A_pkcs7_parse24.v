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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24 A_pkcs7_parse_G24 A_pkcs7_parse_H24 A_pkcs7_parse_I224 A_pkcs7_parse_I24 A_pkcs7_parse_J24.
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
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.             (* [comment removed for export] *)
  Hypothesis CINFO : pkcs7_cinfo_stmtA asegs R HIA A_PKCS7_CINFO_G.
  Hypothesis ALGNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL_G.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG_G 64.
  Hypothesis GETINT : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT_G.
  Hypothesis NEXTLEN : pkcs7_nextlen_stmtA asegs AL A_PKCS7_NEXTLEN_G.
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.58000007S1R3NA0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.11500000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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

  Local Notation S1P := (S1P R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A DATA n lo slo bs).
  Local Notation sjZ := (SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)).
  Local Notation CSZ := ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
                         ++ buf_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 ++ [CB 8 (zeros 8)]
                         ++ [CB 744 (zeros 744)] ++ [CB 8 (zeros 8); CB 416 (zeros 416); CB 8 (zeros 8)] ++ signer_cells 0 0 sjZ).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03;0@D12252769165.274D16116793040.274D16116793040.299D4324896887.274 D44450165448.274D44450165448.299D57793146470.273D57793146470.298D60109196847.274D60109196847.299D62145055974.274D62232727210.273D62232727210.298D68243715475.273D68243715475.298K16199997286.274K16199997286.299K23293880678.274K23293880678.299K30406640486.274K30406640486.299K33965119078.274K33965119078.299K41460675942.274K41460675942.299K42064520925.274K42064520925.299K54978542206.273K54978542206.298K8704438374.274 K8704438374.299 L10370335306.1  L11879002598.1  L12266043405.1  L1254959567.3   L13259035468.2  L1540877545.3   L15756354262.7  L15822417165.1  L16044668601.3  L16195849360.2  L1685717371.0   L16896526054.1  L17660516633.262L17660517149.282L17856347970.11 L19769535484.2  L19980016842.7  L21007906567.2  L21866712442.1  L22941438733.1  L23298126480.2  L24128180555.1  L2424856791.3   L2424960062.2   L26016216788.4  L26224334382.264L26848404223.1  L26892418956.1  L28624903391.262L28624903899.282L28759872924.3  L28814043710.225L28818243751.261L28820447094.281L29773715284.1  L29859284829.3  L30410922128.2  L30570693355.2  L30848574733.265L31034375991.6  L31054838994.262L31054838994.282L32454903270.1  L33532570708.1  L33969393040.2  L33985112333.1  L35655753197.11 L35666023782.15 L37940357415.0  L38738405142.1  L39220637093.0  L40281191306.3  L41099742989.1  L41473207952.2  L42077060395.2  L42642555220.1  L44032381512.1  L45013537572.6  L45120313045.172L45122832123.179L46459939861.7  L47882514004.1  L49495212411.2  L49508988902.1  L49799904432.3  L50059436232.1  L50790731766.15 L51508673957.0  L52045659405.3  L52834355804.1  L54246093652.1  L54965870984.2  L55828188533.1  L56523586534.1  L56658999053.1  L57124690773.0  L57412690392.283L58293102803.4  L58293215814.5  L58794466335.14 L58936939498.8  L59308628179.4  L59308633593.3  L59310685328.5  L59578101107.3  L59579837421.179L59590228931.172L60098763854.6  L60884456420.1  L61545304294.1  L61603606271.2  L62037211595.16 L6203936179.1   L63343663265.0  L64423694358.2  L64850595401.0  L66151427842.16 L67028235242.17 L6899380056.1   L696052593.2    L7738195705.2   L800995545.261  L8691805072.2   L8935664980.1   L9144787073.263 L9356559676.20  L9631767084.2   P49501542924.274P49501542924.299P61592333368.273P61592333368.298P64409801425.274P64409801425.299P7750690063.273 P7750690063.298 Q15605536128.269Q15607990865.294Q16114545872.273Q16114545872.298Q16116793040.274Q16116793040.299Q18795003876.273Q18795003876.298Q18797180388.272Q18797180388.297Q2501439377.269 Q2508091456.294 Q33681886389.273Q33681886389.298Q34362328320.273Q34362328320.298Q40509833325.271Q40509833833.296Q42439443119.273Q42439443119.274Q42439443119.298Q42439443119.299Q42755330731.272Q42755330731.297Q44447922376.273Q44447922376.298Q44450165448.274Q44450165448.299Q48117823211.273Q48117823211.298Q49300978691.270Q49300978691.295Q49303289227.271Q49303289743.296Q49698585326.271Q49698585326.296Q49962066315.296Q49962066831.271Q52744951088.272Q52744951088.297Q52747231024.273Q52747231024.298Q5278473498.270 Q5278473498.295 Q54050633256.270Q54050633256.295Q5542005726.298 Q64683667846.273Q64683667846.274Q64683667846.298Q64683667846.299Q67618520726.273Q67618520726.298Q7652195414.270 Q7652195414.295 Q8041752945.271 Q8041752945.296 00000100n02002102n04004m05o07308<08=08>08?09<0:>0;90<90=40>40>o0?o0@j0Aj0Be0Ce0D`0E`0F[0G[0HV0IV0I\0I`0Id0J00J60JB0JP0JT0J`0Ja0Jb0Jf0KT0LG0Lm0M50MM0MS0MW0M[0M\0M`0Mi0Mo0N<0Nj0No0O30Oa0PT0P`0QQ0RB0S80S<0SE0SF0SM0T;0TN0U?0V50V90V=0V>0VB0Vk0WP0WQ0WT0WU0W^0Wb0Wc0Wd0Wh0Wm0XF0YC0ZH0Zb0Zf0Zg0Zk0[70[<0[j0[k0\70\:0\>0\?0\D0\H0\L0\M0]a0]b0^30^Y0_50_B0_N0_a0_j0`o0al0b60b90b=0b>0bl0c10c20c30c40cW0dM0dQ0dY0dZ0eH0eI0eM0f;0g90g@0hn0ja0l\0n\10M12C14615n16U17<17o18g19Z1:R1;H1<C1=91>41>[1?B1?C1?D1?E1?F1@`1BB1CA1D=1EA1FB1Fo1G\1HO1IG1J:1K21L]1NM1O11OU1P91P]1QM1R=1Ra1SE1T;1U61Ul1Vg1WK1Wo1XS1Y71Y81Zd1\M1^>1_l1_m1_n1`[1aH1b21b\FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp3ARB2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp13ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp3ARB2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB4rawp2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4APPA3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp4APPA3ARB2HB5Ha_st5Hl_stS4rawpS2FBS2FBS4CNTj1n3CJ0S1n2HnS2sp3sp13SP1S1R2lo3LOS3ALOS2FBS2sp3sp13SP1FSS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB4rawpS1R3HIA4PHIj4CNTj4PHIf1h1n3BUD3PJ03PF0S1n4rawpS1R3HIA1h2sp3TOP3sp13SP1S1n2HnS2FBS2FBFS2FBS1n2Hn2NES1n2HnS1A1n4rawp2RAS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBS3sp1S2spS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARB4rawpS4CNTj1n3CJ0S1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LFB2FB3sp13ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LFB2FB3sp13ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LFB2FB3sp13ARB4rawpS2FBS2LB1n2DPFS1A3ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBS1R3HIA1h2sp3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LFB2FB3sp13ARBS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LFB2FB3sp14rawp3ARBS2FBS2FBFS2FBS1R3HIA4FFRj4CNTj4FFRf1h1n1d4BUDF3FJ03FF0S1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTSS1ASS1R3HIA1hS2FBFFS2FBS3sp1S4C24c5C24c02LB1n4C24H2DPS1R4STKg4STKs4STKf2sp1A1n2bs3AAL2A02Hn2FB3sp13SPR4SP1R2F03ARBS1R4STKg4STKs4STKf2sp1A1n2bs3AAL2A02Hn2FB3sp14rawp3SPR4SP1R2F03ARB2R0S4PHIj4CNTj4PHIf1n3PJ03PF0S2FBFS2FBS2sp3sp13SP1S3sp1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSSS2sp3sp13SP1S1nS2FBFS3sp1S2FBS2spSS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A03LEN2Hn3LFB2FB3sp14rawp3ACV3SPR4SP1R2F03ARB2R03RCEFS2LB1n4rawp2DP2CCS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP11HS4FFRj4CNTj4FFRf1n1d3FJ03FF0S1A2A03ARB2K0S4rawp2R02KZS4DATA1n3Hn02xq3HxqS2FB1c2HcS1R4STKg4STKs4STKf2sp1A1n2bs3AAL2A02Hn2FB3sp14rawp3SPR4SP1R2F03ARB2R0S1R4STKg4STKs4STKf2sp1A1n2bs3AAL2A02Hn2FB3sp13SPR4SP1R2F03ARBS1R2lo3LOSS1dS2FBFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3SPRS3sp1SFSS2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP1S2FBS2sp3SPRFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBFS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13ARBS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2FB2F0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13SP13ALO2F14FBLO3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13SP13ALO2F14FBLO3ARB4rawp2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp13SP13ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp13SP14rawp3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3ALO2F14FBLO3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3ALO2F14FBLO3ARB4rawp2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB4rawp2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARBFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp13SPR4SP1R2F03ARBS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp3SPR4SP1R2F03ARB2R0S1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB2FB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB2FB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3ALO3ARB2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp3ALO3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB4rawp2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp3ARB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB3ARBFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB2FB3ARB2h23HT23HS24HTc'2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB3ARB2h23HT23HS24HTc'2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB2FB4rawp3ARB2h23HT23HS24HTc'2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB4rawp3ARB2h23HT23HS24HTc'2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2F03ARB2HBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2F03ARB2HBS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB3ARB2HBS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB3ARB2HB". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c C24c0 GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI AMC CALLOC CINFO ALGNULL MDALG GETINT NEXTLEN NA0 NB0 NRT AAL A0 CWA ASTK AOD HBY LEN Hn CRD DLO DA D47 SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_973c8 :
    si_P SI m ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    forall ms, S1P ms -> aevtA asegs (KF asegs R HIA h mo0) POST ms.
  Proof.
    intros SIP BUD BUDF UW ms HS1.
    ddestruct HS1 as (FB & sp1 & h1 & m1 & x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & w0 & w1 & w2 & fj32 & fj64 & fj96 & fj128 & fj144
                    & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & G4 & G8 & G12 & G16 & G18 & G22 & FSH
                    & SAVE & SLOT & ST48 & SThi & STlo & MI1 & P7Z1 & HB1 & OA1 & OD1 & APPA & APD & PRES0 & SS1).
    subst ms. intros moc [HKc MFc].
    rt_facts. unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *.
    pose proof (hm_top asegs R HIA h1 _ _ m1 HH1) as HT. rewrite Ehtop, Estk in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKg0 STKs0 STKf0 TOP HT; lia]).
    ddestruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof (art_stk_high asegs R HIA) as STKH.
    unfold pkcs7_zero in P7Z1. pose proof (rw_cells_bound _ _ _ _ P7Z1) as ARB. cbn [cells_size csize Nat.add length] in ARB.
    clear HB1.
    (* [comment removed for export] *)
    assert (PRES : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m1).
    { ddestruct PRES0 as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact I]. }
    assert (SIP1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PRES0))| intros a Ha; exact I]. }
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (CWA1 : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA h1) A 1440).
    { rewrite Ehtop. eapply client_wrange_mono; [exact CWA| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (CRDs : client_range L (LB ++ fdata LF) (bv_unsigned sp) DATA n) by (eapply client_range_sep; [exact CRD| intros b Hb; exact Hb| exact DLO]).
    assert (CRD1 : client_range L (LB ++ fdata ((FB, 256) :: LF)) sp1 DATA n).
    { apply (client_range_sp_mono L _ (bv_unsigned sp) sp1); [clear - SP1; lia|]. eapply client_range_incl; [exact CRDs| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (CRA1 : forall SPq, client_range L (LB ++ fdata ((FB, 256) :: LF)) SPq A 1440).
    { intros SPq. apply (client_range_lower L _ lo SPq A 1440); [| exact ALO1]. exact (client_range_of_w L _ _ _ _ _ CWA1). }
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES0)| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKg0 STKs0 STKf0; lia]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    clear PRES0.
    pose proof (CNTg_mono 0 n ltac:(clear - Hn; lia)) as CG0. pose proof (CNTs_mono 0 n ltac:(clear - Hn; lia)) as CS0'.
    ddestruct (A_pkcs7_parse_C24.joint_0 PHIj FFRj CNTj PHIj_mono FFRj_mono CNTj_mono n ltac:(clear - Hn; lia)) as (PJ0 & FJ0' & CJ0). pose proof (FJ0' (d + 1)) as FJ0. clear FJ0'.   (* [comment removed for export] *)
    pose proof (PHIg_mono 0 n ltac:(clear - Hn; lia)) as PG0. pose proof (FFRg_mono 0 n (d + 1) ltac:(clear - Hn; lia)) as FG0.
    pose proof (PHIs_mono 0 n ltac:(clear - Hn; lia)) as PS0. pose proof (FFRs_mono 0 n (d + 1) ltac:(clear - Hn; lia)) as FS0.
    pose proof (PHIf_mono 0 (CNTp n) ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as PF0.
    pose proof (FFRf_mono 0 (CNTp n) 0 ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as FF0.
    apply (aevtA_enter asegs (KF asegs R HIA h1 moc) _ _ _ (conj (proj2 (HKI moc) HKc) (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 moc) as KINV.
    (* [comment removed for export] *)
    zstep. try (if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - A0 ARB; lia); clear - K0 A0 ARB; lia|]; clear K0).
    idtac "M-1".
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    lazymatch goal with HH : HM _ _ _ h1 LB _ ?mx |- context [MS _ _ _ _ _ ?mx _] => rename HH into HH1c end.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc asegs R HIA) with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (cnt := 1) (sz := n) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH1c | exact HK1 | exact LOS | exact TPV | reflexivity
              | lazymatch goal with
                | |- stk _ _ lo _ => assumption
                | |- mem_inv _ _ => assumption
                | |- lo <= sp1 - arl_need_malloc R => pose proof (arl_need_rt_malloc R); clear - SLO SP1 NS1 H STKg0 STKs0 STKf0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite Ehtop; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 <= 1 => clear; lia
                | |- 0 <= n => clear - Hn; lia
                | |- 1 * n < AMAX => unfold AMAX; clear - Hn; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => rewrite Evol; unfold A_pkcs7_parse_C.PHIp in BUD; clear - BUD PJ0 PF0 Hn; lia
                | |- uwc _ _ _ _ _ _ _ => rewrite Estk; exact UW1
                | |- hfr _ _ _ _ + _ <= FR_MAX => rewrite Efr; unfold A_pkcs7_parse_C.FFRp in BUDF; clear - BUDF FJ0 FF0; lia
                end
              | (intros _; cbn [app]; blk_norm_goal; pose proof (Z.div_pos n 5889 ltac:(clear - Hn; lia) ltac:(clear; lia)) as DP; clear - C24H C24c0 DP; lia)   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2' & mo2 & E2 & PO). injection E2 as Ems Emo. subst ms2' mo2x.
    unfold call_postA in PO. cbv beta in PO.
    ddestruct PO as (u0 & u1 & u2 & r & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & Ems2 & MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
    subst ms2.
    rewrite ?(unsigned_lit sp1) in ST2 by exact SP1R. rewrite ?(unsigned_lit sp1) in HP2 by exact SP1R.
    replace (ret_pc (Z_to_bv 64 0x97920)) with (Z_to_bv 64 0x97920 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite ?Z.mul_1_l in HV2. rewrite ?Z.mul_1_l in CASES.
    rewrite Estk in HP2, HS2. rewrite Ehtop in HT2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2.
    assert (HCSc : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; apply HCS2; rewrite Ehcs; exact Hx).
    idtac "M-2".
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    apply (presA_shadow_cells_sh asegs R CS LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [] m1 m2 FB _ CSOK) in FSH;
      [| cbn [cells_size csize Nat.add length]; exact CFB | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add length]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G8; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | exact I ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| exact I].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SLOT; [| apply client_range_stack; clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in ST48; [| clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SThi; [| clear; lia| exact I].
    apply (presA_sshad asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SS1; [| exact SLOS| clear - HT TOP; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in P7Z1; [| cbn [cells_size csize Nat.add length]; exact (CRA1 sp1)| exact I].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ m1 m2 A 1440 CSOK HP2) in OA1; [| intros xq Hxq; eapply hcs_below_top; exact Hxq| right; split; [exact (CRA1 sp1)| clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia]].
    assert (ODn : aobj asegs AL CS m2 DATA n).
    { destruct (Z.lt_ge_cases n 1) as [Hn0|Hn1].
      - split; intros xq Hxq; exfalso; clear - Hxq Hn0; lia.
      - eapply presA_aobj0; [exact CSOK| exact HP2| exact (OD1 Hn1)| intros xq Hxq; eapply hcs_below_top; exact Hxq|].
        right. split; [exact CRD1| clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia]. }
    clear OD1.
    assert (PRES' : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m2).
    { eapply (presW_call asegs R HIA h LB LF _ _ X0 m m1 m2); [exact PRES| exact HP2| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear - SP1; lia| clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia| intros x Hx; exact I]. }
    clear PRES. rename PRES' into PRES.
    assert (SIP2 : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIP1| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| intros a Ha; exact I]. }
    clear SIP1 MI1 STlo HP2 HH1c UW1 LAWS KINV.
    (* [comment removed for export] *)
    carve_frame 32%nat ST48.
    lazymatch goal with FRx : rw_cells _ m2 (sp1 + 16) [CB 32 ?jr] |- _ =>
      apply (rw_cells_split_CB asegs m2 (sp1 + 16) [] 32 jr [] [8; 8; 16]%nat) in FRx; [| reflexivity]; cbn [mk_CB_cells app] in FRx;
      cb8_to_c8 FRx (@nil cell);
      lazymatch type of FRx with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FRx [c1] end;
      rename FRx into RSL end.
    destruct (stk_split asegs m2 (sp1 + 56) (sp1 + 88) (bv_unsigned sp + -104) SThi ltac:(clear - SP1; lia)) as [STmid STb]. clear SThi.
    destruct (stk_carve asegs m2 (sp1 + 56) (sp1 + 88) 32 STmid ltac:(clear; lia)) as [_ [jup UP]]. clear STmid.
    replace (sp1 + 88 - Z.of_nat 32) with (sp1 + 56) in UP by (clear; lia).
    apply (rw_cells_split_CB asegs m2 (sp1 + 56) [] 32 jup [] [24; 8]%nat) in UP; [| reflexivity]. cbn [mk_CB_cells app] in UP.
    lazymatch type of UP with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 UP [c1] end.
    chunk_join RSL SLOT RSL1. chunk_join RSL1 UP RSL.
    rename ST48 into STa.
    (* [comment removed for export] *)
    assert (CELLS : rw_cells asegs m2 A CSZ).
    { eapply rw_cells_reshape; [exact P7Z1| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
    clear P7Z1. unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    (* [comment removed for export] *)
    cb8_to_c8 G18 (@nil cell).
    (* [comment removed for export] *)
    pose proof (mo_frame_trans _ _ _ MFc (mo_frame_trans _ _ _ MF1 MF2)) as MFc2. clear MFc MF1 MF2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo2) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc.
    pose proof (crange_mono _ _ _ _ HCSc CFB) as CFBc. pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc. pose proof (crange_mono _ _ _ _ HCSc SCS0) as SCS03c.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OA1) as OBJc.
    pose proof OA1 as CRA; apply aobj_crange in CRA.
    idtac "M-3".
    destruct CASES as [[Er HH2] | (rawp & Er & RAL & RFR' & RSTK & HH2 & RAWZ)]; subst r.
    - (* [comment removed for export] *)
      pose proof (hm_top asegs R HIA h2 _ _ m2 HH2) as HTc'.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. try (if_cases KZ; zify_cond KZ; [| exfalso; clear - KZ; cbn in KZ; lia]).
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      idtac "M-4".
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with CE : rw_cells _ mx A _ |- _ =>
        assert (PZ : pkcs7_zero asegs mx A) by (unfold pkcs7_zero; eapply rw_cells_reshape; [exact CE| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity]);
        clear CE; pose proof PZ as CE; unfold pkcs7_zero in CE end end.
      dv_shapes. si_now.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
        assert (TP0 : tailP X0 (2 * n + AVOL_CALL) (fr_charge (d + 1)) [] mx None) end.
      { split. { cbn [pkcs7_at]. split; [assumption|]. split; [exact AAL|]. split; [exact A0|]. unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *. clear - ARB. lia. }
        split; [exact I|]. cbn [length]. change (Z.of_nat 0) with 0.
        split; [unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia|].
        split. { unfold A_pkcs7_parse_C.PHIp. clear - PJ0 PF0 Hn. lia. }
        split. { unfold A_pkcs7_parse_C.FFRp. clear - FJ0 FF0 Hn. lia. }
        split; [intros xq Hx; exact (proj1 (proj1 (outside_app _ _ xq) Hx))|]. split; [intros xq Hx; exact Hx|]. exact (conj BUD BUDF). }
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc2 MF9) as MF9'.
      eapply (tail_9755c R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := X0) (PHIa := 2 * n + AVOL_CALL) (FFRa := fr_charge (d + 1)) (Lc := @nil blk) (hc := h2)
                                    (st := None) (r := -22400);
        first [ exact BUD | exact BUDF | exact TP0
              | lazymatch goal with
                | |- _ <= -22400 < _ => clear; lia
                | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                    cbv delta [A_pkcs7_parse_C24.dvA] beta;
                    split; [cbn [app]; eassumption|]; split; [exact HK9|]; split; [exact MF9'|];
                    split; [exact HT2|]; split; [exact HS2|]; split; [exact HF2|]; split; [exact HCSc|]; split; [exact HV2|]; split; [exact HFR2|];
                    split; [exact PRES|]; split; [eassumption|];
                    repeat match goal with |- _ /\ _ => split end;
                    first [ eassumption | reflexivity
                          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA0-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "T97250-LEFT:" g end ].
    - (* [comment removed for export] *)
      pose proof RFR' as RF. ddestruct RF as (R0 & R1 & R2 & R3).
      (* [comment removed for export] *)
      lazymatch type of HH2 with HM _ _ _ _ ?LBh ?LFh _ => set (LB2 := LBh) in *; set (LF2 := LFh) in * end.
      pose proof (hm_top asegs R HIA h2 _ _ m2 HH2) as HTc'.
      assert (RIN : In (rawp, n) LB2) by (subst LB2; left; reflexivity).
      pose proof (blocks_below_hm R HIA h2 _ _ m2 LB2 HH2 ltac:(intros b Hb; exact Hb)) as BBc.
      assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
      assert (RA0 : n = 0 \/ (rawp + n <= A \/ A + 1440 <= rawp)).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right].
        eapply (fresh_apart_client R LB _ lo A 1440 rawp n RFR'); [exact (CRA1 lo)| clear; lia| clear - NE Hn; lia| clear - ALO LOS; lia]. }
      assert (SEP : n = 0 \/ rawp + n <= DATA \/ DATA + n <= rawp).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0|].
        eapply (fresh_apart_client0 R LB _ lo DATA n rawp n RFR'); [| clear - Hn; lia| clear - NE Hn; lia| clear - ALO LOS; lia].
        subst LF2. eapply client_range_incl; [exact CRD| intros b Hb; apply fdata_cons_sub; exact Hb]. }
      assert (RFR : fresh_apart R LB LF rawp n).
      { split; [exact R0|]. split; [exact R1|]. split; [exact R2|]. intros B j Hb. apply R3. subst LF2. apply fdata_cons_sub. exact Hb. }
      (* [comment removed for export] *)
      assert (CWA2 : client_wrange L (LB2 ++ fdata LF2) lo (htop asegs R HIA h2) A 1440).
      { subst LB2 LF2. rewrite HT2, <- Ehtop. eapply client_wrange_mono; [exact CWA1|].
        intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
      (* [comment removed for export] *)
      assert (INH2 : @In blk (FB, 24) (@app blk LB2 (fdata LF2))).
      { subst LB2 LF2. apply in_app_iff in INH. apply in_or_app. destruct INH as [Hx|Hx]; [left; right; exact Hx| right; exact Hx]. }
      assert (IND2 : @In blk (FB + 32, 256 - 40) (@app blk LB2 (fdata LF2))).
      { subst LB2 LF2. apply in_app_iff in IND. apply in_or_app. destruct IND as [Hx|Hx]; [left; right; exact Hx| right; exact Hx]. }
      pose proof (fresh_apart_grow R HIA h2 [(rawp, n)] LB LF m2 FB 256 FRSH HH2) as FRSH2. change (fresh_apart R LB2 LF FB 256) in FRSH2.
      pose proof (presW_init_at R HIA h2 _ _ LB2 LF m2 (bv_unsigned sp) (bv_unsigned sp) X0 h HH2
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; subst LF2; right; exact Hfb) HCSc HS2 ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
      assert (WL2 : wlow R LB2 LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]).
      assert (WCA2 : wcover R LB2 LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
      destruct (hm_apart asegs R HIA h2 _ _ _ HH2) as [_ BA].
      pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA RIN ltac:(subst LF2; left; reflexivity)) as APRF. cbn [fst snd] in APRF. clear BA.
      pose proof (conj RAWZ I) as RAWZbox. clear RAWZ.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      idtac "M-5".
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear - R0 RCE ACV; lia); clear - KZ R0; lia|]. clear KZ.
      (* [comment removed for export] *)
      dv_shapes. si_now.
      lazymatch goal with P2 : presW _ _ _ h2 _ LF _ _ X0 m2 ?mx |- context [MS _ _ _ _ _ ?mx _] => rawb_via P2 RAWZbox RIN RA0 | _ => idtac "M: no PRES2 at 970f8" end.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc2 MF9) as MF9'.
      subst LB2 LF2.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
      eapply (from_97404 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := 2 * n + AVOL_CALL) (FFRa := fr_charge (d + 1)) (hc := h2) (rawp := rawp)
                                  (rt := Z_to_bv 64 0) (p0 := Z_to_bv 64 0) (w8 := Z_to_bv 64 0) (ver := Z_to_bv 64 0) (vp := Z_to_bv 64 0) (dtg := Z_to_bv 64 0) (dpad := Z_to_bv 64 0)
                                  (dlen := 0) (dq := 0) (j56 := zeros 8) (q2 := zeros 8) (q3 := zeros 8) (sj0 := sjZ);
        first [ exact RP | exact RA0 | exact SEP | exact RFR | exact BUD | exact BUDF | exact UW
              | lazymatch goal with
                | |- 0 < rawp => exact R0
                | |- 1 <= n -> aobj _ _ _ _ DATA n => intros _; assumption
                | |- 2 * n + AVOL_CALL <= _ => clear; lia
                | |- fr_charge (d + 1) <= _ => clear; lia
                | |- rw_cells _ _ rawp _ => eassumption
                | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                    cbv delta [A_pkcs7_parse_C24.dvA] beta;
                    split; [cbn [app]; eassumption|]; split; [exact HK9|]; split; [exact MF9'|];
                    split; [exact HT2|]; split; [exact HS2|]; split; [exact HF2|]; split; [exact HCSc|]; split; [exact HV2|]; split; [exact HFR2|];
                    split; [eassumption|]; split; [eassumption|];
                    repeat match goal with |- _ /\ _ => split end;
                    first [ eassumption | reflexivity
                          | lazymatch goal with |- rw_cells _ mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA1-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "F970F8-LEFT:" g end ]
      end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG UARG SM2 NS1 DIMG HMND GETTAG PHIg FFRg CNTg C24c0 GETCERTS PHIs FFRs CNTs GETSIGNERS PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI AMC CALLOC CINFO ALGNULL MDALG GETINT NEXTLEN NA0 NB0 NRT"] Theorem A_pkcs7_parse_der_spec24 :
    pkcs7_parse_der_stmtA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) SI
      (PHIp PHIj CNTj PHIf) (FFRp FFRj CNTj FFRf) (CNTp CNTj) STKp C24c A_PKCS7_PARSE_DER.
  Proof.
    intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo A DATA n lo slo d bs.
    intros HH HK0 P7Z AAL A0 OA CWA ASTK AOD HBY LEN Hn HD CRD OD DLO D47 DA ST SS SLOS SLOL SLO TOP SPA SPH MI TPV SIP BUD UW BUDF C24H LFB -> -> ->.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (pro_walk R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (lo := lo) (slo := slo) (bs := bs);
        first [ exact HH | exact P7Z | exact CWA | exact HBY | exact CRD | exact SLO | exact ST | exact SS | exact OA | exact OD | eassumption | match goal with |- ?g => idtac "PW-LEFT:" g end ]. }
    intros ms1 HS1.
    eapply from_973c8 with (DATA := DATA) (bs := bs);
      first [ exact P7Z | exact CWA | exact HBY | exact CRD | exact DLO | exact D47 | exact DA | exact SLO | exact SIP | exact BUD | exact UW | exact BUDF | exact HS1 | eassumption | match goal with |- ?g => idtac "FB-LEFT:" g end ].
  Qed.
End Walk.
