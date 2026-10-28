(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int
     A_asn1_get_alg_null_A A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_top24 A_pkcs7_getcerts_stmt24 A_pkcs7_parse_A A_pkcs7_parse_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24 A_pkcs7_parse_F24.
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
Local Ltac zchk_new ::= constr:([622160; 622164; 622168; 622172; 622176]).
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
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.54000007S1R3NA0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.11000000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L53822987428.11300000MS2LF2sp1A1n2bs3LFB3bs42Hl1B1H". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma le4_le_bytes_to_word : forall bs4, length bs4 = 4%nat -> le4 (le_bytes_to_word bs4) = bs4.
  Proof.
    intros bs4 Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
    pose proof (PropExec.bytes_le_to_Z_bound bs4) as B. rewrite Hl in B. pose proof (PropExec.bytes_le_to_Z_nonneg bs4).
    rewrite Z.mod_small by (cbn in B; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma rw_cells_CB4_C4 : forall mX B pre bs4 post,
    rw_cells asegs mX B (pre ++ CB 4 bs4 :: post) -> rw_cells asegs mX B (pre ++ C4 (le_bytes_to_word bs4) :: post).
  Proof.
    intros mX B pre bs4 post [[Hwf Hb] Hw].
    apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
    split; [split|].
    - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
    - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_le_bytes_to_word by exact H2. exact Hb.
    - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L11158032613.120L25876784085.20 L29784460045.120L39348729613.120L45146172909.12000000L00n01E01^02ES2LF2sp1A1n2bs3LFB1B1k2H02HkS1B1k2r02HB2Hk1a2Ha1q1r1H2H02q02H4S2LF2sp1A1n2bs3LFB1B2H0S1R2LF2sp1A1n2bs3LFB1B2H0S2LF2sp1A1n2bs2A02Hn3LFB1B1k2H02Hk1a2Ha". (* [comment removed for export] *)
  #[using="LF sp A n bs A0 Hn LFB"] Lemma aobj_partial : forall (CS : Z -> Prop) mX B k,
    rw_cells asegs mX (Z.shiftr B 3 + al_sb AL) [C1 (Z_to_bv 8 k)] -> B mod 8 = 0 -> 0 <= B -> 1 <= k <= 7 ->
    crange CS B k -> aobj asegs AL CS mX B k.
  Proof.
    intros CS mX B k H HB H0 Hk HC. split; [exact HC|]. intros a Ha. exists (Z_to_bv 8 k). split.
    - rewrite (shadow_of_granule AL a B HB ltac:(lia)).
      replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
      destruct H as [[_ HB'] _]. cbn [cells_bytes cbytes app] in HB'. exact HB'.
    - right. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
      clear - Ha HB Hk. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11447730091.41L40228640085.0 000015016S1x1c1e2r33Hce3Hxe1q1r2r11H2H02q02r02H42H52q12r22H93H102q23H142q33H19S". (* [comment removed for export] *)
  #[using="Type"] Lemma addw_err : forall x M c e, M = Z.ones 64 -> (c - e) mod 2^32 = 0 -> -2^31 <= x + e < 2^31 -> -2^63 <= x < 2^63 ->
    (Z_to_bv 64 (bv_swrap 32 (Z.land x M + c)) : word) = Z_to_bv 64 (x + e).
  Proof.
    intros x M c e HM Hce Hxe Hx. subst M. apply bv_eq. rewrite Z.land_ones by (clear; lia).
    rewrite ?Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (2 ^ 64) with 18446744073709551616.
    clear - Hce Hxe Hx. Z.div_mod_to_equations. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
          first [ exact (TPX _ _ REPx SM0) | exact (TPX _ _ REPx (SM0 _ _ _ _)) | eassumption
                | lazymatch goal with |- _ <= rr < _ => first [clear; lia | clear - Hr; lia | lia] | |- _ < rr <= _ => first [clear; lia | clear - Hr; lia | lia] end
                | lazymatch goal with |- HK _ _ _ _ _ => lazymatch goal with HKI : forall mo, HK _ _ _ _ mo <-> HK _ _ _ _ mo |- _ => apply (proj2 (HKI _)); assumption end end
                | (cbv beta; dvA_build) ]
        end
      end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00d0@L1685717371.0   L24023900370.0  L27817441514.283L28582457040.184L29023151364.265L3302530858.2   L35666023782.15 L40228640085.0  L42411609006.0  L43300649301.0  L45544150004.278L50790731766.15 L57124690773.0  L59308579414.10 L60098763854.6  L62989756889.184L64850595401.0  L8171953640.283 L9446677862.2   L9459597980.184 P32557674715.287P53346601986.287Q125584537.281  Q15605646235.279Q26314584654.287Q26316671538.272Q27663034012.280Q27940667404.276Q34357517860.277Q34669208222.282Q37706020980.275Q39285966488.280Q3933900710.276 Q39682685338.278Q42441548847.287Q44298944140.272Q44301027056.287Q44330035866.282Q47812103402.271Q48119910507.287Q50231601566.278Q51604307871.279Q54481541664.277Q5596578838.287 Q58744150173.281Q58972088541.284Q59867425008.287Q64228675114.286Q64681563910.287Q67140783850.271Q67893080934.275Q6912043747.284 00000100201F02102202802]02^02_02`02a03O03P03`03j04R04S04T04Z05E06L08809209l0:l0;Z0<T0>90?90@30@o0Ai0C10Ck0E40Eb0Fb0G\0HG0J<0K60L00MM0MN0NH0OB0OC0QX0SA0Sl0Th0UbSSS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp12cs2Lc3SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12Lc1r2HrFS1r2HrS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTSSSFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSSS1r2Hr2r02KZ1q1HS1R2lo3LOSS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12Lc1rSFS1r2HrS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12Lc1r2HrS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB2cs2Lc3SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp12cs2Lc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB2cs2Lc3SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp12cs2Lc3SP14SP1M3SZC3ALO3ACV3SPR2F82F02HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB2cs2Lc3SZC2HT2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB2cs2Lc3SZC2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 NA0 NB0 NRT bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS"] Lemma tail_97874 : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g8 g12 g16 g18 g22 j32 alg : list byte) (cs : list cell)
      (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte)
      Lc mc moc hc (st : option (p7_own * p7_junk)) (r : Z)
      (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s4v s5v s6v s7v s8v s9v : word),
    dvA FB sp1 W PHIa FFRa w0 w1 w2 g4 g8 g12 g16 g18 g22
        [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
         C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]
        (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80 cs Lc mc moc hc ->
    tailP W PHIa FFRa Lc mc st -> -0x80 < r <= 0 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                      s2v (Z_to_bv 64 (-8)) s4v s5v s6v s7v s8v s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97e78) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D TP Hr. cbv beta in D. dvA_open D. pose proof TP as TP0. ddestruct TP as (REP & SM & CNT & PHI & FFR & HW & HWX & BUD & BUDF).
    tail_prep.
    pose proof (presW_init_at R HIA hc _ _ (Lc ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    pose proof (conj HHc I) as HHbox. apply rw_cells_blob in CELLS. rewrite SZC in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    match goal with |- context [bv_swrap 32 (Z.land r ?M + ?c)] => assert (EQX : (Z_to_bv 64 (bv_swrap 32 (Z.land r M + c)) : word) = Z_to_bv 64 (r + -21760)) by (apply addw_err; [vm_compute; reflexivity| vm_compute; reflexivity| clear - Hr; lia| clear - Hr; lia]) end.
    rewrite EQX. clear EQX.
    zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (REPx : pkcs7_at asegs PK st mx Lc LB A);
      [ eapply (pkcs7_at_presx0 R HIA) with (bs := bs) (slo := slo) (lo := lo) (n := n) (h := h) (A := A) (sp := sp) (hq := hc) (LFq := (FB, 256) :: LF);
        first [ exact REP | exact (proj1 HHbox) | exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2)) | eassumption
              | match goal with |- ?g => idtac "REPX-LEFT:" g end ] |];
      assert (SIx : si_P SI mx);
      [ eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))| intros a _; exact I] |];
      clear SIc REP end.
    assert (TPx : forall mq, pkcs7_at asegs PK st mq Lc LB A -> tailP W PHIa FFRa Lc mq st).
    { intros mq Rq. exact (conj Rq (conj SM (conj CNT (conj PHI (conj FFR (conj HW (conj HWX (conj BUD BUDF)))))))). }
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    2:{ exfalso. change 18446744073709551615 with (Z.ones 64) in KZ. rewrite ?Z.land_ones in KZ by (clear; lia). clear - KZ Hr. Z.div_mod_to_equations. lia. }
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    eapply (tail_977a0 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := W) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lc) (hc := hc) (st := st) (r := r + -21760);
      first [ exact (TPx _ REPx) | eassumption
            | lazymatch goal with |- - 2 ^ 31 <= _ < 2 ^ 31 => clear - Hr; lia end
            | (cbv beta; dvA_build) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0810@C17025492443.375C23922862675.306C51712377427.376C60410007123.307D16071854214.307D16901939902.307D2457516971.307 D31425002750.376D32458870384.307D43080244883.283D49496112240.376D56536395888.307D57793146470.283D59521016234.283D5984197035.307 D60109446735.376D6359981838.307 D66237350158.307D67666003371.376D717153038.376  K13144954490.306K21212095580.375K21737593458.376K28356921734.375K37568386490.375K38334128250.306K39214813446.375K46975357874.307K54978542206.283K55088519473.375K63420573106.307L10370335306.1  L10439800264.4  L10596430123.1  L10762500794.4  L10894997063.3  L10912730231.1  L1107921941.339 L11333811117.3  L11879002598.1  L12266043405.1  L12963055938.3  L13141122540.2  L13176305223.2  L13340048728.1  L13387808695.1  L1386319377.337 L14693784767.193L14695814100.3  L1473795187.4   L1473795957.22  L1473796084.7   L1540877545.17  L1540877545.3   L15618147883.1  L15686577978.1  L15692518263.1  L15822417165.1  L16662351465.1  L16720171459.339L16722252861.193L16722252861.292L1685717371.0   L16896526054.1  L16944181431.1  L17064006458.1  L18010441735.2  L18013431815.1  L18023395959.1  L19769535484.2  L19769535484.3  L19959024712.1  L19980016842.7  L20166242178.3  L21007906567.2  L21218866939.2  L21311120310.1  L21452127729.1  L21644325741.3  L21654730866.2  L21737098262.3  L21866712442.1  L22490511066.9  L2254620236.6   L22706556809.3  L23179818103.1  L23792326817.0  L24023900370.0  L24054617783.1  L24128180555.1  L2424960062.2   L24817214193.2  L2514189370.1   L2545017055.272 L26016216788.4  L2621559066.1   L27650499371.1  L27817441514.278L27832536201.281L27940405558.13 L28316294259.20 L28369338896.2  L29066840183.1  L29742948851.362L29773715284.1  L29999406286.14 L30272718447.1  L31034375991.6  L31251627448.1  L31388754869.15 L31471780431.10 L31636313402.1  L31653556939.1  L31775652143.1  L31852292097.2  L31863022963.4  L3241391265.0   L32454903270.1  L32750658443.2  L32982411378.9  L32992897852.1  L33136591625.1  L33312313103.2  L33532570708.1  L33985112333.1  L34673485611.1  L34783991938.3  L35098291383.1  L35170103653.4  L35666023782.15 L36021046681.2  L36181700215.1  L36692980745.1  L36888478001.3  L3696557773.3   L37268777784.1  L37572943404.2  L37663591692.9  L37714553091.1  L37739402492.20 L37940357415.0  L38235734261.1  L38321384428.2  L38551529394.0  L38656762295.1  L38738405142.1  L38756097312.193L39188636933.0  L39219305104.2  L39686831147.1  L39834879821.3  L40228640085.0  L40253556363.2  L40281191306.3  L40419466676.1  L41099742989.1  L41251426164.1  L41409160545.3  L41659662674.1  L41661145554.2  L41663468825.293L41663468825.336L42038751126.5  L42139611770.2  L42213118647.1  L42411609006.0  L42488948659.2  L42642555220.1  L42917423353.24 L43300649301.0  L43810982283.2  L44191169096.12 L44334313263.1  L45121863851.1  L45186664561.3  L45249686572.193L45313523352.15 L46290454573.5  L46541147848.1  L46745494493.3  L46975911382.3  L47046946167.3  L47870616696.2  L47882514004.1  L48600852026.6  L49037504437.15 L49233373885.2  L49508988902.1  L50141024560.1  L5021251703.1   L50790731766.15 L50798508407.1  L51299303177.1  L51570243003.3  L52045659405.3  L52094935144.346L52275559244.193L52941874306.3  L53000928673.1  L53218759346.2  L53297529385.1  L53517061083.292L53527181501.2  L53585711905.0  L53792287453.7  L53886137103.2  L53992506107.3  L54185219523.15 L54246093652.1  L5491309809.2   L54965870984.2  L55079916376.4  L55085943702.3  L55382645031.0  L55716550157.1  L55842747208.3  L56258289710.4  L56523586534.1  L57065636066.1  L57124690773.0  L57387013391.2  L576250137.272  L576250137.293  L57781587882.346L57951117045.3  L58073846709.16 L58143913820.1  L58304396918.6  L58412049673.1  L58748427563.1  L58993384456.8  L59126280567.1  L59308586248.2  L59427880762.294L59578101107.3  L60056205954.3  L60098763854.6  L6031628760.2   L60448817524.1  L61004000883.20 L61545304294.1  L61567447895.193L61567447895.292L61603606271.2  L61747380284.1  L61970568713.1  L6198624755.2   L6203936179.1   L62275882349.3  L62413581882.1  L62665173170.9  L62680556151.1  L63084899938.1  L63373084206.4  L63420085206.3  L63557664125.2  L63613504898.3  L64038109431.1  L64513097329.3  L64526681523.2  L64850595401.0  L65526290571.2  L65693950831.1  L66151427842.16 L66298372189.2  L66556294966.15 L66572605252.10 L66845504556.4  L66845505322.23 L66845505451.7  L66925259772.280L66937595435.302L67884573201.1  L68272074258.8  L6899380056.1   L7049614941.2   L7122685215.10  L7356357495.1   L7738195705.2   L7864360625.2   L8171953640.278 L8454980662.21  L8466307646.21  L8640568525.3   L881835912.0    L9080220944.4   L9356559676.20  L9631767084.2   L9873114841.15  L9915755099.2   O10567734856.306O13236529176.375O1475481566.304 O1478916974.375 O1594840904.306 O17025492443.375O17144234034.376O21802621976.306O26328763605.375O28722692754.375O28737892366.375O30010457231.306O3078286936.304 O33647379806.306O33990841394.307O37051008023.375O39094383154.307O40095405918.306O4013719057.376 O4028702351.375 O41464052248.306O424351700.305  O44938202843.305O45969540168.306O47569608078.375O47761277330.375O47806715794.375O48233649620.375O49701823576.304O50702732434.375O51103636018.376O52633390046.374O55209884805.305O55518239188.305O56261809874.376O56414299794.375O56496609880.374O58151696734.375O59625529265.375O61464066679.307O64474006218.306O65975700241.376O67171060367.306O7902534110.304 O8258902344.306 O8604748773.306 O9243164245.375 P10761940190.376P10897630432.375P11331234058.375P12956228581.376P20181466405.375P21212095580.375P21658526154.305P24827162710.306P32557674715.284P32557674715.352P32765882668.306P34789739045.375P36881650582.374P3703319658.375 P39840699882.375P40259310636.306P41419110342.375P42034806130.376P42133856477.306P42484919333.306P43817786156.306P45193435862.304P46121612802.284P46121612802.352P47047506707.307P47876372191.305P48588551390.376P49230739482.304P52940256805.375P53346601986.284P53346601986.352P53529750042.304P5497056854.306 P60050384933.375P61592333368.283P6202460773.375 P62260666314.305P63564427226.374P63606742821.375P64519892182.304P64538971685.306P65519421996.306P66292560634.306P7750690063.283 P7854378006.375 Q10522731957.283Q10592533181.307Q11133374175.307Q125584537.278  Q12683804246.376Q15605646235.276Q15766564435.376Q16178735000.307Q17979627402.307Q18099743409.343Q19548768081.302Q19561563123.281Q19561597574.280Q19582148966.307Q21538057956.282Q21540267236.283Q21767670690.307Q21827169904.307Q23163703743.307Q23613318552.307Q24064611734.283Q24986381194.376Q25858702439.376Q26314584654.284Q26314584654.352Q26316671538.269Q26480898663.376Q27663034012.277Q27663313085.376Q27940667404.273Q27942454161.307Q2803826605.307 Q29775981542.307Q30755684130.349Q30802955094.280Q31241107584.348Q32437204119.307Q32458870384.307Q33137450695.307Q34357517860.274Q34362053984.307Q34362053984.376Q34362328320.283Q34669208222.279Q34669522109.307Q34964382778.376Q36508117400.376Q36856420847.376Q37277284943.347Q37706020980.272Q37706198064.349Q38248387216.376Q39285966488.277Q3933900710.273 Q39460178071.376Q39682685338.275Q4010030704.376 Q4067942512.376 Q41414298335.307Q42057144714.307Q42412061296.376Q42439168719.307Q42439168719.376Q42439443119.283Q42441548847.284Q42441548847.352Q43082486931.282Q44298944140.269Q44301027056.284Q44301027056.352Q44330035866.279Q47372006020.348Q47810120324.268Q47812056014.343Q48117823211.283Q48118064779.307Q48118064779.376Q48119910507.284Q48119910507.352Q48234175664.282Q48360113622.376Q4924621080.376 Q49496112240.376Q49698585326.281Q50231601566.275Q51604307871.276Q52747231024.283Q53315247896.307Q53611831399.376Q53799182759.307Q54481541664.274Q5596578838.284 Q5596578838.352 Q56389205783.376Q56530976407.307Q56536395888.307Q58744150173.278Q58972088541.281Q59581139423.282Q59619425870.343Q59865321072.283Q59865603600.307Q59865603600.376Q59867425008.284Q59867425008.352Q60746685720.307Q61755625803.347Q62190329447.307Q62384136807.307Q64228675114.283Q64228675114.351Q64681563910.284Q64681563910.352Q64683667846.283Q64683942374.307Q64683942374.376Q67134113924.268Q67463482983.376Q67893080934.272Q68073340867.343Q6912043747.281 Q7136501407.376 Q7533086823.307 Q9090756535.376 Q9356756743.284 Q9356857095.354 Q9633850233.280 Q9634015756.281 Q9644583048.307 Q9644583048.376 Q9646649006.302 00000100500900=02]05505607`09?0:m0<[0>:0?h0?i0?j0A_0C>0D]0D^0FL0HO0HP0JS0L?0Mk0On0QZ0T=0Ui0WY0Z<0ZB0ZO0ZS0ZT0ZU0ZV0]G0]H0]L0]P0]Q0]R0]Z0]_0]c0]d0^P0^Z0^d0`20`G0`d0a00a40a80a<0a@0aD0d10ek0hX0hY0h]0ha0he0hm0hn0i20i:0iB0iG0i_0i`0if0ig0ik0in0io0j00j10j50jV0jh0k10k50k60k70k;0k?0kE0kF0kJ0li0m60m;0m?0o>10]11A12A12B12F12G12K13613913L13O14E14V14Z14^14b14h15815915=15>15R15V15Z15a15e15i15m15n15o16@16e16m17117517617717:17;17a17d18c18d18h18i18j18n1911:Q1:R1:S1:W1:X1:Y1:Z1:c1:g1:k1:o1;01;11;91<X1>71>81>91>=1>>1>?1>C1>k1>l1>m1?[1?_1?c1?d1?e1@`1A21A71AB1AC1AD1AE1AI1AJ1B@1BA1BE1BH1BI1C71C;1C?1CJ1CV1CW1E=1E>1EA1EG1EK1Fj1Fk1Fl1GF1GM1GX1HP1HT1HU1HV1Hc1Hd1He1Hi1I51IE1II1IL1IM1IT1K31LR1NR1N_1OU1OX1Oo1P31P71PN1PR1PX1PY1Pb1Pc1Pm1Q51Q91R91R=1T11VX1VY1V\1V`1Va1Vf1Vg1Vk1W?1WC1WF1WV1WW1WX1WY1W]1W^1W_1W`1Wa1We1XN1XO1YE1YV1Ya1Zh1[=1\\1^;1^>1^b1^f1^n1_G1_K1_L1_M1_N1`S1aM1aX1aY1ah1bf1bm1cZ1cd1ce1cf1cg1ch1ci1cj1ck1cl1cm1cn1co1d01d11d21d31d41d51d61d71d81d91d:1d;1d<1d=1d>1d?1d@1dA1dB1dC1dD1dh1di1dj1dk1dl1dm1dn1do1e01e11e21e31e41e51e61g]1iM1k>1lo1n`1na20C22^24P26B28]2:N2=32>c2@S2Bn2D_2Ga2J92LL2Ng2Q=2Rm2T]2WE2Y[2\H2^^2`O2bf2e=2gX2in2k_2nD30f32H35236c3993;L3=g3?E3Ag3DQ3DR3Eh3G>3Hc3JO3L43N63OL3OM3Pc3RL3T53U^3U_3WD3Xi3[93\O3^b3`83`93`:3`;3af3cQ3dj3fO3h43iY3ki3mg3o>40\42C43_45F45G46]48>49i49j49k49l4;Q4<g4?44@Y4@Z4BA4Ch4EO4G44HY4JL4JM4L24MW4O<4PR4PS4R84ST4U?4Vm4Xa4ZU4\:4]S4_>4`i4bN4d54eK4fa4i;4kC4mZ50:52Z52[54K54L56157P5955:Z5<?5<@5<A5<B5>J5>K5>L5>M5>N5?d5AI5Bn5DS5DT5DU5DV5DW5DX5DY5DZ5FA5GW5Hm5KL5Mk5P?5RS5Ta5V]5Xh5Z>5Z?5[f5]<5^a5`F5`G5b75cS5e>5fW5h05iI5k15lJFS2FBS2FBS2FBS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2h34alen2ap3HT32LGS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2bs3LEN2Hn3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APRF4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC4APPA2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC2C12C22C34APRF2x23x153x163x174POSTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x143SZC2C12C22C34APRF2x23x153x163x174POSTS4rawpS1A1n4rawp2RAS2FBFFFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2p12Lw4Hp1a3HLw2p23Hp2FS2FBS2FBFFS2lo3sp1S3sp1S2FBFS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp12p12Lw2LRS2p12Lw2LRS1A1a1k2H3S1R3NS14STKg4STKs4STKf5STKg02sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS3sp13SP11a1k2H1S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2sp3sp13SP1S2sp3sp13SP1S2FBS2FBS2FBS2FBS2FBS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P4END22RP2C12C33ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2p12Lw2LR4Hp1a3HLwSS2FBS2FBS2FBS2r23Hr2FS2FBS1n4rawpS1n4rawpS3sp1S1R3HIA1h2sp3TOP3sp13SP1FS1n2HnFS2FBS1AFFFS2FBS4rawp1P4END22C12p12Lw3Hp12p23Hp2S1A2lo4ALO11a1k2H2S1A2xq2HxS2FBSSS2FBS2FBS1n2HnFS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1A1n4rawp2RAS3sp1S2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1FS2FBFS2FBS1R4STKg4STKs4STKf2sp1A2lo4ASTK3SLO3LOS3SPRS1AS1R3HIA1h2sp3TOP2HTS1AS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S2r23Hr21r2KA1q1HS2FBS2FBS2FBS1n2HnS2sp3SPH3sp13SP1SS2FBFS1R2lo3LOS2FB3ALO2F1S2FBS2FBS2FB2F0S2FBS2FBS2FBFFS4rawp2RP2ap4Hap1S1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS2LF3LFBS2FBS2FBFFS1AFS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmS1AS1R1n2lo3LOS4rawp4END22C33ALO3RCE2p12Lw3HLw2p24alen2ap3Hp24Hap2SS2loFSS2FBS1AS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2RP2C13SPR2F04SP1R2p14Hp1aSFS2FBFSFS1R3HIA1hS2FBS2FBS2FBFFS2r13Hr1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFS2FBSFS2FBS1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9SFS1n4rawp4END22C32p12Lw3HLw2p24alen2ap3Hp24Hap2S2FBS2FBFFS1n2FB4rawp4END22C34APRF2p12Lw3HLw2p24alen2ap3Hp24Hap14Hap2S1R1n4rawp3ACV3RCES3sp1S2sp2lo3sp1FFFS2FBFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1FS2FBS1AFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS2FBS2FBS1A2FB4APPAS2sp3sp13SP1FS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2RP2C13SPR2F04SP1R2p12Lw2LR4Hp1aFS1AS1A2A0S2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFSS1n4rawp4END22C32p12Lw3HLwS2FB2F0S1A2FB4APPAS1R1n4rawp4END22C33ACV3RCE2p12Lw3HLw2p24alen2ap3Hp24Hap2S2FBFFS1R2FB3ACV2F1FSS2FBS4CNTj1n3CJ0S1n2FB4rawp4APRFS2FBS1ASS2FB2F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEst5CM8st2x22HxS4CNTj1n4CNT1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S1AS4rawp1P4END22C12p13Hp1S2FBS2FBS4END22p12Lw3HLw2p23Hp2S2FBS1i2HiFS2FB1c2HcFS1R2lo3LOSS2sp3sp1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2FBS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P4END22RP2C12C33ACV3SPR2F04SP1R3RCE2p13Hp14Hp1aS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2p13Hp14Hp1aFS1AS2FBFS3sp1FS2FBS1R2lo3LOS2FB3ALO2F1S2FBS1AS1n2FB4rawp4APRFFFFS2FBFFSFS2FBS2FB2r03F641q1r1H2H02q02H43sp14SP1M1A3AALFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S2r13Hr11r2KT1q1HS2FB1a1k2H3S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F11a1k2H1S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1AS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2FBS2lo3sp1S1R1n2lo3LOS4rawp3ALO3RCES2FBFFFS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCES1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOS1A2lo4ALO1SS2sp2lo3sp13SP1S1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2FB2F0S1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1S4alen3ALRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp13g164rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C12C33ALO3RCE2p13Hp14Hp1a4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPA2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F14alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs2Hn3LFB2FB3g164rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RA2C12C34APPA4APRF2p12Lw3Hp12LR4Hp1a3HLw2p24alen2ap4Hap14Hap23EQ22LG4ALENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APRF2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APRF2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2C12C22C33ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp13g164rawp4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C33ALO3RCE2p12Lw3HLw2p24alen2ap4Hap23EQ22LG4ALENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n3slo2bs2Hn4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2F12HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F14alen2ap2LGS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F14alen2ap2LGS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F14alen2ap2LGFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0FS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02HBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_st5SAEstS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4alen2ap2LGS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2HB5Ha_st5Hl_st5SAEstFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC4alen2ap2LGFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stFFFFFFFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F04SP1R2HB5Ha_st5Hl_st5SAEstS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F04SP1R2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_st5SAEstS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4alen2ap2LGFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp13g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R4alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3g164rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F04alen2ap2LGS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI CINFO ALGNULL MDALG NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_97828 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g12 g16 g18 g22 j32 alg : list byte)
      (rawp P END2 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 P)) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P -> P <= END2 -> END2 <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 A) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97e1c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA C1 C2 C3 BPHI BFFR BUD BUDF UW.
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
    assert (SM0 : p7small (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                                 P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs))).
    { cbn. clear - Hn. lia. }
    assert (SM0' : forall tg' pd' dl' dq', p7small (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                                 P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells tg' pd' dl' dq' ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs))).
    { intros. cbn. clear - Hn. lia. }
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    cb8_to_c8 G4 (@nil cell).
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (conj RAWB I) as RAWBbox. clear RAWB.
    zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 64) 1%nat as OPP. frame_aobj FSH (FB + 32) 1%nat as OL4.
    rawb_now.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    lazymatch goal with G4x : rw_cells _ _ (FB + 32) [C8 ?lw] |- _ =>
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := FB + 64) (LENP := FB + 32) (P := P) (END := END2) (BUF := rawp) (bs := bs) (tag := 49) (lo := lo) (lenv := lw);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact OL4 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | exact C1 | exact C2 | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 64) _ => eassumption
                 | |- rw_cells _ _ (FB + 32) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp _ |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- END2 <= rawp + _ => rewrite LEN; exact C3
                 | |- rawp + _ < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                 | |- FB + 64 + 8 <= FB + 32 \/ _ => right; clear; lia
                 | |- _ = 0 \/ FB + 64 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- _ = 0 \/ FB + 32 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                 | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- (FB + 32) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < FB + 64 => clear - F0; lia
                 | |- 0 < FB + 32 => clear - F0; lia
                 | |- 0 < rawp => exact RP
                 | |- lo <= sp1 - 16 => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- FB + 64 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- FB + 32 + 8 <= sp1 - 16 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 | |- _ = 0 \/ rawp + _ <= sp1 - 16 \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                 end
               | match goal with |- ?g => idtac "GTS-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GTS-LEFT:" g end.
    clear GT' ABc OPP OL4.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into Hr1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : P <= ?pp <= END2 |- _ => rename H into Hp1; rename pp into p1 end.
    lazymatch goal with H : rw_cells _ _ (FB + 32) [C8 ?lw] |- _ => rename lw into Lw end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    { (* [comment removed for export] *) exitG (tail_97874) r1 TPX SM0 HKc MFc Hr1 RP. }
    assert (R10 : r1 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KT. rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr1. Z.div_mod_to_equations. lia. }
    subst r1. destruct (HOK1 eq_refl) as [Hp1a HLw]. clear HOK1 KT Hr1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    splitat CELLS 6%nat CALG. splitat CALG 4%nat CT.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m2 end.
    lazymatch goal with HH : HM _ _ _ hc _ _ m2 |- _ => rename HH into HH2 end.
    lazymatch goal with MI : mem_inv _ m2 |- _ => rename MI into MI2 end.
    lazymatch goal with SS : sshad _ _ m2 slo (bv_unsigned sp) |- _ => rename SS into SS2x | _ => idtac "no SS2" end.
    lazymatch goal with ST : stk _ m2 lo sp1 |- _ => rename ST into ST2x | _ => idtac "no ST2" end.
    try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end.
    rawb_now. lazymatch goal with RB : rw_cells _ m2 rawp _ |- _ => rename RB into RAWB2 end.
    lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) m2 A 1440 |- _ => rename OB into OBJ2 | _ => idtac "no OBJ2" end.
    frame_aobj FSH (FB + 64) 1%nat as OPP.
    assert (CWP : client_wrange L (LB2 ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) (FB + 64) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    destruct (sshad_split asegs AL m2 slo sp1 (bv_unsigned sp) SS2x ltac:(clear - SP1 SLO SLOL NS1 STKg0 STKs0 STKf0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi]. clear SS2x.
    pose proof ALGNULL as AN'. unfold asn1_get_alg_null_stmtA, A_ASN1_GET_ALG_NULL_G in AN'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply AN' with (h := hc) (LB := LB2) (LF := (FB, 256) :: LF) (PP := FB + 64) (ALG := A + 32) (P := p1) (END := p1 + bv_unsigned Lw) (BUF := rawp) (bs := bs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold ASN1_GET_ALG_NULL_STACK_A;
        first [ exact HH2 | exact OPP | exact CWP | exact ST2x | exact SSlo | exact SLOS | exact SLOL | exact MI2 | exact TPV | exact NA0 | exact NS1 | exact RP | reflexivity
              | lazymatch goal with
                | |- (length _ < 512)%nat => cbn [length]; clear - LFB; lia
                | |- rw_cells _ m2 (FB + 64) _ => eassumption
                | |- rw_cells _ m2 (A + 32) _ => exact CALG
                | |- bytes_at _ m2 rawp bs => exact (cb_bytes_at _ _ _ _ RAWB2)
                | |- rawp <= p1 => clear - Hp1 C1; lia
                | |- p1 <= p1 + _ => clear - LR; lia
                | |- p1 + _ <= rawp + Z.of_nat (length bs) => rewrite LEN; clear - HLw C3; lia
                | |- rawp + Z.of_nat (length bs) < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                | |- FB + 64 + 8 <= A + 32 \/ _ => clear - APPA; lia
                | |- _ = 0 \/ FB + 64 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                | |- _ = 0 \/ A + 32 + 24 <= rawp \/ _ => right; rewrite LEN; clear - RA; lia
                | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- (A + 32) mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                | |- 0 < FB + 64 /\ _ => split; [clear - F0; lia| clear - F1 ACV; lia]
                | |- 0 < A + 32 /\ _ => split; [clear - A0; lia| clear - ASTK LOS SLO SPR; lia]
                | |- lo <= sp1 - 4208 => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                | |- lo <= sp1 - 304 - arl_need_amem R => clear - SLO SP1 NS1 NB0 NA0 NRT STKg0 STKs0 STKf0; lia
                | |- lo <= sp1 - 112 - arl_need_smalloc R => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- FB + 64 + 8 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                | |- A + 32 + 24 <= lo \/ _ => left; clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                | |- _ = 0 \/ rawp + _ <= lo \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS; lia
                | |- client_range _ _ _ (FB + 64) _ => eapply client_range_block; [exact IND| clear; lia| clear; lia]
                | |- client_range _ _ _ (A + 32) _ => eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- client_range _ _ _ rawp _ => rewrite LEN; eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (A + 32) _ => eapply client_wrange_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- aobj _ _ _ m2 (A + 32) _ => eapply aobj_sub; [exact OBJ2| clear; lia| clear; lia]
                | |- aobj _ _ _ m2 rawp _ => rewrite LEN; eassumption
                | |- _ = Z_to_bv 64 (p1 + bv_unsigned Lw) => first [reflexivity | symmetry; apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | match goal with |- ?g => idtac "A1-FORM:" g end]
                end
              | match goal with |- ?g => idtac "ALGN-PRE-LEFT:" g end ]. }
    cbv beta. intros ms3 PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & h3 & r2 & p2 & atag & apad & alen & apw
                    & -> & HH3 & Ecs & Etop & Estk & Eflag & Evol & Efr & HKiff & HP3 & MI3 & ST3 & SS3 & Ea0 & Hr2 & FPP3 & CALG3 & Hp2 & HOK2).
    subst ua0. clear AN'.
    replace (ret_pc (Z_to_bv 64 0x97e74)) with (Z_to_bv 64 0x97e74 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in HP3, ST3, SS3 by exact SP1R. rewrite HSc in HP3.
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m3).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (HP3w : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) ((FB + 64, FB + 64 + 8) :: [(A + 32, A + 32 + 24)]) m2 m3).
      { subst LB2. eapply presA_weaken; [exact HP3| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros xq Hx; exact Hx]. }
      pose proof (presA_drop_fresh_gen R LB LF sp1 sp1 (hstkhi asegs R HIA h) [(A + 32, A + 32 + 24)] FB 256 (FB + 64) (FB + 64 + 8) m2 m3 HP3w FRSH
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - F1 FBLO SP1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as HP3d.
      eapply presA_weaken; [exact HP3d| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia|].
      intros xq Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
    clear PRES.
    assert (PRES2b : presW asegs R HIA hc LB2 LF (bv_unsigned sp) (bv_unsigned sp) X0 mc m3).
    { ddestruct PRES2 as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (HP3w : presA asegs R LB2 LF sp1 sp1 (hstkhi asegs R HIA h) ((FB + 64, FB + 64 + 8) :: [(A + 32, A + 32 + 24)]) m2 m3).
      { eapply presA_weaken; [exact HP3| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros xq Hx; exact Hx]. }
      pose proof (presA_drop_fresh_gen R LB2 LF sp1 sp1 (hstkhi asegs R HIA h) [(A + 32, A + 32 + 24)] FB 256 (FB + 64) (FB + 64 + 8) m2 m3 HP3w FRSH3
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - F1 FBLO SP1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as HP3d.
      rewrite HSc.
      eapply presA_weaken; [exact HP3d| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia|].
      intros xq Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
    clear PRES2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJF : forall a k, FB <= a -> a + k <= FB + 256 -> (a + k <= FB + 64 \/ FB + 72 <= a) -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 32, A + 32 + 24)] a k).
    { intros a k H1 H2 H3. cbn. split; [clear - H3; lia|]. split; [clear - H1 H2 APPA; lia| exact I]. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 32, A + 32 + 24)] a k).
    { intros a k H1. cbn. split; [clear - H1 F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia|]. split; [clear - H1 ASTK LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| exact I]. }
    assert (DJA : forall a k, A <= a -> a + k <= A + 1440 -> (a + k <= A + 32 \/ A + 56 <= a) -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 32, A + 32 + 24)] a k).
    { intros a k H1 H2 H3. cbn. split; [clear - H1 H2 APPA; lia|]. split; [clear - H3; lia| exact I]. }
    assert (CRsub : forall a k, A <= a -> a + k <= A + 1440 -> client_range L (LB2 ++ fdata ((FB, 256) :: LF)) sp1 a k).
    { intros a k H1 H2. apply (client_range_lower L _ lo sp1 a k); [| clear - H2 ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia].
      eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| exact H1| exact H2]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) LB2 ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(FB + 64, FB + 64 + 8); (A + 32, A + 32 + 24)] m2 m3 FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    lazymatch goal with G4x : rw_cells _ m2 (FB + 32) _ |- _ =>
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in G4x; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ] end.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in STa; [| clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in SShi; [| clear; lia| clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m3 slo sp1 (bv_unsigned sp) SS3 SShi ltac:(clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia)) as SSm3. clear SS3 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in CELLS; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3) in CT; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    clear RAWB2.
    assert (OBJ3 : aobj asegs AL CS m3 A 1440).
    { eapply presA_aobj0; [exact CSOK| exact HP3| exact OBJA| intros xq Hx; eapply hcs_below_top; exact Hx| right; split; [apply CRsub; clear; lia| clear; lia]]. }
    assert (OBUF3 : aobj asegs AL (hcs asegs R HIA hc) m3 rawp n).
    { eapply presA_aobj0; [exact CSOKc| exact HP3| exact OBUF| intros xq Hx; rewrite <- HSc; eapply hcs_below_top; exact Hx| right; split; [| clear; lia]].
      eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear - Hn; lia]. }
    assert (OBJ3c : aobj asegs AL (hcs asegs R HIA hc) m3 A 1440).
    { eapply presA_aobj0; [exact CSOKc| exact HP3| exact OBJ2| intros xq Hx; rewrite <- HSc; eapply hcs_below_top; exact Hx| right; split; [apply CRsub; clear; lia| clear; lia]]. }
    clear OBJA OBJ2 OBUF ST2x SSlo MI2 HP3 HH2 OPP CWP CALG.
    try match goal with G8o : rw_cells _ m2 (FB + 64) _ |- _ => clear G8o end.
    (* [comment removed for export] *)
    assert (HT3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite Etop; exact HTc).
    assert (HS3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite Estk; exact HSc).
    assert (HF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite Eflag; exact HFc).
    assert (HCS3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros xq Hx; rewrite Ecs; exact (HCSc xq Hx)).
    assert (HV3 : havol asegs R HIA h3 <= havol asegs R HIA h + PHIa) by (rewrite Evol; exact HVc).
    assert (HFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + FFRa) by (rewrite Efr; exact HFRc).
    clear HVc HFRc.
    pose proof (bv_unsigned_in_range 64 alen) as ALR. unfold bv_modulus in ALR. cbn [Z.pow Z.of_N Pos.pow] in ALR.
    pose proof (bv_unsigned_in_range 64 apw) as APR. unfold bv_modulus in APR. cbn [Z.pow Z.of_N Pos.pow] in APR.
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA.
    2:{ (* [comment removed for export] *) exitG (tail_97874) r2 TPX SM0' HKc MFc Hr2 RP. }
    assert (R20 : r2 = 0).
    { change 18446744073709551615 with (Z.ones 64) in KA. rewrite ?Z.land_ones in KA by (clear; lia). clear - KA Hr2. Z.div_mod_to_equations. lia. }
    subst r2. ddestruct (HOK2 eq_refl) as (ap & Eapw & Hap1 & Hap2). subst apw. clear HOK2 KA Hr2.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
        zstep. zstep. zstep. exitG (tail_977a0 R HIA) (-21376) TPX SM0' HKc MFc RP RP. }
    assert (EQ2 : p2 = p1 + bv_unsigned Lw).
    { change 18446744073709551615 with (Z.ones 64) in KE. rewrite ?Z.land_ones in KE by (clear; lia).
      rewrite ?Z.mod_small in KE by (clear - Hp2 Hp1 HLw C1 C2 C3 RP RCE ACV LR; lia). exact KE. }
    clear KE.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with G16x : rw_cells _ mx (FB + 128) [CB 8 ?g] |- _ =>
        let LG := fresh "LG" in
        assert (LG : length g = 8%nat) by (destruct G16x as [[W _] _]; exact (proj1 W));
        apply (rw_cells_split_CB asegs mx (FB + 128) [] 8%nat g [] [4; 4]%nat) in G16x; [| reflexivity];
        cbn [mk_CB_cells app] in G16x;
        apply (rw_cells_CB4_C4 mx (FB + 128) []) in G16x; cbn [app] in G16x;
        splitat G16x 1%nat G16b
      end end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with FSHx : rw_cells _ mx (Z.shiftr FB 3 + al_sb AL) _ |- _ =>
        pose proof FSHx as FSc; chunk_split FSc 16%nat FSa FSb; chunk_split FSb 1%nat FS16 FSd; clear FSa FSd;
        replace (Z.shiftr FB 3 + al_sb AL + 16) with (Z.shiftr (FB + 128) 3 + al_sb AL) in FS16 by (rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - F64; Z.div_mod_to_equations; lia)
      end end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (OEXT : aobj asegs AL (hcs asegs R HIA hc) mx (FB + 128) 4);
      [ apply (aobj_partial (hcs asegs R HIA hc) mx (FB + 128) 4 FS16); [clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| clear; lia| eapply crange_sub; [exact CFBc| clear; lia| clear; lia]] |] end.
    clear FS16.
    (* [comment removed for export] *)
    lazymatch goal with CAx : rw_cells _ ?mx (A + 32) [C4 atag; C4 apad; C8 alen; C8 (Z_to_bv 64 ap)] |- _ =>
      rewrite <- (Z_to_bv_bv_unsigned alen) in CAx; change (rw_cells asegs mx (A + 32) (buf_cells atag apad (bv_unsigned alen) ap)) in CAx; rename CAx into CALG3' end.
    rawb_now.
    lazymatch goal with RB : rw_cells _ ?mx rawp [CB _ bs] |- _ =>
      destruct (bytes_at_sliceF mx rawp bs ap (bv_unsigned alen) (cb_bytes_at _ _ _ _ RB) Hap1 ltac:(clear - ALR; lia) ltac:(rewrite LEN; clear - Hap2 Hp2 HLw C3; lia)) as [ABY ALEN] end.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ h3 _ _ mx |- _ => rename HH into HH3x end end.
    pose proof MDALG as MD'. unfold oid_lookup1_stmtA, A_OID_GET_MD_ALG_G in MD'.
    lazymatch type of ABY with bytes_at _ _ _ ?xsq =>
    acallxA_sp sp1
      (rewrite <- Ecs;
       eapply MD' with (h := h3) (LB := LB2) (LF := (FB, 256) :: LF) (OID := A + 32) (EXT := FB + 128) (P := ap) (LEN := bv_unsigned alen) (lo := lo) (xs := xsq); clear MD';
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact HH3x | exact CALG3' | exact ABY | exact ALEN | exact LOS | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 128) _ => eassumption
                 | |- FB + 128 + 4 <= A + 32 \/ _ => clear - APPA; lia
                 | |- FB + 128 + 4 <= ap \/ _ => clear - APRF Hap1 Hap2 Hp2 HLw C3; lia
                 | |- (A + 32) mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                 | |- (FB + 128) mod 4 = 0 => clear - F64; Z.div_mod_to_equations; lia
                 | |- 0 < A + 32 => clear - A0; lia
                 | |- 0 < FB + 128 => clear - F0; lia
                 | |- 0 < ap => clear - Hap1 RP; lia
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- lo <= sp1 - 64 - arl_need_bcmp R => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                 | |- sp1 <= htop _ _ _ _ => rewrite HT3; clear - SP1 TOP; lia
                 | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                 | |- A + 32 + 24 <= lo \/ _ => left; clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                 | |- FB + 128 + 4 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                 | |- ap + _ <= lo \/ _ => left; clear - Hap2 Hp2 HLw C3 RCE ALO LOS; lia
                 | |- ap + _ + 8 <= 2 ^ 47 => clear - Hap2 Hp2 HLw C3 RCE ACV; lia
                 | |- client_wrange _ _ _ _ (FB + 128) 4 => eapply client_wrange_sp_mono; [exact LOS|]; rewrite HT3, <- HTc; eapply client_wrange_block; [exact IND| clear; lia| clear; lia]
                 | |- aobj _ _ _ _ (A + 32) 24 => rewrite Ecs; eapply aobj_sub; [exact OBJ3c| clear; lia| clear; lia]
                 | |- aobj _ _ _ _ ap _ => rewrite Ecs; eapply aobj_sub; [exact OBUF3| exact Hap1| clear - Hap2 Hp2 HLw C3; lia]
                 | |- aobj _ _ _ _ (FB + 128) 4 => rewrite Ecs; exact OEXT
                 end
               | match goal with |- ?g => idtac "MD-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MD-LEFT:" g end.
    try clear MD'. clear OEXT.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r4 end.
    (* [comment removed for export] *)
    zstep. if_cases KO; zify_cond KO.
    2:{ (* [comment removed for export] *)
        zstep. zstep. zstep. exitG (tail_977a0 R HIA) (-21760) TPX SM0' HKc MFc RP RP. }
    (* [comment removed for export] *)
    dv_shapes. si_now. try match goal with RBo : rw_cells _ _ rawp [CB _ bs] |- _ => clear RBo end. rawb_now.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    subst LB2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) =>
    eapply (from_978e8 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := h3) (rawp := rawp) (P := p2) (END2 := END2)
                                   (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := atag) (dpad := apad) (dlen := bv_unsigned alen) (dq := ap) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
      first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW | exact C3 | exact Hap1
            | lazymatch goal with
              | |- rawp <= p2 => clear - Hp2 Hp1 C1; lia
              | |- p2 <= END2 => clear - Hp2 HLw C2; lia
              | |- 0 <= bv_unsigned alen => clear - ALR; lia
              | |- ap + bv_unsigned alen <= rawp + n => clear - Hap2 Hp2 HLw C3; lia
              | |- 0 < rawp => exact RP
              | |- rw_cells _ _ rawp _ => eassumption
              | |- HK _ _ _ h3 _ => apply (proj2 (HKiff _)); exact HK9
              | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  cbv delta [A_pkcs7_parse_C24.dvA] beta;
                  split; [eassumption|]; split; [apply (proj2 (HKiff _)); exact HK9|]; split; [exact MF9'|];
                  split; [exact HT3|]; split; [exact HS3|]; split; [exact HF3|]; split; [exact HCS3|]; split; [exact HV3|]; split; [exact HFR3|];
                  split; [exact PRESb|]; split; [eassumption|];
                  repeat match goal with |- _ /\ _ => split end;
                  first [ eassumption | reflexivity
                        | lazymatch goal with |- rw_cells _ mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                        | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                        | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA975-LEFT:" g end ] ]
              end
            | assumption
            | match goal with |- ?g => idtac "F975E4-LEFT:" g end ]
    end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
