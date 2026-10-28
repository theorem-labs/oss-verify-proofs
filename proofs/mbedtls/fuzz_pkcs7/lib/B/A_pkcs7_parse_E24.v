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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24.
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
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.50000007S1R3NA0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.10600000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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
  Local Notation joint_0 := (A_pkcs7_parse_C24.joint_0 PHIj FFRj CNTj PHIj_mono FFRj_mono CNTj_mono).
  Local Notation joint_gs := (A_pkcs7_parse_C24.joint_gs PHIg FFRg CNTg PHIs FFRs CNTs PHIj FFRj CNTj PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint).
  Local Notation joint_g := (A_pkcs7_parse_C24.joint_g PHIg FFRg CNTg PHIs FFRs CNTs PHIj FFRj CNTj PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint).
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma reshape_gen : forall mc B pre mid rest k,
    rw_cells asegs mc B (pre ++ mid ++ rest) -> cells_size mid = k ->
    rw_cells asegs mc B (pre ++ [CB k (cells_bytes mid)] ++ rest).
  Proof.
    intros mc B pre mid rest k H SZ. ddestruct (rw_cells_split3 asegs mc B pre mid rest H) as (H1 & H2 & H3).
    apply rw_cells_join3; [exact H1| | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, <- SZ; exact H3].
    apply rw_cells_blob in H2. rewrite SZ in H2. exact H2.
  Qed.

  #[using="Type"] Lemma cb_bytes_at : forall mX B k xs, rw_cells asegs mX B [CB k xs] -> bytes_at asegs mX B xs.
  Proof. intros mX B k xs RC. destruct RC as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L14032639533.128L15232617654.128L35485059244.128L35497640934.130L46144785452.12800000E00Z00o01D01YS2LF2sp1A1n2bs3LFB2a'S2LF2sp1A1n2bs3LFB2a'S2LF2sp1A1n2bs3LFB2a'S2LF2sp1A1n2bs3LFB2a'S2LF2sp1A1n2bs3LFB2a'". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma signer_chain_presxD : forall m1 m' L1 L2 SP X a l,
    signer_chain asegs m1 L1 a l -> (forall b, In b (signer_blocks l) -> In b L2) ->
    heap_presx asegs L L2 SP X m1 m' ->
    (forall b, In b (signer_blocks l) -> 0 < snd b -> disjoint_from X (fst b) (snd b)) ->
    signer_chain asegs m' L2 a l.
  Proof.
    intros m1 m' L1 L2 SP X a l. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H HIN HP HDJ; [exact H|].
    ddestruct H as (-> & Hin & Hal & Hpos & inext & nxt & j & HR & HN & HC).
    assert (Hin2 : In (a', SIGNER_SIZE) L2) by (apply HIN; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    split; [reflexivity|]. split; [exact Hin2|]. split; [exact Hal|]. split; [exact Hpos|].
    dexists inext, nxt, j. split; [| split].
    - eapply heap_presx_rw_cells; [exact HP| exact HR| |].
      + eapply client_range_block; [exact Hin2| lia| cbn [cells_size csize Nat.add signer_cells]; unfold SIGNER_SIZE; lia].
      + cbn [cells_size csize Nat.add signer_cells]. apply (HDJ (a', SIGNER_SIZE)); [| unfold SIGNER_SIZE; cbn; lia].
        apply in_or_app; left. apply in_or_app; right. left. reflexivity.
    - eapply chain_presx; [exact HN| | exact HP| unfold NAME_SIZE; lia|].
      + intros x Hx. apply HIN. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
      + intros x Hx. apply (HDJ (x, NAME_SIZE)); [| unfold NAME_SIZE; cbn; lia]. apply in_or_app; left. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    - eapply IH; [exact HC| | exact HP|].
      + intros b Hb. apply HIN. apply in_or_app; right. exact Hb.
      + intros b Hb Hk. apply HDJ; [| exact Hk]. apply in_or_app; right. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L35497649836.11700000BS2LF2sp1A1n2bs3LFB". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma name_chain_presxD : forall m1 m' L1 L2 SP X a names,
    name_chain asegs (fun _ => True) m1 L1 a names -> (forall x, In x names -> In (x, NAME_SIZE) L2) ->
    heap_presx asegs L L2 SP X m1 m' ->
    (forall x, In x names -> disjoint_from X x NAME_SIZE) ->
    name_chain asegs (fun _ => True) m' L2 a names.
  Proof. intros. eapply chain_presx; [eassumption| eassumption| eassumption| unfold NAME_SIZE; lia| assumption]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2424960062.2  L30580884288.1400000600_S1n2HnS1R4STKg4STKs4STKf2sp1A2lo5ALO1'3SPR4SLO'". (* [comment removed for export] *)
  #[using="R STKg STKs STKf LF sp lo slo AAL A0 ASTK LEN Hn SLOS SLOL SLO LFB LOS ALO1"] Lemma rep_build : forall mX Lx (rt p0 ver vp dtg dpad : word) (rawp dlen dq : Z) (c56 c808 q3c : list cell) (f : crt_own) (jc : crt_junk)
      (inext snext : Z) (sj : signer_junk) (names0 : list Z) (sg : list (Z * list Z)),
    rw_cells asegs mX A ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ c56
                         ++ crt_cells f jc ++ c808 ++ [CB 416 (zeros 416)] ++ q3c ++ signer_cells inext snext sj) ->
    cells_size c56 = 8%nat -> cells_size c808 = 8%nat -> cells_size q3c = 8%nat ->
    rw_cells asegs mX rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> In (rawp, n) Lx ->
    crt_own_ok asegs PK mX (Lx ++ LB) (A + 64) f jc ->
    name_chain asegs (fun _ => True) mX (Lx ++ LB) inext names0 ->
    signer_chain asegs mX (Lx ++ LB) snext sg ->
    Permutation Lx ([(rawp, n)] ++ crt_blocks f ++ map (fun a => (a, NAME_SIZE)) names0 ++ signer_blocks sg) ->
    List.NoDup (map fst Lx) ->
    pkcs7_at asegs PK (Some (P7O n rawp f inext names0 snext sg,
                             P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ c56)) jc (cells_bytes c808) (cells_bytes q3c) sj bs))
             mX Lx LB A.
  Proof.
    intros until sg. intros HC S56 S808 S3 RC RP RIN OWN HN HS PERM ND. pose proof (alloc_ceiling_val R) as ACV. pose proof ALO1 as ALO1'.
    unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in ALO1'. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.
    eapply pkcs7_at_build; cbn [po_rawp po_rawlen po_crt po_issuer0_next po_names0 po_signers_next po_signers pj_raw pj_crt].
    - unfold pkcs7_cells. cbn [po_rawlen po_rawp po_crt po_issuer0_next po_signers_next pj_rawtag pj0 pj1 pj_crt pj2 pj3 pj_s0].
      (* [comment removed for export] *)
      pose proof (reshape_gen mX A [C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp)] ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ c56)
                    (crt_cells f jc ++ c808 ++ [CB 416 (zeros 416)] ++ q3c ++ signer_cells inext snext sj) 40 HC
                    ltac:(rewrite !cells_size_app; cbn [cells_size csize Nat.add buf_cells]; rewrite S56; reflexivity)) as HC1.
      pose proof (reshape_gen mX A ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); CB 40 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ c56))] ++ crt_cells f jc)
                    c808 ([CB 416 (zeros 416)] ++ q3c ++ signer_cells inext snext sj) 8 ltac:(rewrite <- app_assoc; exact HC1) S808) as HC2.
      pose proof (reshape_gen mX A (([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); CB 40 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ c56))] ++ crt_cells f jc) ++ [CB 8 (cells_bytes c808); CB 416 (zeros 416)])
                    q3c (signer_cells inext snext sj) 8 ltac:(rewrite <- !app_assoc; rewrite <- !app_assoc in HC2; exact HC2) S3) as HC3.
      rewrite <- ?app_assoc in HC3. rewrite <- ?app_assoc. exact HC3.
    - exact AAL.
    - exact A0.
    - unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *. pose proof SLO as SLO'. unfold A_pkcs7_parse_A.STKp in SLO'. clear - ALO1' SPR SLO' STKg0 STKs0 STKf0 NS1. lia.
    - exact RP.
    - clear - Hn; lia.
    - apply in_or_app. left. exact RIN.
    - exact RC.
    - exact OWN.
    - exact HN.
    - exact HS.
    - exact PERM.
    - exact ND.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma crt_unblob_mid : forall mX mw pre rest f jc,
    rw_cells asegs mw (A + 64) (crt_cells f jc) -> cells_size pre = 64%nat ->
    rw_cells asegs mX A (pre ++ [CB 744 (cells_bytes (crt_cells f jc))] ++ rest) -> rw_cells asegs mX A (pre ++ crt_cells f jc ++ rest).
  Proof.
    intros mX mw pre rest f jc CRTW SZ H. destruct (rw_cells_split3 asegs mX A _ _ _ H) as (H1 & H2 & H3).
    rewrite SZ in H2, H3. change (Z.of_nat 64) with 64 in H2, H3.
    assert (SZC : cells_size (crt_cells f jc) = 744%nat) by reflexivity.
    apply rw_cells_join3; [exact H1| rewrite SZ; exact (rw_cells_unblob _ _ _ _ _ _ CRTW SZC H2)| rewrite SZ, SZC; exact H3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@D16116793040.276D44450165448.276D60109196847.276K16199997286.276K23293880678.276K30406640486.276K33965119078.276K41460675942.276K42064520925.276K67530189413.276K8704438374.276 L1386317440.263 L14730345466.4  L16195849360.2  L16467427964.264L16467427964.265L16467427964.267L1685717371.0   L22056157363.9  L2213003991.4   L22706487826.5  L22706555648.3  L23298126480.2  L30410922128.2  L33969393040.2  L35666023782.15 L38691415991.0  L38738405142.1  L40228640085.0  L41473207952.2  L41529245.8     L41553137013.10 L41663468825.266L42077060395.2  L4290477465.10  L43300649301.0  L4519752719.264 L46960437801.4  L49495212411.2  L52069407411.266L53885755257.4  L53969727459.2  L56784576294.2  L57124690773.0  L60098763854.6  L64423694358.2  L64850595401.0  L65044888453.10 L67246375.0     L67529387105.3  L8691805072.2   L9356559676.20  P49501542924.276P64409801425.276Q11801279589.276Q15696256514.272Q15696419038.271Q15698272651.272Q16114545872.275Q16116793040.276Q21913097623.270Q21915098592.271Q21927647888.273Q33101684507.272Q34671632784.272Q39185082255.272Q42439443119.276Q42755330731.274Q44447922376.275Q44450165448.276Q46551147629.272Q520603521.272  Q59865321072.276Q6240324341.271 Q64683667846.276Q7524327693.273 Q7526559242.270 Q7528556157.271 Q8041752945.273 00002904B06R08Y0:`0<g0>n0A50C<0EW0G^0G_0Gn0Go0If0K]0MT0MU0N80NI0NW0N_0N`0Na0Nb0OG0OH0OK0OL0OM0On0PR0RI0RJ0R^0R_0UN0U]0U^0U_0Ul0V30V;0V<0VF0VG0VH0Vl0Vm0Vn0Vo0Wm0Zg0]d0_c0aP0c=0dj0fi0hh0k>0mT0oj11W13E15217:1901:o1<n1?Q1A?1A@1Bm1EU1GN1IG1K@1M3S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs3LEN2Hn3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2RA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC4APPA2HB5Ha_st5Hl_stFS4CNTj1n2Lx3CNTFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCSS4FFRj4CNTj4FFRf1n1d4FFRa2Lx4BFFR1HS2p44END23X0'3NE0S1R1A3AOD1a2DaS1A1a2HoFFFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTSS1ASFS4PHIj4CNTj4PHIf1n4PHIa2Lx4BPHI1HS1R1n4rawp2p44END22RP3Hp42C33ACV3BceS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCFS2r23Hr21r2KR1q1H2H0SS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC3SPR2F04SP1RS2p44END22B42BEFFS1n2Hn1f4RAWLS1R3ACVS2r23Hr2SS1R2lo3LOSFSS1R1n4rawp2p44END22RP3Hp42C33ACV3BceSFFS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCFS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB4rawp2r12r22rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HT2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq4j56r3q2r2q31f2jc5inext5snext2sj2Lx3SZC2HB". (* [comment removed for export] *)
  #[using="IMG NS1 HMND STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS ALO1"] Lemma from_979e8 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g12 g16 g18 g22 j32 alg : list byte)
      (rawp p4 END2 r1 r2 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56r q2r q3 : list byte)
      (f : crt_own) (jc : crt_junk) (mw : mem) (inext snext : Z) (sj : signer_junk) (names0 : list Z) (sg : list (Z * list Z))
      (Lx : list blk) mc moc hc (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s7v s8v s9v : word),
    dvA FB sp1 (X0 ++ si_fp SI) PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 p4)) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r]
         ++ [CB 744 (cells_bytes (crt_cells f jc))] ++ [C4 (Z_to_bv 64 0); CB 4 q2r] ++ [CB 416 (zeros 416); CB 8 q3] ++ signer_cells inext snext sj)
        Lx mc moc hc ->
    rw_cells asegs mw (A + 64) (crt_cells f jc) ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> In (rawp, n) Lx -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    crt_own_ok asegs PK mc (Lx ++ LB) (A + 64) f jc ->
    name_chain asegs (fun _ => True) mc (Lx ++ LB) inext names0 ->
    signer_chain asegs mc (Lx ++ LB) snext sg ->
    Permutation Lx ([(rawp, n)] ++ crt_blocks f ++ map (fun a => (a, NAME_SIZE)) names0 ++ signer_blocks sg) ->
    (forall B k, In (B, k) (crt_blocks f ++ map (fun a => (a, NAME_SIZE)) names0 ++ signer_blocks sg) -> 0 < k -> B + k <= A \/ A + 1440 <= B) ->
    co_rawlen f < 2 ^ 40 ->
    rawp <= p4 <= END2 -> END2 <= rawp + n ->
    -2^31 < r2 < 2^31 ->
    Z.of_nat (length Lx) <= CNTp n ->
    PHIa <= (2 * n + AVOL_CALL) + PHIj n -> FFRa <= fr_charge (d + 1) + FFRj n (d + 1) ->     (* [comment removed for export] *)
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r2) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) s3v s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) s7v s8v s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97fd0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D CRTW RAWB RP RIN RA OWN HN HSC PERM OAPX RAWL Hp4 C3 Hr2 CNT BPHI BFFR BUD BUDF.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    (* [comment removed for export] *)
    assert (CWAc : client_wrange L ((Lx ++ LB) ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { rewrite HTc. eapply client_wrange_mono; [exact CWA|]. intros b Hb. apply fdata_cons_sub. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (WCA : wcover R LB LF (bv_unsigned sp) (X0 ++ si_fp SI) A 1440) by (apply wcover_inside; cbn [inside app]; left; clear; lia).
    pose proof (blocks_below_hm R HIA hc _ _ mc (Lx ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (B4 : 0 <= p4 < 2 ^ 64) by (destruct (BBc _ (in_or_app _ _ _ (or_introl RIN))) as [_ Bce]; cbn [fst snd] in Bce; clear - Bce RP Hp4 C3 ACV; lia).
    assert (BE : 0 <= END2 < 2 ^ 64) by (destruct (BBc _ (in_or_app _ _ _ (or_introl RIN))) as [_ Bce]; cbn [fst snd] in Bce; clear - Bce RP Hp4 C3 ACV; lia).
    (* [comment removed for export] *)
    assert (TPX : forall mq st, pkcs7_at asegs PK st mq Lx LB A -> p7small st -> tailP (X0 ++ si_fp SI) PHIa FFRa Lx mq st).
    { intros mq st REPq SMq. split; [exact REPq|]. split; [exact SMq|]. split; [exact CNT|].
      split; [pose proof (PHIf_mono (Z.of_nat (length Lx)) (CNTp n) ltac:(clear - CNT; lia)); unfold A_pkcs7_parse_C.PHIp; clear - BPHI H; lia|].
      split; [pose proof (FFRf_mono (Z.of_nat (length Lx)) (CNTp n) 0 ltac:(clear - CNT; lia)); unfold A_pkcs7_parse_C.FFRp; clear - BFFR H; lia|].
      split; [intros x Hx; exact Hx|]. split; [intros x Hx; exact (proj1 (proj1 (outside_app _ _ x) Hx))|]. exact (conj BUD BUDF). }
    assert (ND : List.NoDup (map fst Lx)) by (pose proof (HMND _ _ _ _ HHc) as NDx; rewrite map_app in NDx; exact (NoDup_app_inv_l _ _ NDx)).
    assert (LXIN : forall b, In b (crt_blocks f ++ map (fun a => (a, NAME_SIZE)) names0 ++ signer_blocks sg) -> In b (Lx ++ LB)).
    { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. right. exact Hb. }
    assert (SM : p7small (Some (P7O n rawp f inext names0 snext sg, P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])) jc
                                 (cells_bytes [C4 (Z_to_bv 64 0); CB 4 q2r]) (cells_bytes [CB 8 q3]) sj bs))) by (cbn; clear - Hn RAWL; lia).
    (* [comment removed for export] *)
    assert (REP6 : pkcs7_at asegs PK (Some (P7O n rawp f inext names0 snext sg, P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])) jc
                                          (cells_bytes [C4 (Z_to_bv 64 0); CB 4 q2r]) (cells_bytes [CB 8 q3]) sj bs)) mc Lx LB A).
    { eapply rep_build; [| reflexivity| reflexivity| reflexivity| exact RAWB| exact RP| exact RIN| exact OWN| exact HN| exact HSC| exact PERM| exact ND].
      apply (crt_unblob_mid mc mw ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])
               ([C4 (Z_to_bv 64 0); CB 4 q2r] ++ [CB 416 (zeros 416)] ++ [CB 8 q3] ++ signer_cells inext snext sj) f jc CRTW eq_refl).
      rewrite <- ?app_assoc. rewrite <- ?app_assoc in CELLS. exact CELLS. }
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      apply rw_cells_blob in G8. cbn [cells_size csize cells_bytes cbytes app Nat.add] in G8.
      eapply (tail_97504 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := X0 ++ si_fp SI) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lx) (hc := hc)
                                     (st := Some (P7O n rawp f inext names0 snext sg, P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])) jc
                                                  (cells_bytes [C4 (Z_to_bv 64 0); CB 4 q2r]) (cells_bytes [CB 8 q3]) sj bs));
        first [ exact (TPX _ _ REP6 SM) | eassumption
              | lazymatch goal with |- - 2 ^ 31 <= r2 < 2 ^ 31 => clear - Hr2; lia end
              | (cbv beta; dvA_build) ]. }
    (* [comment removed for export] *)
    assert (R2nn : 0 <= r2).
    { change 18446744073709551615 with (Z.ones 64) in KR. rewrite Z.land_ones in KR by (clear; lia). clear - KR Hr2. Z.div_mod_to_equations. lia. }
    clear KR.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    zstep. zstep. zstep. zstep. zstep. zstep.
    clear ABc.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => pose proof (munch_refl [(A + 1232, A + 1236)] mx) as MU7; pose proof (wmono_refl asegs mx) as WM7 end.
    zstep. zstep.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m7 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of MU7 with munch _ ?mx _ => rename mx into m6 end.
    assert (HPX7 : heap_presx asegs L (Lx ++ LB) sp1 X0 m6 m7).
    { eapply heap_presx_of_munch; [exact MU7| exact WM7|]. intros a _ _ Ho. cbn [outside] in Ho |- *. clear - Ho. lia. }
    lazymatch goal with MI : mem_inv _ m7 |- _ => rename MI into MI7 end.
    assert (SI7 : si_P SI m7).
    { eapply (si_munch_offdata L SI); [exact SIc| exact MU7|]. intros a Da Wa. cbn [outside]. clear - Da AOD. lia. }
    clear SIc.
    assert (OWN7 : crt_own_ok asegs PK m7 (Lx ++ LB) (A + 64) f jc).
    { eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := X0) (SP := sp1);
        [exact OWN| intros b Hb; apply LXIN; apply in_or_app; left; exact Hb| exact HPX7| exact BBc| clear - ACV; lia| exact MI7|].
      intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [| exact I]. apply (OAPX B k); [apply in_or_app; left; exact Hb| exact Hk]. }
    assert (HN7 : name_chain asegs (fun _ => True) m7 (Lx ++ LB) inext names0).
    { eapply name_chain_presxD; [exact HN| | exact HPX7|].
      - intros x Hx. apply LXIN. apply in_or_app; right. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
      - intros x Hx. cbn. split; [| exact I]. apply (OAPX x NAME_SIZE); [| unfold NAME_SIZE; clear; lia].
        apply in_or_app; right. apply in_or_app; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx. }
    assert (HSC7 : signer_chain asegs m7 (Lx ++ LB) snext sg).
    { eapply signer_chain_presxD; [exact HSC| | exact HPX7|].
      - intros b Hb. apply LXIN. apply in_or_app; right. apply in_or_app; right. exact Hb.
      - intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [| exact I]. apply (OAPX B k); [| exact Hk]. apply in_or_app; right. apply in_or_app; right. exact Hb. }
    clear HPX7 MU7 WM7 OWN HN HSC.
    lazymatch goal with RB : rw_cells _ m7 rawp _ |- _ => rename RB into RAWB7 end.
    assert (REP7 : pkcs7_at asegs PK (Some (P7O n rawp f inext names0 snext sg, P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])) jc
                                          (cells_bytes [C4 (Z_to_bv 64 0); CB 4 q2r]) (cells_bytes [C4 (Z_to_bv 64 r2); CB 4 (skipn 4 q3)]) sj bs)) m7 Lx LB A).
    { eapply rep_build; [| reflexivity| reflexivity| reflexivity| exact RAWB7| exact RP| exact RIN| exact OWN7| exact HN7| exact HSC7| exact PERM| exact ND].
      apply (crt_unblob_mid m7 mw ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])
               ([C4 (Z_to_bv 64 0); CB 4 q2r] ++ [CB 416 (zeros 416)] ++ [C4 (Z_to_bv 64 r2); CB 4 (skipn 4 q3)] ++ signer_cells inext snext sj) f jc CRTW eq_refl).
      unfold buf_cells, signer_cells. cbn [app]. exact CELLS. }
    assert (SM7 : p7small (Some (P7O n rawp f inext names0 snext sg, P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [C4 (Z_to_bv 64 r1); CB 4 j56r])) jc
                                  (cells_bytes [C4 (Z_to_bv 64 0); CB 4 q2r]) (cells_bytes [C4 (Z_to_bv 64 r2); CB 4 (skipn 4 q3)]) sj bs))) by (cbn; clear - Hn RAWL; lia).
    apply rw_cells_blob in G8. cbn [cells_size csize cells_bytes cbytes app Nat.add] in G8.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (Z.eq_dec p4 END2) as [EQ|NE].
    - rewrite EQ, Z.lxor_nilpotent.
      match goal with |- context [Z_to_bv 64 (Z.land ?e1 ?e2)] =>
        replace (Z_to_bv 64 (Z.land e1 e2) : word) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
      rewrite EQ in G8.
      eapply (tail_97504 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := X0 ++ si_fp SI) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lx) (hc := hc) (r := 0);
        first [ exact (TPX _ _ REP7 SM7) | eassumption
              | lazymatch goal with |- - 2 ^ 31 <= 0 < 2 ^ 31 => clear; lia end
              | (cbv beta; dvA_build) ].
    - replace (Z.lxor p4 END2 <? 1) with false.
      2:{ symmetry. apply Z.ltb_ge. pose proof (proj2 (Z.lxor_nonneg p4 END2) ltac:(clear - B4 BE; lia)) as X0'.
          destruct (Z.eq_dec (Z.lxor p4 END2) 0) as [E0|NE0]; [| clear - X0' NE0; lia]. exfalso. apply NE. apply Z.lxor_eq. exact E0. }
      match goal with |- context [Z_to_bv 64 (Z.land ?e1 ?e2)] =>
        replace (Z_to_bv 64 (Z.land e1 e2) : word) with (Z_to_bv 64 (-21248) : word) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (tail_97504 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := X0 ++ si_fp SI) (PHIa := PHIa) (FFRa := FFRa) (Lc := Lx) (hc := hc) (r := -21248);
        first [ exact (TPX _ _ REP7 SM7) | eassumption
              | lazymatch goal with |- - 2 ^ 31 <= -21248 < 2 ^ 31 => clear; lia end
              | (cbv beta; dvA_build) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03c0@D16116793040.292D16116793040.293D44450165448.292D44450165448.293D60109196847.292D60109196847.293K16199997286.292K16199997286.293K23293880678.292K23293880678.293K30406640486.292K30406640486.293K33965119078.292K33965119078.293K41460675942.292K41460675942.293K42064520925.292K42064520925.293K67530189413.292K67530189413.293K8704438374.292 K8704438374.293 L10370335306.1  L10596430123.1  L11469879088.1  L11879002598.1  L1254959567.3   L13357322749.6  L14715664093.5  L15191836344.1  L1540877545.17  L1540877545.3   L15618147883.1  L15686577978.1  L15700613176.1  L15756354262.7  L1593228653.7   L16195849360.2  L16208316619.5  L16467427964.276L16467427964.279L16467427964.281L16467427964.282L1685717371.0   L16896526054.1  L17064006458.1  L17212877250.4  L17882190307.1  L19769535484.2  L19959024712.1  L19980016842.7  L20443553251.1  L21311120310.1  L21719861176.1  L22056157363.13 L2254620236.6   L22704459713.3  L23298126480.2  L24128180555.1  L2424960062.2   L2514189370.1   L26591772832.4  L26637699004.1  L26892418956.1  L27650499371.1  L28913793048.19 L29676255814.4  L29773715284.1  L30410922128.2  L31034375991.6  L31104916084.4  L31104916084.7  L31104916213.22 L31251627448.1  L31636313402.1  L31653556939.1  L31863022963.4  L31868079865.6  L32454903270.1  L32556390507.2  L32982411378.9  L33043839605.13 L33106041121.1  L33136591625.1  L33312313103.2  L33448935356.1  L33532570708.1  L33969393040.2  L34160466994.2  L34295895267.1  L34673485611.1  L35658253640.4  L35666023782.15 L35822716720.1  L36692980745.1  L37268777784.1  L37714553091.1  L38679745763.1  L38738405142.1  L39686831147.1  L40088084972.10 L40228640085.0  L40281191306.3  L40778157368.1  L41473207952.2  L41529245.12    L42077028656.1  L42077060395.2  L42642555220.1  L43105457693.10 L43171512609.1  L43300649301.0  L44334313263.1  L44771872639.281L46541147848.1  L47832818059.2  L47882514004.1  L48117736679.17 L4899644682.11  L49495212411.2  L49508988902.1  L49799904432.3  L50141024560.1  L50699569849.20 L51299303177.1  L51570243003.3  L52045659405.3  L52966452230.4  L53000928673.1  L53218759346.2  L53297529385.1  L53506910339.12 L53624487132.1  L53885755257.4  L53969727459.2  L54246093652.1  L55406783735.11 L56523586534.1  L56658999053.1  L56854842269.2  L57065636066.1  L57124690773.0  L57628698881.3  L57628893203.5  L58143913820.1  L58327394093.5  L58412049673.1  L58606322338.3  L58748427563.1  L59273946083.1  L59308586248.2  L59330201615.278L59427879996.275L59578101107.3  L60098763854.6  L6066307049.5   L61545304294.1  L61747380284.1  L61926053921.1  L61970568713.1  L62037211595.16 L6203936179.1   L62413581882.1  L63373084206.4  L64423694358.2  L64850595401.0  L65008825131.3  L65337174320.1  L65443826765.3  L66142926141.4  L66151427842.16 L66715901089.1  L66845504556.4  L66845505322.23 L66845505451.7  L66925289488.292L67159606587.3  L6739893627.21  L67529387105.3  L67884573201.1  L6899380056.1   L696052593.2    L7893464212.4   L8053507233.1   L806595063.12   L8201234081.0   L8466307646.21  L8640568525.3   L8691805072.2   L9356559676.20  L9364260897.1   L9631767084.2   L9762418081.1   L9873114841.15  P49501542924.292P49501542924.293P64409801425.292P64409801425.293Q12938238223.290Q1447144685.290 Q15183479086.289Q15198453515.290Q16114545872.291Q16114545872.292Q16116793040.292Q16116793040.293Q19561628010.292Q21913097623.283Q21914737458.288Q21915098592.286Q21927647888.289Q25075822059.292Q25075822059.293Q31253398539.287Q31255460748.288Q31255821662.286Q34671307936.292Q36758551813.289Q42439443119.292Q42439443119.293Q42755330731.290Q42755330731.291Q44447922376.291Q44447922376.292Q44450165448.292Q44450165448.293Q50535470061.287Q51011567989.286Q51738442767.287Q53005286293.288Q59865321072.292Q59865321072.293Q64683667846.292Q64683667846.293Q7524327693.289 Q7526559242.283 Q7528325295.288 Q7528556157.286 Q7757850595.292 Q8041752945.289 Q8041752945.290 Q8061862711.289 Q9633818773.292 00001j03a05[07R09S0;Q0=I0?>0A60Bk0Dc0FX0HP0JE0L=0N20Oj0Q_0T?0V_0XW0ZL0ZR0ZV0ZY0Z]0Zi0[B0[X0[[0\80\D0\H0\L0\O0\]0]:0];0]E0^m0`U0b=0ce0cf0cj0cn0d@0dC0dK0dP0dh0dk0do0e20eg0f90fB0fC0fG0fM0fQ0fZ0f]0fa0fe0h10hC0hG0hH0h[0he0i:0j>0jA0jE0jI0jY0jj0jn0k60kJ0kn0l10l50l<0l?0lC0lD0lJ0lM0lQ0l^0mC0mF0mJ0mM0mP0mS0mV0mZ0mn0mo0n80n;0n<0no0o20o30o70ob0oe0of0oj12J12O12W12[13R14?14@14D14P14S15c15g16216>16K16N16T16X17L17O17\17c17g18P18T18X18^18a18b18j19819;19M19Q19Z19^19a19g1<G1<H1<Q1<[1<o1=31=61=91==1=k1>01>41>D1>E1>F1>O1>R1>]1>o1?_1?b1?m1A41AI1C11C<1D<1D=1D@1DD1DL1D\1D_1EL1EM1FG1FR1FS1GQ1GT1G[1G^1HK1K61M^1PL1S71TU1Vi1XG1Ye1[U1]B1_21`_1bQ1dX1f_1hf1jm1l]1nJ1oh21F22d24C25a27Z29P2;72<^2>N2@;2Ak2CX2El2GJ2Hh2JF2JG2JH2La2O72Pa2RK2T52U_2W>2Xb2ZF2[d2]FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs3LEN2Hn3LFB4rawp2p34END22r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2RA3Hp32C34R1nn2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs3LEN2Hn3LFB4rawp2p34END22r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2RA3Hp32C34R1nn2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC4APPA2HB5Ha_st5Hl_stS4rawpS2FBS1AS2FBS4CNTj1n3CJ0S4rawp2p34END23Hp32p43Hp4S4CNTj1n4rawp3LBc4CNT1S1AS1R4STKg4STKs4STKf2sp3sp13SP1S2sp3sp13SP1S2FBS2FBS1AS1R2lo3LOS3ALOS4CNTg4CNTj1n3LBc2c14CNTc3GJCFS2FB1B1k1HS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCSS2FBS2FBS4rawp2p34END23Hp3S1AS1n4rawpS3sp1S1R3HIA1h2sp3TOP3sp13SP1S1AS2FBS1AS4FFRg4FFRj4CNTj4FFRf1n1d4FFRa4rawp3LBc2c14BFFR3GJF1HS1A2lo4ALO11a1k2H2S1A1x3Hx0FS2FBS1n2HnS2FBS1A1B1k1HS1AS2spS2FBS1R3HIA4PHIg4PHIs4PHIj4CNTj4PHIf1h1n4PHIa2p34END22hc2c13HVc4BPHI3BUD3PF03JSPS4rawp2p34END23Hp3S2FBFS1R3HIA1h2sp3TOP2HTS1A1a1k2H2S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS3sp13SP11a1k2H1S1AS2FBS2FBS2sp3SPH3sp13SP1S1R3HIA1h2sp1a2HaS2FBS2LF3LFBS1R2lo3LOS2FB3ALO2F1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1AS2FBS2FB2F0S1AS2FBFS1A2A0S1AS2FBS1A1n4rawp2RAS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS1AS2FBS1AS1AS1AS1AS2FBS2r13Hr11r2KR1q1H2H0SS1R3HIA1hS1AFS4PHIg4PHIj4CNTj4PHIf1n4PHIa4rawp3LBc2c14BPHI3GJP1HS1AFS2FBS4PHIg4PHIs4PHIj1n4PHIa2p34END22c14BPHI3JSPS1ASS2FBS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC3SPR2F04SP1RS3sp1S2r13Hr1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3ALO4DLOxS4FFRg4FFRs4FFRj1n1d4FFRa2p34END22c14BFFR3JSFFS2FBS2sp3sp13SP1S1AS1R3HIA4FFRg4FFRs4FFRj4CNTj4FFRf1h1n1d4FFRa2p34END22hc2c14HFRc4BFFR4BUDF3FF03JSFS2FBS1A2FB4APPAS2sp3sp13SP1S1A1n4rawp2RAS1AS1A2A0S2FBS4CNTg4CNTs4CNTj1n2p34END23LBc2c14CNTc3JSC3LBs5HCNT6S1AS1n2Hn1f4RAWLS1R3ACVS2FBS1R3HIA4PHIs1h4PHIa2p34END22hc3HVc2h63HV6S2FBS2spS1n2HnS1ASS1A1a2HoS1R1A3AOD1a2DaS1AS1R1n4rawp3ACV3RCES2FBS1R1A3AODS2FBS1AS1i2HiS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A02Hn3SLO3SPH3LFB4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC3SPR2F04SP1RFS2FB1c2HcS1R2lo3LOSS2LB1n4rawp3LBc4C24iS2FBS1AS1AS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3SPRS3sp1S2FBS1n2FB4rawp4APRFFSS1R2FB2F2S1AS1A2lo4ALO1S4rawp2p34END23Hp3S2sp2r03SPA1q1r1H2H02q02H43sp14SP1M2FB3F641A3AALS1AS2FB1a1k2H3S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F11a1k2H1S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1A2FB4APPAS1R3HIA4STKg4STKs4STKf1h2sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS1a2HaFS1AS2FBS2sp3SPRS1n2FB4rawp4APRFS1AS1R3HIA4FFRs1h1d4FFRa2p34END22hc4HFRc2h64HFR6SS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOS1A2lo4ALO1FS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1AS2FB2F0S1AS1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC3SPR2F82F0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2bs3AAL2A02Hn3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB4rawp2r12rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HT2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HBS1R4STKg4STKs4STKf2LF1A1n2bs2A03LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2HBS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj01f2jc3LBc3SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND STKg PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB LOS ALO1"] Lemma from_97990 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g12 g16 g18 g22 j32 alg : list byte)
      (rawp p3 END2 r1 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      (f : crt_own) (jc : crt_junk) (mw : mem) (LBc : list blk) mc moc hc (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s7v s9v : word) (c1 : Z),
    dvA FB sp1 (X0 ++ si_fp SI) PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 p3)) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (cells_bytes (crt_cells f jc))] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        (LBc ++ [(rawp, n)]) mc moc hc ->
    rw_cells asegs mw (A + 64) (crt_cells f jc) ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    crt_own_ok asegs PK mc ((LBc ++ [(rawp, n)]) ++ LB) (A + 64) f jc ->
    Permutation LBc (crt_blocks f) ->
    (forall B k, In (B, k) (crt_blocks f) -> 0 < k -> B + k <= A \/ A + 1440 <= B) ->
    co_rawlen f < 2 ^ 40 ->
    rawp <= p3 <= END2 -> END2 <= rawp + n ->
    rawp <= dq -> 0 <= dlen -> dq + dlen <= rawp + n ->
    -2^31 < r1 <= 1 ->
    (* [comment removed for export] *)
    0 <= c1 -> c1 <= n -> (0 <= r1 -> c1 + (END2 - p3) <= n) ->
    Z.of_nat (length LBc) <= CNTg c1 ->
    PHIa <= (2 * n + AVOL_CALL) + PHIg c1 -> FFRa <= fr_charge (d + 1) + FFRg c1 (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r1) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) s3v s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) s7v (Z_to_bv 64 (A + 32)) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97f78) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until c1. intros D CRTW RAWB RP RA OWN PERMc OAPc RAWL Hp3 C3 Q1 Q2 Q3 Hr1 C10 C1n C1S CNTc BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (CWAc : client_wrange L (((LBc ++ [(rawp, n)]) ++ LB) ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { rewrite HTc. eapply client_wrange_mono; [exact CWA|]. intros b Hb. apply fdata_cons_sub. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (WCA : wcover R LB LF (bv_unsigned sp) (X0 ++ si_fp SI) A 1440) by (apply wcover_inside; cbn [inside app]; left; clear; lia).
    pose proof (blocks_below_hm R HIA hc _ _ mc ((LBc ++ [(rawp, n)]) ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) (LBc ++ [(rawp, n)])) by (apply in_or_app; right; left; reflexivity).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ (in_or_app _ _ _ (or_introl RIN))) as [_ Bce]; exact Bce).
    (* [comment removed for export] *)
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ BA].
    pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA ltac:(apply in_or_app; left; exact RIN) ltac:(left; reflexivity)) as APRF. cbn [fst snd] in APRF.
    assert (APF : forall B k, In (B, k) (crt_blocks f) -> B + k <= FB \/ FB + 256 <= B).
    { intros B k Hb. pose proof (blocks_apart_app2 _ _ (B, k) (FB, 256) BA ltac:(apply in_or_app; left; apply in_or_app; left; eapply Permutation_in; [apply Permutation_sym; exact PERMc| exact Hb]) ltac:(left; reflexivity)) as X.
      cbn [fst snd] in X. exact X. }
    clear BA.
    assert (LXIN : forall b, In b (crt_blocks f) -> In b ((LBc ++ [(rawp, n)]) ++ LB)).
    { intros b Hb. apply in_or_app. left. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERMc| exact Hb]. }
    assert (ND : List.NoDup (map fst (LBc ++ [(rawp, n)]))) by (pose proof (HMND _ _ _ _ HHc) as NDx; rewrite map_app in NDx; exact (NoDup_app_inv_l _ _ NDx)).
    assert (PERM1 : Permutation (LBc ++ [(rawp, n)]) ([(rawp, n)] ++ crt_blocks f ++ map (fun a => (a, NAME_SIZE)) [] ++ signer_blocks [])).
    { cbn [map signer_blocks app]. rewrite app_nil_r. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PERMc. }
    (* [comment removed for export] *)
    ddestruct (joint_0 n ltac:(clear - Hn; lia)) as (PJ0 & FJ0' & CJ0). pose proof (FJ0' (d + 1)) as FJ0. clear FJ0'.
    ddestruct (joint_g c1 n (conj C10 C1n)) as (GJP & GJF' & GJC). pose proof (GJF' (d + 1)) as GJF. clear GJF'.
    pose proof (PHIf_mono 0 (CNTp n) ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as PF0.
    pose proof (FFRf_mono 0 (CNTp n) 0 ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as FF0.
    assert (TPX : forall mq st, pkcs7_at asegs PK st mq (LBc ++ [(rawp, n)]) LB A -> p7small st -> tailP (X0 ++ si_fp SI) PHIa FFRa (LBc ++ [(rawp, n)]) mq st).
    { intros mq st REPq SMq.
      assert (CNT1 : Z.of_nat (length (LBc ++ [(rawp, n)])) <= CNTp n) by (rewrite length_app; cbn [length]; unfold A_pkcs7_parse_C.CNTp; clear - CNTc GJC; lia).
      split; [exact REPq|]. split; [exact SMq|]. split; [exact CNT1|].
      split; [pose proof (PHIf_mono (Z.of_nat (length (LBc ++ [(rawp, n)]))) (CNTp n) ltac:(clear - CNT1; lia)); unfold A_pkcs7_parse_C.PHIp; clear - BPHI H GJP; lia|].
      split; [pose proof (FFRf_mono (Z.of_nat (length (LBc ++ [(rawp, n)]))) (CNTp n) 0 ltac:(clear - CNT1; lia)); unfold A_pkcs7_parse_C.FFRp; clear - BFFR H GJF; lia|].
      split; [intros x Hx; exact Hx|]. split; [intros x Hx; exact (proj1 (proj1 (outside_app _ _ x) Hx))|]. exact (conj BUD BUDF). }
    set (po1 := P7O n rawp f 0 [] 0 []).
    set (pj1 := P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) jc (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs).
    assert (SM1 : p7small (Some (po1, pj1))) by (cbn; clear - Hn RAWL; lia).
    assert (REP4 : pkcs7_at asegs PK (Some (po1, pj1)) mc (LBc ++ [(rawp, n)]) LB A).
    { subst po1 pj1. eapply rep_build; [| reflexivity| reflexivity| reflexivity| exact RAWB| exact RP| exact RIN| exact OWN| apply chain_nil| reflexivity| exact PERM1| exact ND].
      apply (crt_unblob_mid mc mw ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])
               ([CB 8 q2] ++ [CB 416 (zeros 416)] ++ [CB 8 q3] ++ signer_cells 0 0 sj0) f jc CRTW eq_refl).
      rewrite <- ?app_assoc. rewrite <- ?app_assoc in CELLS. exact CELLS. }
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      apply rw_cells_blob in G8. cbn [cells_size csize cells_bytes cbytes app Nat.add] in G8. rewrite ?app_nil_r in G8.
      eapply (tail_97504 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := X0 ++ si_fp SI) (PHIa := PHIa) (FFRa := FFRa) (Lc := LBc ++ [(rawp, n)]) (hc := hc)
                                     (st := Some (po1, pj1));
        first [ exact (TPX _ _ REP4 SM1) | eassumption
              | lazymatch goal with |- - 2 ^ 31 <= r1 < 2 ^ 31 => clear - Hr1; lia end
              | (cbv beta; dvA_build) ]. }
    assert (R1nn : 0 <= r1).
    { change 18446744073709551615 with (Z.ones 64) in KR. rewrite Z.land_ones in KR by (clear; lia). clear - KR Hr1. Z.div_mod_to_equations. lia. }
    clear KR REP4.
    (* [comment removed for export] *)
    ddestruct (joint_gs c1 (END2 - p3) n C10 ltac:(clear - Hp3; lia) (C1S R1nn)) as (JSP & JSF' & JSC). pose proof (JSF' (d + 1)) as JSF. clear JSF'.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => pose proof (munch_refl [(A + 56, A + 60); (A + 808, A + 812)] mx) as MU5; pose proof (wmono_refl asegs mx) as WM5 end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    clear ABc.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m5 end.
    lazymatch type of MU5 with munch _ ?mx _ => rename mx into m4 end.
    assert (HPX5 : heap_presx asegs L ((LBc ++ [(rawp, n)]) ++ LB) sp1 X0 m4 m5).
    { eapply heap_presx_of_munch; [exact MU5| exact WM5|]. intros a _ _ Ho. cbn [outside] in Ho |- *. clear - Ho. lia. }
    lazymatch goal with MI : mem_inv _ m5 |- _ => rename MI into MI5 end.
    assert (SI5 : si_P SI m5).
    { eapply (si_munch_offdata L SI); [exact SIc| exact MU5|]. intros a Da Wa. cbn [outside]. clear - Da AOD. lia. }
    assert (OWN5 : crt_own_ok asegs PK m5 ((LBc ++ [(rawp, n)]) ++ LB) (A + 64) f jc).
    { eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := X0) (SP := sp1);
        [exact OWN| exact LXIN| exact HPX5| exact BBc| clear - ACV; lia| exact MI5|].
      intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [| exact I]. exact (OAPc B k Hb Hk). }
    clear SIc OWN MU5 WM5 HPX5.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    splitat CELLS 6%nat CDA. splitat CDA 4%nat C56. splitat C56 2%nat CC. splitat CC 1%nat CZ1. splitat CZ1 3%nat CQ3. splitat CQ3 1%nat CSG.
    change (rw_cells asegs m5 (A + 32) (buf_cells dtg dpad dlen dq)) in CDA.
    change (rw_cells asegs m5 (A + 1240) (signer_cells 0 0 sj0)) in CSG.
    lazymatch goal with HH : HM _ _ _ hc _ _ m5 |- _ => rename HH into HH5 end.
    lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) m5 A 1440 |- _ => rename OB into OBJ5 | _ => idtac "no OBJ5" end.
    frame_aobj FSH (FB + 64) 1%nat as OPP.
    assert (CWP : client_wrange L (((LBc ++ [(rawp, n)]) ++ LB) ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) (FB + 64) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    assert (UW5 : uwc asegs m5 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs m5 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKg0 STKs0 STKf0; lia].
        intros a Ha. apply (proj2 (outside_app _ _ a)). split; [cbn; split; [clear - Ha ASTK LOS SLO NS1 STKg0 STKs0 STKf0; lia| exact I]|].
        eapply (disjoint_outside _ (bv_unsigned sp) (hstkhi asegs R HIA h - bv_unsigned sp)); [| clear - Ha; lia].
        apply (si_disjoint_off L SI). right. pose proof (art_data_lo asegs R HIA) as DLOx. clear - DLOx ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    destruct (sshad_split asegs AL m5 slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 STKg0 STKs0 STKf0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi]. clear SSc.
    pose proof (art_data_lo asegs R HIA) as DLOW.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GETSIGNERS with (h := hc) (LB := (LBc ++ [(rawp, n)]) ++ LB) (LF := (FB, 256) :: LF) (PP := FB + 64) (P := p3) (END := END2) (BUF := rawp) (bs := bs)
                             (SIG := A + 1240) (DALG := A + 32) (lo := lo) (slo := slo) (d := d + 1) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (sj := sj0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold SIGNER_SIZE;
        first [ exact HH5 | exact HK1 | exact G8 | exact OPP | exact CWP | exact CSG | exact CDA | exact STlo | exact SSlo | exact SLOS | exact SLOL | exact MI5 | exact TPV | exact UW5 | exact Q1 | exact Q2 | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => unfold LFMAX_CRT; cbn [length]; clear - LFB; lia
                | |- bytes_at _ m5 rawp bs => exact (cb_bytes_at _ _ _ _ RAWB)
                | |- In (rawp, Z.of_nat (length bs)) _ => rewrite LEN; apply in_or_app; left; exact RIN
                | |- List.NoDup _ => exact (HMND _ _ _ _ HH5)
                | |- aobj _ _ _ m5 (A + 1240) _ => eapply aobj_sub; [exact OBJ5| clear; lia| clear; lia]
                | |- aobj _ _ _ m5 (A + 32) _ => eapply aobj_sub; [exact OBJ5| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (A + 1240) _ => eapply client_wrange_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- client_range _ _ _ (A + 32) _ => eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- (A + 1240) mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                | |- (A + 32) mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                | |- 0 < FB + 64 => clear - F0; lia
                | |- 0 < A + 1240 => clear - A0; lia
                | |- 0 < A + 32 => clear - A0; lia
                | |- 0 < rawp => exact RP
                | |- FB + 64 + 8 <= lo => clear - F1 ALO LOS; lia
                | |- A + 1240 + 200 <= lo => clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                | |- A + 32 + 24 <= lo => clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                | |- rawp <= p3 => clear - Hp3; lia
                | |- p3 <= END2 => clear - Hp3; lia
                | |- END2 <= rawp + Z.of_nat (length bs) => rewrite LEN; exact C3
                | |- dq + dlen <= rawp + Z.of_nat (length bs) => rewrite LEN; exact Q3
                | |- rawp + Z.of_nat (length bs) < 2 ^ 47 => rewrite LEN; clear - RCE ACV; lia
                | |- Z.of_nat (length bs) < 2 ^ 30 => rewrite LEN; clear - Hn; lia
                | |- FB + 64 + 8 <= rawp \/ rawp + _ <= FB + 64 => rewrite ?LEN; clear - APRF; lia
                | |- A + 1240 + 200 <= rawp \/ rawp + _ <= A + 1240 => rewrite ?LEN; clear - RA; lia
                | |- FB + 64 + 8 <= A + 1240 \/ _ => clear - APPA; lia
                | |- FB + 64 + 8 <= A + 32 \/ _ => clear - APPA; lia
                | |- A + 32 + 24 <= A + 1240 \/ _ => left; clear; lia
                | |- lo <= sp1 - STKs => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite ?HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold A_pkcs7_parse_C.PHIp in BUD; clear - BUD HVc BPHI JSP PF0; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold A_pkcs7_parse_C.FFRp in BUDF; clear - BUDF HFRc BFFR JSF FF0; lia
                | |- uwc _ m5 _ _ _ _ _ => rewrite HSc; exact UW5
                end
              | match goal with |- ?g => idtac "GETSIGNERS-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms6 mo6x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m6 & mo6 & h6 & r2 & p4 & inext & snext & sj & names0 & sg & LBs
                    & E6 & Ea0 & Hr2 & MI6 & ST6 & SS6 & MF6 & HP6 & HT6 & HS6 & HF6 & HK6 & HCS6 & HV6 & HFR6 & HCNT6 & HPP6 & Hp4 & CSG6 & CDA6 & HN6 & HSC6 & PERM6 & HH6).
    injection E6 as Ems Emo. subst ms6 mo6x ua0.
    replace (ret_pc (Z_to_bv 64 0x97fd0)) with (Z_to_bv 64 0x97fd0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST6, SS6, HP6 by exact SP1R. unfold SIGNER_SIZE in HP6.
    rewrite HTc in HT6. rewrite HSc in HS6, HP6. rewrite HFc in HF6.
    assert (HCSh6 : forall x, CS x -> hcs asegs R HIA h6 x) by (intros x Hx; apply HCS6, HCSc, Hx).
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (X0 ++ si_fp SI) m m6).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (HP6w : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)] m5 m6).
      { eapply presA_weaken; [exact HP6| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      pose proof (presA_drop_fresh_gen R LB LF sp1 sp1 (hstkhi asegs R HIA h) [(A + 1240, A + 1240 + 200)] FB 256 (FB + 64) (FB + 64 + 8) m5 m6 HP6w FRSH
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - F1 FBLO SP1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as HP6d.
      eapply presA_weaken; [exact HP6d| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia|].
      intros x Hx. pose proof (proj1 (proj1 (outside_app _ _ x) Hx)) as Hx0. cbn [outside] in Hx0 |- *. clear - Hx0. lia. }
    clear PRES.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJF : forall a k, FB <= a -> a + k <= FB + 256 -> (a + k <= FB + 64 \/ FB + 72 <= a) -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)] a k).
    { intros a k H1 H2 H3. cbn. split; [clear - H3; lia| split; [clear - H1 H2 APPA; lia| exact I]]. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)] a k).
    { intros a k H1. cbn. split; [clear - H1 F1 ALO LOS SP1 SLO NS1 STKg0 STKs0 STKf0; lia| split; [clear - H1 ASTK LOS SP1 SLO NS1 STKg0 STKs0 STKf0; lia| exact I]]. }
    assert (DJA : forall a k, A <= a -> a + k <= A + 1240 -> disjoint_from [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)] a k).
    { intros a k H1 H2. cbn. split; [clear - H1 H2 APPA; lia| split; [clear - H2; lia| exact I]]. }
    assert (CRsub : forall a k, A <= a -> a + k <= A + 1440 -> client_range L (((LBc ++ [(rawp, n)]) ++ LB) ++ fdata ((FB, 256) :: LF)) sp1 a k).
    { intros a k H1 H2. apply (client_range_lower L _ lo sp1 a k); [| clear - H2 ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia].
      eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| exact H1| exact H2]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) ((LBc ++ [(rawp, n)]) ++ LB) ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)] m5 m6 FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP6 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in STa; [| clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in SShi; [| clear; lia| clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m6 slo sp1 (bv_unsigned sp) SS6 SShi ltac:(clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia)) as SSm6. clear SS6 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in CELLS; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in C56; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in CC; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in CZ1; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in CQ3; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    clear CDA CSG.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m5 m6 _ _ HP6) in RAWB;
      [| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact RIN| clear; lia| clear; lia]
       | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); cbn; split; [clear - APRF; lia| split; [clear - RA; lia| exact I]] ].
    assert (OBJ6 : aobj asegs AL CS m6 A 1440).
    { eapply presA_aobj0; [exact CSOK| exact HP6| exact OBJA| intros x Hx; eapply hcs_below_top; exact Hx| right; split; [apply CRsub; clear; lia| clear; lia]]. }
    assert (SI6 : si_P SI m6).
    { eapply (si_heap_presx asegs L SI); [exact SI5| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP6)|].
      intros a Ha. apply (si_outside2 L SI (FB + 64) 8 (A + 1240) 200 a); [clear - F2; lia| clear - AOD; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia| exact Ha]. }
    pose proof (blocks_below_hm R HIA h6 _ _ m6 (LBs ++ (LBc ++ [(rawp, n)]) ++ LB) HH6 ltac:(intros b Hb; exact Hb)) as BB6.
    assert (OWN6 : crt_own_ok asegs PK m6 ((LBs ++ LBc ++ [(rawp, n)]) ++ LB) (A + 64) f jc).
    { assert (OWN6a : crt_own_ok asegs PK m6 ((LBc ++ [(rawp, n)]) ++ LB) (A + 64) f jc).
      { eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := [(FB + 64, FB + 64 + 8); (A + 1240, A + 1240 + 200)]) (SP := sp1);
          [exact OWN5| exact LXIN| | exact BBc| clear - ACV; lia| exact MI6|].
        - eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP6)| intros b Hb; apply in_or_app; left; exact Hb| clear; lia| intros x Hx; exact Hx].
        - intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [pose proof (APF B k Hb); clear - H Hk; lia| split; [pose proof (OAPc B k Hb Hk); clear - H; lia| exact I]]. }
      rewrite <- (app_assoc LBs (LBc ++ [(rawp, n)]) LB).
      eapply (crt_own_ok_presx2 asegs L PK m6 m6) with (CE := alloc_ceiling) (X := []) (SP := sp1) (Lp := (LBc ++ [(rawp, n)]) ++ LB);
        [exact OWN6a| intros b Hb; apply in_or_app; right; exact (LXIN b Hb)| exact LXIN| apply heap_presx_refl| exact BBc| constructor| clear - ACV; lia| exact MI6]. }
    clear OWN5 OBJA MI5 SI5 STlo HP6.
    (* [comment removed for export] *)
    unfold buf_cells in CDA6. unfold signer_cells in CSG6.
    joinr CQ3 CSG6. joinr CZ1 CQ3. joinr CC CZ1. joinr C56 CC. joinr CDA6 C56. joinr CELLS CDA6.
    pose proof HPP6 as G8'. apply rw_cells_blob in G8'. cbn [cells_size csize cells_bytes cbytes app Nat.add] in G8'. rewrite ?app_nil_r in G8'.
    (* [comment removed for export] *)
    assert (HV6' : havol asegs R HIA h6 <= havol asegs R HIA h + (PHIa + PHIs (END2 - p3))) by (clear - HV6 HVc; lia).
    assert (HFR6' : hfr asegs R HIA h6 <= hfr asegs R HIA h + (FFRa + FFRs (END2 - p3) (d + 1))) by (clear - HFR6 HFRc; lia).
    assert (CNT6 : Z.of_nat (length (LBs ++ LBc ++ [(rawp, n)])) <= CNTp n).
    { rewrite !length_app. cbn [length]. unfold A_pkcs7_parse_C.CNTp. clear - HCNT6 JSC CNTc. lia. }
    assert (C24y : cnt24 ((LBs ++ LBc ++ [(rawp, n)]) ++ LB) <= cnt24 LB + 1 + 2 * (n / 5889)).
    { rewrite <- app_assoc. rewrite cnt24_app. rewrite (cnt24_signers _ _ _ PERM6). blk_norm_in C24i. blk_norm_goal. clear - C24i. lia. }
    rewrite (app_assoc LBs (LBc ++ [(rawp, n)]) LB) in HH6, HN6, HSC6.
    eapply (from_979e8 FB sp1 (PHIa + PHIs (END2 - p3)) (FFRa + FFRs (END2 - p3) (d + 1)) w0 w1 w2 v48 v80 g4 g12 g16 g18 g22 j32 alg rawp p4 END2 r1 r2 rt p0 ver vp dtg dpad dlen dq
              _ _ q3 f jc mw inext snext sj names0 sg (LBs ++ LBc ++ [(rawp, n)]) m6 mo6 h6);
      first [ exact CRTW | exact RAWB | exact RP | exact RA | exact OWN6 | exact HN6 | exact HSC6 | exact RAWL | exact C3 | exact Hr2 | exact CNT6 | exact BUD | exact BUDF
            | lazymatch goal with
              | |- In (rawp, n) _ => apply in_or_app; right; exact RIN
              | |- Permutation _ _ =>
                  eapply Permutation_trans; [apply Permutation_app_comm|]; rewrite <- app_assoc;
                  eapply Permutation_trans; [apply Permutation_app_swap_app|]; cbn [app]; apply perm_skip;
                  apply Permutation_app; [exact PERMc| unfold SNAME in PERM6; exact PERM6]
              | |- rawp <= p4 <= END2 => clear - Hp4 Hp3; lia
              | |- PHIa + PHIs _ <= _ => clear - BPHI JSP; lia
              | |- FFRa + FFRs _ (d + 1) <= _ => clear - BFFR JSF; lia
              | |- forall B k, In (B, k) _ -> 0 < k -> _ =>
                  intros B k Hb Hk; apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (OAPc B k Hb Hk)|];
                  eapply (obj_apart_new R HIA h6 LBs ((LBc ++ [(rawp, n)]) ++ LB) LF ((FB, 256) :: LF) m6 lo (htop asegs R HIA h) A 1440 B k DIMG);
                  [rewrite <- (app_assoc LBs (LBc ++ [(rawp, n)]) LB) in HH6; exact HH6| intros fb Hfb; right; exact Hfb| | clear - ALO LOS; lia| clear; lia| | exact Hk];
                  [ eapply client_wrange_mono; [exact CWA| intros b Hb'; apply in_app_iff in Hb'; apply in_app_iff; destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; exact Hb'| right; exact Hb']]
                  | eapply Permutation_in; [apply Permutation_sym; exact PERM6|]; unfold SNAME; exact Hb ]
              | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  split; [exact HH6|]; split; [exact HK6|]; split; [eapply mo_frame_trans; [exact MFc| eapply mo_frame_trans; [exact MF1| exact MF6]]|];
                  split; [exact HT6|]; split; [exact HS6|]; split; [exact HF6|]; split; [exact HCSh6|]; split; [exact HV6'|]; split; [exact HFR6'|];
                  split; [exact PRESb|]; split; [exact SI6|];
                  repeat match goal with |- _ /\ _ => split end;
                  first [ exact G8' | exact CELLS | exact OBJ6 | eassumption | reflexivity
                        | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                        | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA6-LEFT:" g end ] ]
              end
            | match goal with |- ?g => idtac "F976E4-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04^0@C17025492443.289C54586839181.290D40772109871.290D50818716548.272D55889817356.272D56475227919.290D60109446735.290D65178138846.290K13515552910.290K20993777550.290K34874119485.290K3639265129.289 K40953392141.290K43464830217.290K44665102626.290K46287977870.290K56954985102.290K6402262670.290 K68007439502.290L10370335306.1  L10596430123.1  L11825282338.3  L11879002598.1  L12267397436.2  L1254959567.3   L13511127832.2  L13559991919.1  L14023416440.260L15191836344.1  L1540877545.17  L1540877545.3   L15618147883.1  L15686577978.1  L15734601492.17 L15756354262.7  L15824827452.2  L16272328766.3  L1643305408.9   L16467427964.258L16503999923.3  L16811460530.285L1685717371.0   L16896526054.1  L17021776415.9  L17064006458.1  L1903154355.3   L19769535484.2  L19959024712.1  L19980016842.7  L20998132760.2  L21280122319.2  L21311120310.1  L21712497613.3  L21868500043.2  L22251874280.7  L2254620236.6   L22704459713.3  L22939159100.2  L23618331571.3  L24128180555.1  L2424960062.2   L2503300556.20  L2514189370.1   L26892418956.1  L27175237299.3  L27650499371.1  L27737037422.21 L28961244751.2  L29150121138.2  L2939434296.9   L29435231613.2  L29773715284.1  L31034375991.6  L3156381960.260 L3156381960.276 L31636313402.1  L31653556939.1  L31863022963.4  L32285870553.7  L32345789891.2  L32454903270.1  L32556390507.2  L32955242219.16 L32978455966.1  L32982411378.9  L32984484578.1  L33136591625.1  L33211686944.2  L33312313103.2  L33532570708.1  L33982705724.2  L34661878195.3  L34673485611.1  L34870222507.2  L35666023782.15 L3624015310.2   L36692980745.1  L36731335728.3  L37475594310.15 L37714553091.1  L37855325666.3  L38235734261.1  L38679745763.1  L38738405142.1  L39686831147.1  L39862048955.3  L40281191306.3  L40369717752.3  L40778157368.1  L40953952873.3  L41068191504.9  L41096910396.2  L4187569568.3   L41922307974.4  L42642555220.1  L42779898568.4  L43300649301.0  L43454096926.1  L43882045675.4  L44334313263.1  L44675085189.3  L44908280802.1  L45296581822.2  L46275753496.2  L46541147848.1  L4692531706.18  L47882514004.1  L48079476396.13 L49000381535.12 L49278698542.2  L49292959580.283L49508988902.1  L49799904432.3  L5023981265.13  L50790731766.15 L50873506834.2  L51299303177.1  L51508673957.0  L5153599366.2   L52045659405.3  L52575544124.1  L52839883568.2  L53297529385.1  L54246093652.1  L5460295853.7   L54651097983.4  L54963599545.2  L54978688591.284L55043972167.14 L55714664252.2  L56523586534.1  L56658999053.1  L56942760216.2  L57124690773.0  L57230825576.266L58143913820.1  L58327394093.5  L58412049673.1  L58748427563.1  L59198135667.4  L59198135925.22 L59198136052.7  L59308586248.2  L59578101107.3  L60098763854.6  L60503691675.18 L60589918416.6  L61292069120.3  L61545304294.1  L61603606271.1  L61671942897.1  L61970568713.1  L62037211595.16 L6203936179.1   L62413581882.1  L63373084206.4  L6398364952.2   L64850595401.0  L65008825131.3  L65337174320.1  L65414423329.0  L65781247302.9  L66151427842.16 L66590572961.0  L66845504556.4  L66845505322.23 L66845505451.7  L66939708074.280L6736229990.3   L6739893627.21  L67884573201.1  L68002948888.2  L6899380056.1   L696052593.2    L7735748552.2   L7893464212.4   L8053507233.1   L8265267294.0   L8466307646.21  L881835912.0    L9356559676.20  L9389275059.3   L9536947392.268 L9631767084.2   L9873114841.15  O13114015517.290O14736948856.290O1478916974.290 O17025492443.289O18631257245.288O22980131687.290O24268044341.288O2598354827.290 O28722692754.290O37051008023.290O37526595730.290O4013719057.290 O43472075384.290O45781431160.290O47761277330.290O47806715794.290O50138229880.290O50702732434.290O52429235576.290O54586839181.290O56414299794.290O565947610.290  O57111671029.289O59625529265.290O63481010296.290O9250788821.290 O9257030307.290 P12278670331.272P15835051771.272P16257178265.288P16498286356.290P1904674324.290 P21282481928.272P21870859916.272P22945712379.272P23608422676.290P27165320212.290P28971467912.272P32335060692.290P33980871419.272P34677103380.290P3639265129.289 P36737083031.290P37861113669.289P40379732831.290P41095599355.272P43464830217.290P45282373145.290P50879319733.288P52838298007.290P54651585819.290P54978542206.272P55703916027.272P61291792132.272P6734636225.290 P7750690063.272 P9383453972.290 Q12683804246.290Q15163850165.272Q15766564435.290Q19546686416.280Q21925682067.266Q22712450012.272Q2513790033.270 Q25511591557.272Q25513505925.271Q26630670972.268Q26634504698.284Q29114031881.290Q34362328320.272Q34669473306.280Q36856420847.290Q38248387216.290Q40772109871.290Q42388231288.272Q42439168719.290Q42439443119.272Q43879899724.290Q45718585479.272Q45720570503.271Q49698585326.270Q50840533351.290Q54978688591.290Q59865321072.272Q59865603600.290Q60993511497.268Q60997411791.284Q64683667846.272Q64683942374.290Q65178138846.290Q66209653702.290Q6783377981.272 Q7522361358.266 Q7759684953.280 Q9080751600.269 Q9644567087.280 Q9644583048.290 00000100201Q04806g09B0:h0<G0=d0?A0@^0@_0Ba0Bb0DC0E`0G=0HZ0J70J=0JA0JJ0JN0JO0J[0J\0J_0L>0LA0L^0Lj0Ln0M20N60ND0NE0NF0Ni0PH0PI0Qh0Qi0Qm0RP0RT0RU0R]0Rb0S:0S;0S<0S@0SK0SL0Sb0T40T>0T?0T@0TD0TJ0UI0UM0UQ0UR0UV0VZ0V[0Va0WD0WJ0WN0Wa0Y@0Z_0Zc0Zg0[70[P0[Q0[U0[]0\S0\V0\j0\m0]10]90]@0]D0]E0]F0]J0]K0^00^10^50^60^k0^n0^o0_30_60_90_=0_H0_Q0_R0_U0_V0_o0`00`;0`H0`L0`Y0`Z0`[0`j0`n0`o0a20a30a40a90aj0an0bQ0c10c90dX0d\0dh0eL0f:0f;0f?0f@0fH0fT0fW0fX0f\0f`0g80g90g:0i^0jP0jQ0jU0jY0jZ0j[0m?0mB0mT0mX0m\0mf0o40oI0oO0oX0ob10j11B11C11G11L11O11S12A12F12J12Z12[12\12e12h12i13K14;14<14G15N15c17B17C18C18F18G18K18S18T18d18g18h19b19c1:a1:b1<A1<H1=51=61=71=81=91=:1=;1=<1==1=>1=?1=@1=A1=B1=C1=D1=E1=F1=G1=H1=I1=J1=K1=L1=M1=N1=O1=P1@:1Bd1E71FY1H;1J]1MB1Og1QI1Rk1UR1Wb1ZL1[n1[o1]P1_11`S1c=1c>1eQ1gd1j71lK1nm21W24O26027]29?2:\2:]2<P2>92@72Ad2D=2Em2G]2I>2J_2L42L52MK2ML2Nb2P72RV2T22Ua2WB2YO2[\2]A2^b2``2`a2`b2b`2d^2fm2hi2j>2j?2la2nB2oX31232K33dFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2bs3LEN2Hn3LFB4rawp2P24END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RA2C12C22C3FS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS1R4STKg4STKs4STKf2LF1A1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4APPAS4rawpS2FBS1R1A3AODS2FBFS4CNTj1n3CJ0FS1AS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1AS1R4STKg4STKs4STKf2sp3sp13SP1S2sp3sp13SP1S2FBS2FBS1R3HIA4PHIg4PHIj4CNTj4PHIf1h1n4PHIa2P24END22hc3HVc4BPHI3BUD3GNP3PF0S1R2lo3LOS3ALOFFS4C24c2LB1n4C24H4rawp2P24END22CC2DMS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCSS2FBS4PHIg1n4PHIa2P24END24BPHI2r12p32c1S2FBFS1n4rawpS3sp1S1R3HIA1h2sp3TOP3sp13SP1FFS2FBS1A2lo4ALO1FS1n4rawp2P24END22C12C3S1A2lo4ALO11a1k2H2S1A2xq3Hx0FFS2FBS1n2HnS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV4SP1RS2FBS2spFS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALO4DLOW1a2H1FS1A2A0S4FFRg1d4FFRa2P24END24BFFR2r12p32c1S1n2HnS2FBS1R3HIA1h2sp3TOP2HTS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS2FBS2sp3SPH3sp13SP1S1R2FB2F21a1k2H12H21A3AODFS2FBS2LF3LFBS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S1AS1R2lo3LOS2FB3ALO2F1S1AS2FBS2lo3sp1S2FB2F0S2FBFFS2FBFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTFS2FBFS1R3HIA4FFRg1h1d4FFRa2P24END22hc4HFRc2h32r12p32c13CX2S1AFS2loS1AS1AS2FBS1A2FB4APPAS1R3HIA1hFS1AFS1n4rawp2P24END22C12C22C3FS2sp2lo3sp1S1A1n4rawp2RAS2FBS1A1n4rawp2RASFS2sp2lo3sp13SP1S2FBFS1AFFS3sp1S1R4STKg4STKs4STKf5STKg02sp1A2lo4ASTK3SLO3SPH3LOSS2FBS1n4rawp2P24END22C12C22C32r12p33RN1S1n4rawp2P24END22C12C32r12p33Hp3S2lo3sp1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS2sp3sp13SP1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSFS2FBSS2lo3sp1S2sp3sp13SP1S1AFS2FBS2FBS1R3HIA1h2sp3TOP3sp13SP1FFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A04ASTK3LEN2Hn3SLO3LFB3LOS4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R3HIA4PHIg1h4PHIa2P24END22hc3HVc2h32r12p32c13CX1FS2FBS2spFSS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo2bs2A04ASTK3LEN2Hn3SLO3LFB3LOS4ALO12FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1AS1R1n4rawp3ACV3RCES2FBS2FBS1A1a1k2H3S1R3NS14STKg4STKs4STKf5STKg02sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS3sp13SP11a1k2H1S1A2FB4APPA1a1k2H12H2S1i2HiS2FB1c2HcS1R2lo3LOSS1R3HIA4FFRg4FFRj4CNTj4FFRf1h1n1d4FFRa2P24END22hc4HFRc4BFFR4BUDF3GNF3FF0S4rawp2P24END22C12p33Hp3FS2FBS3sp1S1AS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3SPRS3sp1S2FBS1n2FB4rawp4APRFFSS1R2FB2F2S1ASS2LB1n4rawp2P24END23LBc4C24g2CC2DMS2sp2r03SPA1q1r1H2H02q02H43sp14SP1M2FB3F641A3AALSS2FB1a1k2H3S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F11a1k2H1S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3HIA4STKg4STKs4STKf1h2sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS1a2HaS1AFS2FBS2sp3SPRFS1n2FB4rawp4APRFS1ASS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOSS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FB2F0S1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1FFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOFS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB3LOS3sp14rawp2P24END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C12C22C33ALO3RCES1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2P24END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2C12C22C33ALO3RCE2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO3ACV4SP1RS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2HB5Ha_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2HB5Ha_st5Hl_stS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R4STKg4STKs4STKf2LF1A1n2bs3LFB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HBS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_97978 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g12 g16 g18 g22 j32 alg : list byte)
      (rawp P2 END2 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s7v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 P2)) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P2 -> P2 <= END2 -> END2 <= rawp + n ->
    rawp <= dq -> 0 <= dlen -> dq + dlen <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) s3v s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) s7v (Z_to_bv 64 (A + 32)) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97f58) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA C1 C2 C3 Q1 Q2 Q3 BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (CWAc : client_wrange L (([(rawp, n)] ++ LB) ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { rewrite HTc. eapply client_wrange_mono; [exact CWA|]. intros b Hb. apply fdata_cons_sub. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WCA2 : wcover R ([(rawp, n)] ++ LB) LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    pose proof (blocks_below_hm R HIA hc _ _ mc ([(rawp, n)] ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) ([(rawp, n)] ++ LB)) by (left; reflexivity).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [BR BA].
    pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA RIN ltac:(left; reflexivity)) as APRF. cbn [fst snd] in APRF.
    rewrite Forall_forall in BR. ddestruct (BR (rawp, n) ltac:(apply in_or_app; left; exact RIN)) as (_ & _ & _ & RIMG). cbn [fst snd] in RIMG. clear BR BA.
    (* [comment removed for export] *)
    ddestruct (joint_0 n ltac:(clear - Hn; lia)) as (PJ0 & FJ0' & CJ0). pose proof (FJ0' (d + 1)) as FJ0. clear FJ0'.
    ddestruct (joint_g (END2 - P2) n ltac:(clear - C1 C2 C3 RP Hn; lia)) as (GNP & GNF' & GNC). pose proof (GNF' (d + 1)) as GNF. clear GNF'.
    pose proof (PHIf_mono 0 (CNTp n) ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as PF0.
    pose proof (FFRf_mono 0 (CNTp n) 0 ltac:(unfold A_pkcs7_parse_C.CNTp; clear - CJ0; lia)) as FF0.
    pose proof (presW_init_at R HIA hc _ _ ([(rawp, n)] ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    assert (WL2 : wlow R ([(rawp, n)] ++ LB) LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]).
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    splitat CELLS 11%nat CS2. splitat CS2 1%nat CS3.
    change (rw_cells asegs mc (A + 64) [CB 744 (zeros 744)]) in CS2.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. carve_frame 16%nat STlo. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 426584) with (Z_to_bv 64 (arl_amemset R)) by (rewrite AMS; reflexivity).
    lazymatch goal with H : rw_cells _ _ (A + 64) [CB 744 (zeros 744)] |- _ => apply (u8arr_of_rw_cells asegs) in H; rename H into ZC0 end.
    pose proof (artA_amemset asegs R HIA (arl_amemset R)) as SPM.
    acallxA_sp (sp1 + -16)
      (eapply SPM with (h := hc) (LB := ([(rawp, n)] ++ LB)) (LF := (FB, 256) :: LF) (DST := A + 64) (v := 0) (n := 744) (lo := lo) (ds := zeros 744); clear SPM;
         rewrite ?(unsigned_lit (sp1 + -16)) by (clear - SP1R SP1 SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia);
         first [ exact ZC0 | exact LOS | reflexivity
               | lazymatch goal with
                 | |- _ = arl_amemset R \/ _ => left; reflexivity
                 | |- HM _ _ _ hc _ _ _ => eassumption
                 | |- Z.of_nat (length (zeros 744)) = 744 => unfold zeros; rewrite repeat_length; reflexivity
                 | |- aobj _ _ _ ?mx (A + 64) 744 => lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) mx A 1440 |- _ => eapply aobj_sub; [exact OB| clear; lia| clear; lia] end
                 | |- 0 <= 0 < 256 => clear; lia
                 | |- stk _ _ lo _ => assumption
                 | |- lo <= _ - arl_need_amem R => clear - SLO SP1 NS1 NB0 NA0 NRT STKg0 STKs0 STKf0; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- mem_inv _ _ => assumption
                 | |- A + 64 + 744 <= lo \/ _ => left; clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                 | |- 744 = 0 \/ _ => right; clear - ASTK LOS SLO SPH NS1 STKg0 STKs0 STKf0; lia
                 | |- 744 < _ => clear; lia
                 | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_inside; [eapply client_wrange_sp_mono; [exact LOS| exact CWAc]| intros b Hb; exact Hb| clear; lia| clear; lia]
                 | |- _ <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                 end
               | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "MEMSET-LEFT:" g end.
    try clear SPM.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    lazymatch goal with H : u8arr _ m1 (A + 64) _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; change (Z.to_nat 744) with 744%nat in H;
                                                        change (repeat (Z_to_bv 8 0) 744) with (zeros 744) in H; rename H into ZC1 end.
    lazymatch goal with H : ?x = Z_to_bv 64 (A + 64) |- _ => subst x | _ => idtac end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with FRw : rw_cells _ m1 (sp1 + -16) _, STw : stk _ m1 lo (sp1 + -16) |- _ => release_frame FRw STw sp1; rename STw into ST1 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with HH : HM _ _ _ hc _ _ m1 |- _ => rename HH into HH1 end.
    lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) m1 A 1440 |- _ => rename OB into OBJ1 | _ => idtac "no OBJ1" end.
    lazymatch goal with MI : mem_inv _ m1 |- _ => rename MI into MI1 end.
    lazymatch goal with SS : sshad _ _ m1 slo (bv_unsigned sp) |- _ => rename SS into SS1 | _ => idtac "no SS1" end.
    assert (SIP1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))|].
      intros a Ha. exact (si_outside1 L SI A 1440 a AOD Ha). }
    clear SIc PRES2 WL2 WCA2.
    frame_aobj FSH (FB + 64) 1%nat as OPP.
    assert (CWP : client_wrange L (([(rawp, n)] ++ LB) ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) (FB + 64) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    lazymatch goal with PR : presW _ _ _ h LB LF _ _ X0 m m1 |- _ => rename PR into PRES end.
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKg0 STKs0 STKf0; lia].
        intros a Ha. cbn. split; [clear - Ha ASTK LOS SLO NS1 STKg0 STKs0 STKf0; lia| exact I]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    destruct (sshad_split asegs AL m1 slo sp1 (bv_unsigned sp) SS1 ltac:(clear - SP1 SLO SLOL NS1 STKg0 STKs0 STKf0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi]. clear SS1.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GETCERTS with (h := hc) (LB := ([(rawp, n)] ++ LB)) (LF := (FB, 256) :: LF) (PP := FB + 64) (P := P2) (END := END2) (BUF := rawp) (bs := bs)
                           (CRT := A + 64) (lo := lo) (slo := slo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold CRT_SIZE;
        first [ exact HH1 | exact HK1 | exact G8 | exact OPP | exact CWP | exact ZC1 | exact ST1 | exact SSlo | exact SLOS | exact SLOL | exact MI1 | exact TPV | exact SIP1 | exact C1 | exact C2 | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => unfold LFMAX_CRT; cbn [length]; clear - LFB; lia
                | |- bytes_at _ m1 rawp bs => lazymatch goal with RB : rw_cells _ m1 rawp _ |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                | |- In (rawp, Z.of_nat (length bs)) _ => rewrite LEN; exact RIN
                | |- List.NoDup _ => exact (HMND _ _ _ _ HH1)
                | |- aobj _ _ _ m1 (A + 64) _ => eapply aobj_sub; [exact OBJ1| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (A + 64) _ => eapply client_wrange_inside; [exact CWAc| intros b Hb; exact Hb| clear; lia| clear; lia]
                | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- (A + 64) mod 8 = 0 => clear - AAL; Z.div_mod_to_equations; lia
                | |- 0 < FB + 64 => clear - F0; lia
                | |- 0 < A + 64 => clear - A0; lia
                | |- 0 < rawp => exact RP
                | |- FB + 64 + 8 <= lo => clear - F1 ALO LOS; lia
                | |- A + 64 + 744 <= lo => clear - ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                | |- END2 <= rawp + Z.of_nat (length bs) => rewrite LEN; exact C3
                | |- rawp + Z.of_nat (length bs) < 2 ^ 47 => rewrite LEN; clear - RCE ACV; lia
                | |- Z.of_nat (length bs) < 2 ^ 30 => rewrite LEN; clear - Hn; lia
                | |- FB + 64 + 8 <= rawp \/ rawp + _ <= FB + 64 => rewrite ?LEN; clear - APRF; lia
                | |- A + 64 + 744 <= rawp \/ rawp + _ <= A + 64 => rewrite ?LEN; clear - RA; lia
                | |- FB + 64 + 8 <= hl_data_lo _ \/ _ => clear - F2; lia
                | |- A + 64 + 744 <= hl_data_lo _ \/ _ => clear - AOD; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia
                | |- FB + 64 + 8 <= A + 64 \/ _ => clear - APPA; lia
                | |- lo <= sp1 - STKg => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite ?HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold A_pkcs7_parse_C.PHIp in BUD; clear - BUD HVc BPHI GNP PF0; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold A_pkcs7_parse_C.FFRp in BUDF; clear - BUDF HFRc BFFR GNF FF0; lia
                | |- uwc _ m1 _ _ _ _ _ => rewrite HSc; exact UW1
                end
              | first [ (lazymatch goal with |- Z.of_nat (length bs) < AMAX => idtac end; rewrite LEN; unfold AMAX; clear - Hn; lia)
                    | (lazymatch goal with |- context [cnt24] => idtac end; cbn [app]; blk_norm_goal; pose proof (cnt24_cons_le (rawp, n) LB) as CC;
                       pose proof (Z.div_le_mono (END2 - P2) n 5889 ltac:(clear; lia) ltac:(clear - C1 C2 C3; lia)) as DM; clear - C24H CC DM; lia)
                    | match goal with |- ?g => idtac "GETCERTS-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2' & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3' & q4 & q5 & q6 & m4 & mo4 & h3 & r1 & p3 & f3 & j3 & LBc
                    & E4 & Ea0 & Hr1 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & HSUC3 & HPP4 & Hp3 & CA4 & PERM4 & ND4 & RAW4 & HH4 & SIP4 & C24g).
    injection E4 as Ems Emo. subst ms4 mo4x qa0.
    assert (C24x : cnt24 ((LBc ++ [(rawp, n)]) ++ LB) <= cnt24 LB + 1 + 2 * (n / 5889)).
    { rewrite <- app_assoc. cbn [app] in C24g |- *. blk_norm_in C24g. blk_norm_goal. pose proof (cnt24_cons_le (rawp, n) LB) as CC.
      pose proof (Z.div_le_mono (END2 - P2) n 5889 ltac:(clear; lia) ltac:(clear - C1 C2 C3; lia)) as DM. clear - C24g CC DM. lia. }
    replace (ret_pc (Z_to_bv 64 0x97f78)) with (Z_to_bv 64 0x97f78 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R. unfold CRT_SIZE in HP4.
    rewrite HTc in HT3. rewrite HSc in HS3, HP4. rewrite HFc in HF3.
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros xq Hx; apply HCS3, HCSc, Hx).
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (X0 ++ si_fp SI) m m4).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans.
      { eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros xq Hx. exact (proj1 (proj1 (outside_app _ _ xq) Hx)). }
      assert (HP4w : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) ((FB + 64, FB + 64 + 8) :: [(A + 64, A + 64 + 744)] ++ si_fp SI) m1 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros xq Hx; exact Hx]. }
      pose proof (presA_drop_fresh_gen R LB LF sp1 sp1 (hstkhi asegs R HIA h) ([(A + 64, A + 64 + 744)] ++ si_fp SI) FB 256 (FB + 64) (FB + 64 + 8) m1 m4 HP4w FRSH
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - F1 FBLO SP1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as HP4d.
      eapply presA_weaken; [exact HP4d| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia|].
      intros xq Hx. apply (proj2 (outside_app _ _ xq)). pose proof (proj1 (outside_app _ _ xq) Hx) as [Hx0 Hx1].
      split; [cbn [outside] in Hx0 |- *; clear - Hx0; lia| exact Hx1]. }
    clear PRES.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    pose proof (art_data_lo asegs R HIA) as DLOW.
    assert (DJF : forall a k, FB <= a -> a + k <= FB + 256 -> (a + k <= FB + 64 \/ FB + 72 <= a) -> disjoint_from ([(FB + 64, FB + 64 + 8); (A + 64, A + 64 + 744)] ++ si_fp SI) a k).
    { intros a k H1 H2 H3. apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn; split; [clear - H3; lia| split; [clear - H1 H2 APPA; lia| exact I]]|].
      apply (si_disjoint_off L SI). clear - H1 H2 F2. lia. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from ([(FB + 64, FB + 64 + 8); (A + 64, A + 64 + 744)] ++ si_fp SI) a k).
    { intros a k H1. apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn; split; [clear - H1 F1 ALO LOS SP1 SLO NS1 STKg0 STKs0 STKf0; lia| split; [clear - H1 ASTK LOS SP1 SLO NS1 STKg0 STKs0 STKf0; lia| exact I]]|].
      apply (si_disjoint_off L SI). right. clear - H1 DLOW ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0. lia. }
    assert (DJA : forall a k, A <= a -> a + k <= A + 1440 -> (a + k <= A + 64 \/ A + 808 <= a) -> disjoint_from ([(FB + 64, FB + 64 + 8); (A + 64, A + 64 + 744)] ++ si_fp SI) a k).
    { intros a k H1 H2 H3. apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn; split; [clear - H1 H2 APPA; lia| split; [clear - H3; lia| exact I]]|].
      apply (si_disjoint_off L SI). clear - H1 H2 AOD. unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *. lia. }
    assert (CRsub : forall a k, A <= a -> a + k <= A + 1440 -> client_range L (([(rawp, n)] ++ LB) ++ fdata ((FB, 256) :: LF)) sp1 a k).
    { intros a k H1 H2. apply (client_range_lower L _ lo sp1 a k); [| clear - H2 ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia].
      eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| exact H1| exact H2]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) ([(rawp, n)] ++ LB) ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 64, FB + 64 + 8); (A + 64, A + 64 + 744)] ++ si_fp SI) m1 m4 FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in STa; [| clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in SShi; [| clear; lia| clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m4 slo sp1 (bv_unsigned sp) SS4 SShi ltac:(clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia)) as SSm4. clear SS4 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in CELLS; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in CS3; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    lazymatch goal with RB : rw_cells _ m1 rawp _ |- _ =>
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m4 _ _ HP4) in RB;
      [ rename RB into RAWB4
      | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia]
      | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); apply (proj2 (SInv.disjoint_from_app _ _ _ _)); split;
        [cbn; split; [clear - APRF; lia| split; [clear - RA; lia| exact I]] | apply (si_fp_disjoint_offimg L SI); [exact RIMG| exact (proj1 DIMG)| exact (proj2 DIMG)]] ] end.
    assert (OBJ4 : aobj asegs AL CS m4 A 1440).
    { eapply presA_aobj0; [exact CSOK| exact HP4| exact OBJA| intros xq Hx; eapply hcs_below_top; exact Hx| right; split; [apply CRsub; clear; lia| clear; lia]]. }
    clear OBJA OBJ1 ZC1 MI1 ST1 HP4 G8 OPP CWP UW1.
    ddestruct CA4 as (CC4 & _ & _ & _ & OWN4).
    assert (SZ744 : cells_size (crt_cells f3 j3) = 744%nat) by reflexivity.
    pose proof CC4 as CC4b. apply rw_cells_blob in CC4b. rewrite SZ744 in CC4b.
    assert (OAPc : forall B k, In (B, k) (crt_blocks f3) -> 0 < k -> B + k <= A \/ A + 1440 <= B).
    { intros B k Hb Hk.
      eapply (obj_apart_new R HIA h3 LBc ([(rawp, n)] ++ LB) LF ((FB, 256) :: LF) m4 lo (htop asegs R HIA h) A 1440 B k DIMG);
        [exact HH4| intros fb Hfb; right; exact Hfb| | clear - ALO LOS; lia| clear; lia| eapply Permutation_in; [apply Permutation_sym; exact PERM4| exact Hb]| exact Hk].
      eapply client_wrange_mono; [exact CWA|]. intros b Hb'. apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; exact Hb'| right; exact Hb']. }
    (* [comment removed for export] *)
    joinr CC4b CS3. joinr CELLS CC4b.
    pose proof HPP4 as G8'. apply rw_cells_blob in G8'. cbn [cells_size csize cells_bytes cbytes app Nat.add] in G8'. rewrite ?app_nil_r in G8'.
    (* [comment removed for export] *)
    set (c1 := if 0 <=? r1 then p3 - P2 else END2 - P2).
    assert (CX : havol asegs R HIA h3 <= havol asegs R HIA hc + PHIg c1 /\ hfr asegs R HIA h3 <= hfr asegs R HIA hc + FFRg c1 (d + 1)
                 /\ Z.of_nat (length LBc) <= CNTg c1 /\ 0 <= c1 /\ c1 <= n /\ (0 <= r1 -> c1 + (END2 - p3) <= n)).
    { subst c1. destruct (Z.leb_spec 0 r1) as [RP1|RN1].
      - ddestruct (HSUC3 RP1) as (U1 & U2 & U3). split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. clear - Hp3 C1 C2 C3 RP Hn. lia.
      - split; [exact HV3|]. split; [exact HFR3|]. split; [exact HCNT3|]. clear - Hp3 C1 C2 C3 RP Hn RN1. lia. }
    ddestruct CX as (CX1 & CX2 & CX3 & C10 & C1n & C1S).
    assert (HV4' : havol asegs R HIA h3 <= havol asegs R HIA h + (PHIa + PHIg c1)) by (clear - CX1 HVc; lia).
    assert (HFR4' : hfr asegs R HIA h3 <= hfr asegs R HIA h + (FFRa + FFRg c1 (d + 1))) by (clear - CX2 HFRc; lia).
    (* [comment removed for export] *)
    change (Z * Z)%type with blk in HH4. change (Z * Z)%type with blk in OWN4.
    rewrite (app_assoc LBc [(rawp, n) : blk] LB) in HH4. rewrite (app_assoc LBc [(rawp, n) : blk] LB) in OWN4.
    eapply (from_97990 FB sp1 (PHIa + PHIg c1) (FFRa + FFRg c1 (d + 1)) w0 w1 w2 v48 v80 g4 g12 g16 g18 g22 j32 alg rawp p3 END2 r1 rt p0 ver vp dtg dpad dlen dq
              j56 q2 q3 sj0 f3 j3 m4 LBc m4 mo4 h3) with (c1 := c1);
      first [ exact C10 | exact C1n | exact C1S | exact CX3 | exact CC4 | exact RAWB4 | exact RP | exact RA | exact OWN4 | exact PERM4 | exact OAPc | exact RAW4 | exact C3 | exact Q1 | exact Q2 | exact Q3 | exact Hr1 | exact BUD | exact BUDF | exact UW
            | lazymatch goal with
              | |- rawp <= p3 <= END2 => clear - Hp3 C1; lia
              | |- PHIa + PHIg _ <= _ => clear - BPHI; lia
              | |- FFRa + FFRg _ (d + 1) <= _ => clear - BFFR; lia
              | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  split; [exact HH4|]; split; [exact HK3|]; split; [eapply mo_frame_trans; [exact MFc| eapply mo_frame_trans; [exact MF1| exact MF4]]|];
                  split; [exact HT3|]; split; [exact HS3|]; split; [exact HF3|]; split; [exact HCSh3|]; split; [exact HV4'|]; split; [exact HFR4'|];
                  split; [exact PRESb|]; split; [exact SIP4|];
                  repeat match goal with |- _ /\ _ => split end;
                  first [ exact G8' | exact CELLS | exact OBJ4 | eassumption | reflexivity
                        | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                        | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA4-LEFT:" g end ] ]
              end
            | match goal with |- ?g => idtac "F9768C-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
