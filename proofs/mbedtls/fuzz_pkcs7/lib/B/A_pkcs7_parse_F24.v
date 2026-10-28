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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24 A_pkcs7_parse_C24 A_pkcs7_parse_D24 A_pkcs7_parse_E24.
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
Local Ltac zchk_new ::= constr:([622624; 622628; 622632; 622636; 622640]).
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
  Hypothesis NA0 : 0 <= arl_need_amem R.
  Hypothesis NB0 : 0 <= arl_need_bcmp R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35674842593.52000007S1R3NA0". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L15273424461.10800000dS1R2LF2sp1A1n2lo3slo2bs2A03LEN2Hn4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
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

  Local Notation rep_buildE := (rep_build R PK STKg STKs STKf LB LF sp A n lo slo bs AAL A0 ASTK LEN Hn SLOS SLOL SLO LFB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L1954413818.119 L2192452093.118 L22676661558.119L32883993289.122L38339916114.122L53197855842.119L58186465473.12200000]01F01o02b03L04<04lS2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz3HB02H12HLS2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz2H12H3S2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz2H22HLS2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz2H12H32HL1i2Hi1HS2LF2sp1A1n2bs3LFB2mX1B3bsx1P2Lz2HL1i2Hi1HS2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz3HB12H22H32HLS2LF2sp1A1n2bs2A02Hn3LFB1B3bsx1P2Lz2H12HL1i2Hi1H". (* [comment removed for export] *)
  Lemma bytes_at_slice : forall mX B bsx P Lz, bytes_at asegs mX B bsx -> B <= P -> 0 <= Lz -> P + Lz <= B + Z.of_nat (length bsx) ->
    bytes_at asegs mX P (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P - B)) bsx))
    /\ Z.of_nat (length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P - B)) bsx))) = Lz.
  Proof using LF sp A n bs A0 Hn LFB.
    (intros mX B bsx P Lz dd_H; ddestruct dd_H as (HB0 & HB1 & HB); intros H1 H2 H3).
    assert (HL : length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P - B)) bsx)) = Z.to_nat Lz).
    { rewrite firstn_length, skipn_length. lia. }
    split; [| rewrite HL; lia]. split; [lia|]. split; [rewrite HL; lia|].
    intros i Hi. rewrite HL in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat Lz)); [| lia].
    rewrite nth_error_skipn. rewrite <- (HB (Z.to_nat (P - B) + i)%nat) by lia. f_equal. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="R STKg STKs STKf LF sp lo slo AAL A0 ASTK LEN Hn SLOS SLOL SLO LFB"] Lemma rep0_build : forall mX (rt p0 ver vp dtg dpad : word) (rawp dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk),
    rw_cells asegs mX A ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
                         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0) ->
    rw_cells asegs mX rawp [CB (Z.to_nat n) bs] -> 0 < rawp ->
    pkcs7_at asegs PK (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                             P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs))
             mX [(rawp, n)] LB A.
  Proof.
    intros until sj0. intros HC RC RP.
    ddestruct (rw_cells_split3 asegs mX A ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])
                [CB 744 (zeros 744)] ([CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0) HC) as (H1 & H2 & H3).
    cbn [cells_size csize Nat.add length buf_cells app] in H2, H3. change (A + Z.of_nat 64) with (A + 64) in H2, H3. change (Z.of_nat 744) with 744 in H3.
    pose proof (rw_cells_zeros asegs mX (A + 64) 744 _ H2 crt_cells_zero eq_refl) as CZ.
    eapply (rep_buildE mX [(rawp, n)] rt p0 ver vp dtg dpad rawp dlen dq [CB 8 j56] [CB 8 q2] [CB 8 q3] crt_own_zero crt_junk_zero 0 0 sj0 [] []);
      [| reflexivity| reflexivity| reflexivity| exact RC| exact RP| left; reflexivity| apply crt_own_ok_zero| apply chain_nil| reflexivity| | ].
    - apply (crt_unblob_mid A mX mX ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])
                            ([CB 8 q2] ++ [CB 416 (zeros 416)] ++ [CB 8 q3] ++ signer_cells 0 0 sj0) crt_own_zero crt_junk_zero CZ eq_refl).
      apply rw_cells_join3; [exact H1| | ].
      + cbn [cells_size csize Nat.add length buf_cells app]. change (A + Z.of_nat 64) with (A + 64). apply rw_cells_blob in CZ. exact CZ.
      + cbn [cells_size csize Nat.add length buf_cells app]. change (A + Z.of_nat 64) with (A + 64). exact H3.
    - rewrite crt_blocks_zero. cbn. apply Permutation_refl.
    - cbn. constructor; [intros []| constructor].
  Qed.

  (* [comment removed for export] *)
  Ltac blob8 H := apply rw_cells_blob in H; cbn [cells_size csize cells_bytes cbytes app Nat.add] in H; rewrite ?app_nil_r in H.

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
  Ltac exitF rr TPX SM0 HKc MFc Hr RP :=
    repeat (lazymatch goal with |- context [MS _ _ (Z_to_bv 64 621224) _ _ _ _] => fail | |- _ => zstep end);
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      lazymatch goal with CE : rw_cells _ mx A [C4 ?rt; C4 ?p0; C8 (Z_to_bv 64 _); C8 (Z_to_bv 64 ?rawp); C4 ?ver; C4 ?vp; C4 ?dtg; C4 ?dpad; C8 (Z_to_bv 64 ?dlen); C8 (Z_to_bv 64 ?dq);
                                        CB 8 ?j56; CB 744 (zeros 744); CB 8 ?q2; CB 416 (zeros 416); CB 8 ?q3; CB 80 (RepCrt.sj0 ?sj); C8 _; C1 _; CB 7 _; CB 96 _; C8 _],
                      RB : rw_cells _ mx ?rawp' [CB _ bs] |- _ =>
        let REPx := fresh "REPx" in
        assert (REPx : pkcs7_at asegs PK (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                               P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj bs)) mx [(rawp, n)] LB A)
          by (apply (rep0_build mx rt p0 ver vp dtg dpad rawp dlen dq j56 q2 q3 sj); [unfold buf_cells, signer_cells; cbn [app]; exact CE| exact RB| exact RP]);
        repeat match goal with H : rw_cells _ mx (?FB + 64) [C8 _] |- _ => blob8 H | H : rw_cells _ mx (?FB + 96) [C8 _] |- _ => blob8 H end;
        lazymatch goal with RS : rw_cells _ mx (?sp1 + 16) _, AL' : rw_cells _ mx (?sp1' + 56) _, SE' : rw_cells _ mx (?sp1'' + 80) _ |- _ =>
          apply rw_cells_blob in AL'; cbn [cells_size csize Nat.add] in AL'; joinr RS AL'; joinr RS SE' end;
        si_now;
        let mo9 := fresh "mo9" in let HK9 := fresh "HK9" in let MF9 := fresh "MF9" in
        intros mo9 [HK9 MF9]; pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'; clear HKc MFc;
        lazymatch goal with HHx : HM _ _ _ ?hc _ _ mx, HVx : havol _ _ _ _ <= havol _ _ _ _ + ?PHIa, HFRx : hfr _ _ _ _ <= hfr _ _ _ _ + ?FFRa |- _ =>
        eapply (tail_97504 R HIA) with (STKg := STKg) (STKs := STKs) (STKf := STKf) (bs := bs) (W := [(A, A + 1440)]) (PHIa := PHIa) (FFRa := FFRa) (Lc := [(rawp, n)]) (hc := hc) (r := rr);
          first [ exact (TPX _ _ REPx SM0) | eassumption
                | lazymatch goal with |- - 2 ^ 31 <= _ < 2 ^ 31 => first [clear; lia | clear - Hr; lia] end
                | (cbv beta; dvA_build) ]
        end
      end end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L40228640085.0 L40798716262.1600000100JSS1r2Hr1q2r02r11H2H02q02H4".
  #[using="Type"] Lemma addw_err5480 : forall r, -127 < r <= 0 ->
    bv_swrap 32 (Z.land r 18446744073709551615 + 18446744073709529984) = r + -21632.
  Proof.
    intros r Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia).
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
    clear - Hr. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0570@C17025492443.303C18973515383.326C23920765559.325D11893914196.326D16069757090.326D16899842714.326D27847976046.303D45723329834.326D50626680719.326D56538493012.326D5982099855.326 D60109446735.303D6362079018.326 K13147051614.326K21212095580.303K22863142806.326K49776690270.326K55088519473.303K63418475926.326L10377779059.1  L10472353826.312L10762500794.4  L10894997063.3  L10912730231.1  L109174781.4    L1108448139.280 L12195957072.19 L12886541299.1  L13141122540.2  L13176305223.2  L13340048728.1  L13601556081.2  L15042694813.7  L16467427964.269L16467427964.292L16467427964.314L16467427964.318L16668540544.223L16668540544.316L16729185788.269L18023395959.1  L18302214263.1  L19980016842.7  L20166242178.3  L20690421408.1  L21007906567.2  L21218866939.2  L21644325741.3  L21653067913.301L21654730866.2  L216852546.4    L22191044377.2  L22860483030.3  L23389044221.4  L2424960062.2   L24817214193.2  L25160623805.2  L2534192221.4   L25789285751.1  L2621559066.1   L27280244015.1  L27940405558.13 L28442841414.2  L29010569984.268L29066840183.1  L29345674871.1  L30827914234.223L31852292097.2  L31947286927.291L31947286927.317L32327136116.1  L33312313103.2  L33817424237.3  L34783991938.3  L35110622472.11 L35666023782.15 L36181700215.1  L36308544528.280L36460502135.1  L37663591692.9  L37940357415.0  L38110372910.4  L38235734261.1  L38738405142.1  L39240359025.2  L39348637477.0  L39631162845.2  L39836337748.223L39836337748.316L39836419797.317L40228640085.0  L40253556363.2  L40301035635.20 L40447859511.14 L40493076153.3  L41409160545.3  L41663468825.291L41663468825.317L41898327682.3  L42139611770.2  L42359347016.0  L42609104409.291L43300649301.0  L43810982283.2  L46290454573.5  L46710299783.5  L46745494493.3  L47046946167.3  L47870616696.2  L49028543392.1  L49739481329.2  L49761849324.2  L49939585185.0  L50790731766.15 L50798508407.1  L50925318027.2  L51047916864.223L51074967415.1  L52654123303.0  L52892334950.1  L52895316838.2  L52941874306.3  L53519090864.316L53527181501.2  L53910107169.291L53910109749.317L55085943702.3  L55842747208.3  L57048425585.3  L57124690773.0  L57611209309.2  L57951117045.3  L58650166718.223L58718842998.5  L58790154276.15 L59308586248.2  L59308633210.3  L60016383950.223L60056205954.3  L60098763854.6  L6031628760.2   L60448817524.1  L61004000883.20 L61366595865.317L62586290822.10 L63373084206.4  L63420085206.3  L63613504898.3  L63901643096.1  L64267954266.4  L64406477449.3  L64513097329.3  L64526681523.2  L64850595401.0  L65121026222.268L65258828961.0  L65526290571.2  L65768422677.2  L65770151573.1  L66151426447.10 L66151427842.16 L66298372189.2  L6659335921.2   L66925259772.300L6704320638.6   L67653551064.1  L67897887985.2  L67977350524.268L68272074258.8  L7049614941.2   L7356357495.1   L8274820260.8   L8454980662.21  L8742280115.2   L881835912.0    L9080220944.4   L9243719951.2   L9356559676.20  O11532716922.326O11932660720.324O1473384442.323 O1478916974.303 O1596938092.326 O17025492443.303O20300933498.326O21469769210.326O21804719164.326O24872904570.326O28722692754.303O3076189820.323 O32535777404.323O33649476986.326O33992938518.326O35590701227.326O36520195031.303O37051008023.303O37526595730.303O4013719057.303 O44940300031.324O45967443052.326O47761277330.303O47806715794.303O4831476988.326 O50702732434.303O50713881329.303O526338812.326  O54759041018.326O55211981985.324O55516142064.324O55712217697.326O56414299794.303O59625529265.303O6010750458.323 O6120109628.326 O61466163795.326O63902264854.326O64471909102.326O65963309676.324O67168963243.326O8260999532.326 O8602651585.326 P101289150.326  P10761940190.303P10897630432.303P13597906162.326P20181466405.303P21212095580.303P21656429038.324P22185289150.303P23396888254.326P24829259890.326P25156940862.323P33812653038.324P34789739045.303P39227264754.326P40257213448.326P41419110342.303P41905122341.303P42135953657.326P43815688968.326P46717128672.303P47045409591.326P47874275067.324P49735832178.326P50930023688.324P52940256805.303P53531847230.323P57052051186.323P60050384933.303P63606742821.303P64259062553.326P64517795058.323P64541068801.326P65521519112.326P66294657758.326P6646248562.326 P67910983282.326P8756727809.326 Q12683804246.303Q13394320958.276Q15766564435.303Q17064172330.324Q17977530286.326Q19405359842.275Q19561563123.301Q19561597574.300Q20615001507.276Q21765573510.326Q21834833659.326Q21913096220.321Q21913097494.325Q21913097623.276Q21913098889.276Q21913099655.299Q22137998202.301Q23161606555.326Q23611221436.326Q27944551349.326Q2805923721.326 Q29778078658.326Q32435106995.326Q33135353571.326Q34359956804.326Q34667424921.326Q34669522109.298Q34671339340.300Q34673389371.324Q34964382778.303Q36856420847.303Q38248387216.303Q41259827082.324Q41263692812.298Q41412201211.326Q42439168719.303Q42441265899.326Q48120161967.326Q48360113622.303Q522258730.324  Q52968037308.326Q535169708.298  Q53797085571.326Q53876633983.275Q56389205783.303Q58741773977.326Q58746442809.301Q58748523835.324Q59865603600.303Q59867700788.326Q62622133678.326Q64681845186.326Q64683942374.303Q7366556695.324 Q7379074961.298 Q7526555924.276 Q7526557210.299 Q7526558593.321 Q7526559242.276 Q7526559371.325 Q7757884431.300 Q8360723123.326 Q9090756535.303 Q9356559660.283 Q9356756743.303 Q9633850233.300 Q9634015756.301 Q9644583048.303 Q9646680236.326 00000100500901Z04<06V0930:T0:U0<60<70=_0?@0AF0AG0DF0FL0Go0Jn0K30K40K50K60K70K80LY0MP0MU0MV0M^0Mc0Md0N>0O]0Q>0R_0T@0VN0YO0Zn0[20[30[K0[L0[Q0[W0[X0[Y0]:0];0]J0]K0]L0]M0]S0]T0]U0]e0]i0]n0^20^V0^^0^_0^c0^g0_\0_b0aC0bd0bh0bo0c00c10cW0d<0d@0ea0ee0fK0fL0f\0f`0fc0fd0fe0fm0iC0lL0oU0oV0oW10W11G11O11P13114R14S14T14U17G17H17I17[17\17g17h17i17n17o18018118_18c18d1:^1:b1:c1:d1:j1:k1<L1<M1?B1BO1BP1B\1B]1B^1Bf1C31Df1E61Eh1En1F51F61F71FA1FI1FM1GM1Hn1I?1IO1IP1IQ1IV1IW1I_1I`1Ia1Ib1L91L:1L;1LC1LD1LT1M71M81M91NZ1O11O61O71PV1Q:1QB1QF1Qb1Rg1Rh1Ri1S81S?1T=1T>1T?1T@1TA1TB1TC1TD1TE1TF1TG1TH1TI1TJ1TK1TL1TM1TN1TO1TP1TQ1TR1TS1TT1TU1TV1TW1TX1TY1TZ1U>1U?1U@1UA1UB1UC1UD1UE1UF1UG1UH1UI1UJ1UK1XU1[81\[1_31`W1`X1b<1cg1g11iN1kk1mO1o321K23h25L27029J2;g2>P2AH2C`2F=2HZ2J>2L[2O32PW2R;2U92WQ2Yf2\C2]c2`;2bS2dh2fG2hE2j:2kR2kS2mQ2o<30g32H34Z3623823:23<03=n3?n3AF3C[3E33G33HL3Il3Im3KP3KQ3Li3NA3OY3Q13S13S23TJ3Um3WP3Xh3ZF3[d3]n3_Q3`i3bA3cY3cZ3e;3e<3fT3gl3iD3iE3iF3iG3kE3mC3oC41C42d44G45j47K48n4:F4:G4;j4=H4>f4@A4A\4C74DRFS2FBS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1RS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2p'2se1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC4APPA3x183x313x323x335POST0FS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC2C12C34APRF2Hq3Hqp3Hse2L92NE3x183x313x323x335POST0S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB2FB3sp14rawp2p'2se1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC4APPA3x183x313x323x335POST0S1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC2C12C34APRF2Hq3Hqp3Hse2L92NE3x183x313x323x335POST0S3sp1FFFFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R1n2lo3LOS4rawp1P4END22p'3len1q2C33Hp'3ALO3RCE3Hqp2L9S3sp1FS2lo3sp1S3sp1FS1n4rawp4END22p'2se2C33HseS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P4END22p'2se3len1q2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323PC43GP2S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323PC43GP2S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBFS1R3HIA1h2sp3TOP3sp13SP1FS3sp1S1n2HnFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1P4END22p'3Hp'FFFS1n2HnFFS4END22p'2se3HseS2FBS3sp1S2FBS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S3len2KLFS2FBS2FBS1R4STKg4STKs4STKf2sp1A1n2bs2FB3sp14rawp1q3x323x332LRS1n2HnS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS2FB2F0FFS1n4rawp1P4END22p'3len1q2C33Hp'3Hqp2L9S1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS2FBS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2FBS4FFRj4CNTj4FFRf1n1d4FFRa4BFFR3FJ03FFmSS1n2FB4rawp4APRFS2loS1AFSS2lo3sp1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P4END22p'2se3len1q2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323x333GP24GLEN2LRS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323x333GP24GLEN2LRS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323x333GP24GLEN2LRSFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S1R1n4rawp1P4END22p'3len1q2C33Hp'3ACV3RCE3Hqp2L9S2r33Hr3FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFSS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33Hp'3ACV3SPR2F04SP1R3RCE2Hq3Hqp2L9SFS1R1n4rawp3ACV3RCEFS2sp2lo3sp1FFS3sp1FFSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS2FBFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2p'3len1q2RP2C13SPR2F04SP1R2Hq3Hqp2L93x323x333GP22LRS2FBSFS1r2HrFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L9S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2RP2C12C33ACV3SPR2F04SP1R3RCE2Hq3Hqp3Hse2L93x323x333PC43GP24GLEN2LRFS4CNTj1n3CJ0FSS2lo3sp1S4CNTj1n4CNT1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2sp1A1n2bs2A02Hn2FB3sp14rawp1P2p'3len1q2RP2C13SPR2F04SP1R2Hq3Hqp2L93x323GP2S4rawp1P1q2C12HqS1R3NS14STKg4STKs4STKf5STKg03NRT2sp2lo3SLO3sp13SP1S1i2HiS2r32KWFFS1R2lo3LOSS2sp3sp1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS2r33Hr31r2KT1q1HS1n2FB4rawp4APRFFFS3sp1FS2r33Hr3FFSS1R4STKg4STKs4STKf2LF2sp1A1n2bs2A02Hn3LFB2FB3sp14rawp1P4END22p'3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C12C33Hp'3SPR2F04SP1R2Hq4Hlen3HqpSFS2r33Hr3FS1r2Hr2r02KR1q1HS2FB2r03F641q1r1H2H02q02H43sp14SP1MFFS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4rawp1P4END22p'2C13Hp'S3sp1FS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS4PHIj4CNTj4PHIf1n4PHIa4BPHI3PJ03PFmS2lo3sp1S2FBS1R2lo3slo4SLOS4SLOL3ALO3ACVS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCEFSS2sp2lo3sp13SP1S2FB2F0S1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1FFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs2Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC2RA2C12C34APPA4APRF2Hq3Hqp3Hse2L94QLEN2NE3x183x313x323x335POST0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp1P4END22p'3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C12C33Hp'3ALO3RCE2Hq3Hqp2L9S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO3ACVS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1A1n2lo2bs2Hn3LFB2FB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03x303SZC2RA2C12C34APPA4APRF2Hq3Hqp3Hse2L94QLEN2NE3x183x313x323x335POST0S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C33Hp'3ALO3RCE3Hqp3Hse2L94QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1P4END22p'3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2C12C33Hp'3ALO3RCE2Hq3Hqp2L9S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLOS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1P4END22p'2se3len1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2C33Hp'3ALO3RCE3Hqp3Hse2L94QLENS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F1S1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO4FBLO2F1S1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F0S1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALOS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALOS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HTS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZCFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZCS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp14rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1RS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0S1R4STKg4STKs4STKf2LF1n2bs3LFB2FB4rawp1q2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F0". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_9790c : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 : word) (g4 g12 g16 g18 g22 j32 : list byte)
      (rawp P END2 r p' se : Z) (tg pad : word) (len q : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 p')) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48
        (cells_bytes (buf_cells tg pad len q)) (Z_to_bv 64 se)
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P -> P <= END2 -> END2 <= rawp + n ->
    rawp <= dq -> 0 <= dlen -> dq + dlen <= rawp + n ->
    -0x5600 < r <= 0 -> P <= p' <= END2 ->
    (r = 0 -> tg = Z_to_bv 64 6 /\ P + 4 <= q /\ 0 <= len /\ q + len = p' /\ p' <= se <= END2) ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (A + 32)) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97ef0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA C1 C2 C3 Q1 Q2 Q3 Hr Hp' HOK BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    pose proof (blocks_below_hm R HIA hc _ _ mc ([(rawp, n)] ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    assert (RIN : In (rawp, n) ([(rawp, n)] ++ LB)) by (left; reflexivity).
    assert (RCE : rawp + n <= alloc_ceiling) by (destruct (BBc _ RIN) as [_ Bce]; exact Bce).
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ BA].
    pose proof (blocks_apart_app2 _ _ (rawp, n) (FB, 256) BA RIN ltac:(left; reflexivity)) as APRF. cbn [fst snd] in APRF. clear BA.
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc rawp n HHc RIN) as OBUF.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of HHc with HM _ _ _ _ ?LB2 _ _ =>
      pose proof (presW_init_at R HIA hc _ _ LB2 LF mc (bv_unsigned sp) (bv_unsigned sp) X0 h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2;
      assert (WL2 : wlow R LB2 LF) by (split; [exact (proj2 (proj2 (proj2 PRES2)))| apply (art_data_lo asegs R HIA)]);
      assert (WCA2 : wcover R LB2 LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia)
    end.
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
      split; [intros x9 Hx; exact (proj1 (proj1 (outside_app _ _ x9) Hx))|]. split; [intros x9 Hx; exact Hx|]. exact (conj BUD BUDF). }
    assert (SM0 : p7small (Some (P7O n rawp crt_own_zero 0 [] 0 [],
                                 P7J rt p0 (cells_bytes ([C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56])) crt_junk_zero (cells_bytes [CB 8 q2]) (cells_bytes [CB 8 q3]) sj0 bs))).
    { cbn. clear - Hn. lia. }
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    cb8_to_c8 G12 (@nil cell).
    splitat RSL 4%nat ALG. splitat ALG 1%nat SE.
    pose proof (rw_cells_reshape asegs _ _ _ (buf_cells tg pad len q) ALG ltac:(cbn; repeat split; exact I) ltac:(symmetry; exact (app_nil_r _))) as ALG'. clear ALG. rename ALG' into ALG.
    unfold buf_cells in ALG.
    pose proof (conj CELLS I) as CELLbox. (* [comment removed for export] *)
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KR; zify_cond KR.
    { (* [comment removed for export] *) exitF r TPX SM0 HKc MFc Hr RP. }
    assert (R0 : r = 0).
    { change 18446744073709551615 with (Z.ones 64) in KR. rewrite ?Z.land_ones in KR by (clear; lia). clear - KR Hr. Z.div_mod_to_equations. lia. }
    subst r. ddestruct (HOK eq_refl) as (Etg & Hq & Hlen & Hqp & Hse). subst tg. clear HOK KR Hr.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *) exitF (-21632) TPX SM0 HKc MFc Hr RP. }
    assert (L9 : len = 9).
    { change 18446744073709551615 with (Z.ones 64) in KL. rewrite ?Z.land_ones in KL by (clear; lia). rewrite ?Z.mod_small in KL by (clear - Hlen Hqp Hp' C1 C2 C3 RP RCE ACV; lia). clear - KL. lia. }
    clear KL.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 362244) with (Z_to_bv 64 (arl_memcmp_i R)) by (rewrite MCI; reflexivity).
    pose proof (hcs_img_cs R HIA hc IMG (proj2 (proj2 (proj2 IMG')))) as ICS. pose proof (hm_img_shadow asegs R HIA) as ISH.
    destruct (bytes_at_slice _ rawp bs q 9 (cb_bytes_at _ _ _ _ RAWB) ltac:(clear - Hq C1; lia) ltac:(clear; lia) ltac:(rewrite LEN; clear - L9 Hqp Hp' C3; lia)) as [QBY QLEN].
    ro_str 0x24d40 9%nat as ROS. img_aobj 0x24d40 9 as ORO.
    pose proof (artA_bcmp asegs R HIA) as SPB.
    lazymatch type of QBY with bytes_at _ _ _ ?qqs =>
    acallxA_sp sp1
      (eapply SPB with (h := hc) (LB := ([(rawp, n)] ++ LB)) (LF := (FB, 256) :: LF) (P := 0x24d40) (Q := q) (n := 9) (lo := lo) (qs := qqs); clear SPB;
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact ROS | exact QBY | exact ORO | exact QLEN | exact LOS | reflexivity
               | lazymatch goal with
                 | |- HM _ _ _ hc _ _ _ => eassumption
                 | |- aobj _ _ _ _ q 9 => lazymatch goal with OB : aobj _ _ (hcs asegs R HIA hc) _ rawp n |- _ => eapply aobj_sub; [exact OB| clear - Hq C1; lia| clear - L9 Hqp Hp' C3; lia] end
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- lo <= sp1 - arl_need_bcmp R => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- 150848 + 9 <= lo \/ _ => left; clear - ACV ALO LOS; lia
                 | |- q + 9 <= lo \/ _ => left; clear - L9 Hqp Hp' C3 RCE ALO LOS; lia
                 | |- 9 = 0 \/ 150848 + 9 + 8 <= _ => right; clear; lia
                 | |- 9 = 0 \/ q + 9 + 8 <= _ => right; clear - L9 Hqp Hp' C3 RCE ACV; lia
                 | |- 9 < _ => clear; lia
                 | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                 end
               | match goal with |- ?g => idtac "BCMP-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "BCMP-LEFT:" g end.
    try clear SPB. try clear ROS ORO.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *) exitF (-21632) TPX SM0 HKc MFc Hr RP. }
    clear KB.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *)
      assert (EQ : p' = se).
      { change 18446744073709551615 with (Z.ones 64) in KE. rewrite ?Z.land_ones in KE by (clear; lia).
        rewrite ?Z.mod_small in KE by (clear - Hse Hp' C1 C2 C3 RP RCE ACV; lia). exact KE. }
      subst se. try clear KE. try clear EQ.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
        repeat match goal with H : rw_cells _ mx (FB + 64) [C8 _] |- _ => blob8 H | H : rw_cells _ mx (FB + 96) [C8 _] |- _ => blob8 H end;
        lazymatch goal with RS : rw_cells _ mx (sp1 + 16) _, AL' : rw_cells _ mx (sp1 + 56) _, SE' : rw_cells _ mx (sp1 + 80) _ |- _ =>
          apply rw_cells_blob in AL'; cbn [cells_size csize Nat.add] in AL'; joinr RS AL'; joinr RS SE' end end.
      si_now.
      intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
      destruct CELLbox as [CELLS0 _].
      eapply (from_97978 R HIA) with (C24c := C24c) (STKg := STKg) (STKs := STKs) (STKf := STKf) (PHIg := PHIg) (FFRg := FFRg) (CNTg := CNTg) (PHIs := PHIs) (FFRs := FFRs) (CNTs := CNTs) (bs := bs) (PHIa := PHIa) (FFRa := FFRa) (hc := hc) (rawp := rawp) (P2 := p') (END2 := END2)
                                     (rt := rt) (p0 := p0) (ver := ver) (vp := vp) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (j56 := j56) (q2 := q2) (q3 := q3) (sj0 := sj0);
        first [ exact RA | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW | exact Q1 | exact Q2 | exact Q3 | exact C3
              | lazymatch goal with
                | |- rawp <= p' => clear - Hp' C1; lia
                | |- p' <= END2 => clear - Hp'; lia
                | |- 0 < rawp => exact RP
                | |- rw_cells _ _ rawp _ => eassumption
                | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                    cbv delta [A_pkcs7_parse_C24.dvA] beta; repeat match goal with |- _ /\ _ => split end;
                    first [ eassumption | reflexivity
                          | lazymatch goal with |- rw_cells _ ?mx A _ => lazymatch goal with CE : rw_cells _ mx A _ |- _ => unfold buf_cells, signer_cells; cbn [app]; exact CE end end
                          | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                          | first [ c24_dva Hn | match goal with |- ?g => idtac "DVAG-LEFT:" g end ] ]
                end
              | assumption
              | match goal with |- ?g => idtac "F9766C-LEFT:" g end ]. }
    (* [comment removed for export] *)
    assert (NE : p' <> se).
    { intros E. apply KE. rewrite E. reflexivity. }
    clear KE.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => lazymatch goal with HH : HM _ _ _ hc _ _ mx |- _ => pose proof (hm_abase asegs R HIA hc _ _ mx HH) as ABc end end.
    frame_aobj FSH (FB + 64) 1%nat as OPP. frame_aobj FSH (FB + 96) 1%nat as OL2.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with G12x : rw_cells _ _ (FB + 96) [C8 ?lw] |- _ =>
    acallxA_sp sp1
      (eapply GT' with (CS := hcs asegs R HIA hc) (PP := FB + 64) (LENP := FB + 96) (P := p') (END := se) (BUF := rawp) (bs := bs) (tag := 160) (lo := lo) (lenv := lw);
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact OPP | exact OL2 | exact CSOKc | exact ABc | exact (art_alwf asegs R HIA) | reflexivity
               | lazymatch goal with
                 | |- rw_cells _ _ (FB + 64) _ => eassumption
                 | |- rw_cells _ _ (FB + 96) _ => eassumption
                 | |- bytes_at _ _ rawp bs => lazymatch goal with RB : rw_cells _ _ rawp _ |- _ => exact (cb_bytes_at _ _ _ _ RB) end
                 | |- aobj _ _ _ _ rawp _ => rewrite LEN; eassumption
                 | |- stk _ _ lo _ => assumption
                 | |- mem_inv _ _ => assumption
                 | |- rawp <= p' => clear - Hp' C1; lia
                 | |- p' <= se => clear - Hse; lia
                 | |- se <= rawp + _ => rewrite LEN; clear - Hse C3; lia
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
                 end
               | match goal with |- ?g => idtac "GT-PRE-LEFT:" g end ])
    end.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "GT-LEFT:" g end.
    clear GT' ABc OPP OL2.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r3 end.
    match goal with H : _ < r3 <= 0 |- _ => rename H into Hr3 end.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    - (* [comment removed for export] *)
      assert (R30 : r3 = 0).
      { try change 18446744073709551615 with (Z.ones 64) in KT. try rewrite ?Z.land_ones in KT by (clear; lia). clear - KT Hr3. Z.div_mod_to_equations. lia. }
      match goal with H : r3 = 0 -> _ |- _ => destruct (H R30) as [GP2 GLEN] end.
      match goal with H : rw_cells _ _ (FB + 96) [C8 ?L] |- _ => pose proof (bv_unsigned_in_range 64 L) as LR; unfold bv_modulus in LR; cbn [Z.pow Z.of_N Pos.pow] in LR end.
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KQ; zify_cond KQ.
      + zstep. zstep. exitF (-21376) TPX SM0 HKc MFc Hr3 RP.
      + zstep. zstep. exitF (-21632) TPX SM0 HKc MFc Hr3 RP.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      rewrite (addw_err5480 r3 Hr3).
      zstep. if_cases KW; zify_cond KW.
      { exitF (r3 + -21632) TPX SM0 HKc MFc Hr3 RP. }
      exfalso. clear - KW Hr3. rewrite !zchk_signed_lit64 in KW by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L29784547046.121L39348544230.121L40624322454.12100000P01201RS2LF2sp1A1n2bs3LFB3shi1B1k2H22H0S1R2LF2sp1A1n2bs3LFB3shi1B1k2H22H0S2LF2sp1A1n2bs3LFB3shi1B1k2H22H0". (* [comment removed for export] *)
  #[using="LF sp A n bs LFB"] Lemma aobj_of_sshad : forall (CS : Z -> Prop) mX slo' shi B (k : nat),
    cs_ok AL CS -> sshad asegs AL mX slo' shi -> slo' <= B -> B + 8 * Z.of_nat (S k) <= shi -> B mod 8 = 0 -> 0 <= B ->
    crange CS B (8 * Z.of_nat (S k)) -> aobj asegs AL CS mX B (8 * Z.of_nat (S k)).
  Proof.
    intros CS mX slo' shi B k OK SS H1 H2 HB H0 HC.
    pose proof (sshad_chunk asegs AL mX slo' shi k B SS H1 H2 HB) as SH.
    replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) in SH by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    eapply (aobj_of_zero_shadow_sh asegs AL CS mX B (zcells (S k)) B 0 (S k) OK SH HC HB H0 ltac:(lia)).
    intros i Hi. apply cell_at_zcells. exact Hi.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L40231916847.6 L40231919038.7 L40238205906.12L40238205906.9 L5792585626.5  00000B00V01601K01]S4SPq'1a1b2H21x2HsS1R1a1b2H34DLO'1x2HdS1R1a1b2H31x1B1j2Hr3FB02n03Hle1HS1R1a1b2H31x1B1j2Hr1HS3SPq4SPq'2H11x2Hs". (* [comment removed for export] *)
  #[using="HIA"] Lemma presA_drop_low : forall LB' LF' SPq SPq' SSPq TOPq a b W m1 m2,
    presA asegs R LB' LF' SPq SSPq TOPq ((a, b) :: W) m1 m2 -> SPq <= SPq' -> b <= SPq' -> alloc_ceiling <= a -> blocks_low R LB' LF' ->
    presA asegs R LB' LF' SPq' SSPq TOPq W m1 m2.
  Proof.
    intros LB' LF' SPq SPq' SSPq TOPq a b W m1 m2 [P S] H1 H2 H3 BL. split; [| exact S].
    pose proof (art_data_lo asegs R HIA) as DLO'.
    intros x Hx Hc Ho. apply P; [exact Hx| |].
    - destruct Hc as [Hs|[Hd|Hb]]; [left; clear - Hs H1; lia| right; left; exact Hd| right; right; exact Hb].
    - cbn [outside]. split; [| exact Ho]. destruct Hc as [Hs|[Hd|Hb]]; [clear - Hs H2; lia| clear - Hd H3 DLO'; lia|].
      ddestruct Hb as ([B j] & Hin & Hr). cbn in Hr. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      + pose proof (BL B j ltac:(apply in_app_iff; left; exact Hin)). clear - H H3 Hr. lia.
      + destruct (fdata_sub2 _ _ Hin) as ([FB0 n0] & Hf & Hle). cbn in Hle. pose proof (BL FB0 n0 ltac:(apply in_app_iff; right; exact Hf)). clear - H H3 Hr Hle. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03i0@C17025492443.284C51703510221.285D17862782199.285D27847976046.285D54678312198.285D60109446735.285K21212095580.284K55088519473.285L10350520051.20 L10370335306.1  L10377779059.1  L10596430123.1  L10762500794.4  L10894997063.3  L11879002598.1  L12856250995.20 L12886541299.1  L13176305223.2  L13258319052.1  L14065442494.4  L14575900174.20 L14577825678.1  L14648274357.15 L14890891574.15 L1540877545.17  L1540877545.3   L154317396.2    L15618147883.1  L15686577978.1  L16896526054.1  L17064006458.1  L18215415218.2  L19412386243.20 L19769535484.2  L19959024712.1  L19980016842.7  L20166242178.3  L20690421408.1  L21007906567.2  L21218866939.2  L21311120310.1  L22524867225.3  L2254620236.6   L23280248706.2  L23778063080.3  L24128180555.1  L2424960062.2   L24556220889.2  L24814928753.20 L2514189370.1   L25666648246.15 L26581069586.21 L26892418956.1  L26925090882.20 L26926459330.1  L27650499371.1  L28113126617.2  L28174365494.15 L2841043673.2   L29343637352.3  L29488365454.7  L29773715284.1  L30251340380.4  L31034375991.6  L31636313402.1  L31653556939.1  L31863022963.4  L32454903270.1  L32735572878.1  L32982411378.9  L33136591625.1  L33312313103.2  L33532570708.1  L34673485611.1  L34783991938.3  L35666023782.15 L36021046681.2  L36692980745.1  L36946940416.2  L36957137154.19 L37714553091.1  L38224815777.0  L38235734261.1  L38738405142.1  L39231752993.0  L39686831147.1  L39833554087.18 L39899360997.3  L40281191306.3  L40531390536.1  L41409160545.3  L41582997571.20 L41584906691.2  L41894566718.4  L41898327682.3  L42343371559.18 L42642555220.1  L42730880473.2  L43300649301.0  L43601418766.2  L43603311502.20 L44179521038.20 L44334313263.1  L4487177102.20  L45163301507.4  L46290454573.5  L46474986368.2  L46485780610.19 L46494596498.21 L46541147848.1  L46745494493.3  L47074042038.21 L47882514004.1  L49028543392.1  L49508988902.1  L49828434905.2  L50059436232.1  L50790731766.15 L51299303177.1  L52045659405.3  L52097702196.21 L52101890174.5  L52941874306.3  L53297529385.1  L53525256509.20 L54246093652.1  L54692943777.17 L55079916376.4  L55085943702.3  L56523586534.1  L56602619958.21 L57124690773.0  L57611209309.2  L58143913820.1  L58412049673.1  L58748427563.1  L58790154276.16 L59308586248.2  L59578101107.3  L60056205954.3  L60098763854.6  L61132393998.7  L61160671333.3  L61545304294.1  L61970568713.1  L6203936179.1   L62413581882.1  L63373084206.4  L63613504898.3  L64284786756.22 L64284786756.24 L64515399665.20 L64526695682.20 L64850595401.0  L66151427842.16 L66559471286.13 L66845504556.4  L66845505451.7  L66925273130.280L67884573201.1  L68003094489.2  L6899380056.1   L7049614941.2   L7122685215.10  L7368572214.13  L7404054466.20  L7412273667.4   L7893464212.4   L8265267294.0   L8466307646.21  L881835912.0    L9080220944.4   L9149395626.2   L9356559676.20  L9631767084.2   L9873114841.15  L9957571780.22  L9957571780.24  O12120680648.285O1478916974.285 O17025492443.284O25079455223.285O28722692754.285O35263825765.285O37051008023.285O37526595730.285O4013719057.285 O47761277330.285O47806715794.285O49812953032.285O50702732434.285O51703510221.285O5455046344.285 O56414299794.285O56474393032.285O59365646154.285O59625529265.285O60864744136.285O67527245000.285O8345375835.285 P10761940190.285P10897630432.285P165605033.285  P20181466405.285P21212095580.284P22525420797.285P23277647141.285P24549450622.285P28106331774.285P2847813758.285 P34789739045.285P41419110342.285P41579152228.285P41905122341.285P42716737406.285P49843618174.285P52940256805.285P60050384933.285P63606742821.285P68008807806.285P9155141645.285 Q12683804246.285Q1436510207.285 Q15766564435.285Q17177644902.285Q19561611600.280Q34362053984.285Q34671324314.280Q34964382778.285Q364471657.285  Q36856420847.285Q38248387216.285Q39840088098.285Q40325119892.285Q42439168719.285Q43436911846.285Q48360113622.285Q53259957567.285Q56389205783.285Q59865603600.285Q64200704302.285Q64683942374.285Q66549688001.285Q66565712913.285Q7757834201.280 Q9090756535.285 Q9356559649.265 Q9633802415.280 Q9644583048.285 00000100202Q05307Z09G09H0;00<00<60<;0<?0<@0<A0<E0=E0=J0=R0=W0=g0>=0>B0?80?n0@K0@W0@X0@\0@`0@d0@h0A00AM0AU0AZ0B20B30B80B>0B?0BC0BD0BV0BW0Bc0Bg0Bm0Bn0Cn0D20D_0Ed0Eh0F>0FC0FG0FH0G50G60GB0GZ0G^0Gn0HA0HE0HI0HY0H]0Hb0I60I:0IA0IE0II0IJ0Io0J70J;0JE0KM0KP0KQ0KU0KX0KY0K]0LW0Lc0Ll0M10M20MO0MP0M`0Ma0N[0N_0N`0Na0Ni0OB0O[0O_0P50PD0PV0P`0Qh0Rm0S20S=0TB0TF0TK0TO0TP0TU0UC0UG0US0VW0Ve0Vf0Vj0Wj0Wn0Xd0Y10Y20Y60Z;0Z<0ZD0ZG0ZK0ZO0[E0[K0[T0[U0[_0\70\C0\G0\K0\P0\T0\d0\e0]i0_00`00`h0`i0aL0b00b;0bP0d60d90d:0d>0dF0d_0eC0eY0eh0f80f90g30g40gC0gD0hB0hI0i60j:0kA0kB0kC0kD0kE0kF0kG0kH0kI0kJ0kK0kL0kM0kN0kO0kP0kQ0kR0kS0kT0kU0kV0kW0n10oY0oZ11C11D14316R18o1;Q1>31?\1AE1Bj1DS1G01IR1K;1Ld1NM1Pj1SG1Tk1VP1XJ1Yh1[X1[Y1]61_;1`Y1`Z1b71dN1f61gY1gZ1iB1k\1k]1k^1k_1mb1o@21E22b24J25m27M28mFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2bs2A02Hn3TOP3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2LAS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1A1n2lo2bs2A02Hn3TOP3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj02hc3HTc3SP13SZC3SPR2F04SP1R2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs2A02Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3SPR2F04SP1R2LAS1R4STKg4STKs4STKf2LF2sp1A1n2lo2bs3LFB3LOS2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S4rawpS3sp1S2FBFFS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S3sp1S2lo3sp1S3sp1S2sp3sp13SP13SPRS1R4STKg4STKs4STKf3sp1S3sp1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2sp3sp13SP1S2sp3sp13SP1FS2FBS2FBS2FBS2FBS2lo3sp1S1R4STKg4STKs4STKf2sp3sp13SP1S1n4rawpS3sp1S1R3HIA1h2sp3TOP3sp13SP1FS3sp1S1n2HnFS2FBFS1A2lo4ALO11a1k2H2FS2sp3sp13SP1S2FBS1n2HnFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1S1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCES2spS1R4STKg4STKs4STKf3sp1S3sp1S2FBFS1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1FS2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP1S2FBS2sp3SPH3sp13SP1S1R3HIA1h2sp3TOP2HTS2FBS2FBS2sp3SPH3sp13SP1S2FBS3sp1S1R2lo3LOS2FB3ALO2F1S2FBS2FB2F0S2FBS2FBFS1R3HIA4STKg4STKs4STKf1h2sp2lo3TOP2HTS2LF3LFBS2FBS3sp14SP1RS1R3NS14STKg4STKs4STKf5STKg02sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALO3ACPS1ASS2loS1ASS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOS2sp3sp13SP1S1R3HIA1hS3sp1FS1R4STKg4STKs4STKf2sp3sp13SP1FS2sp3sp13SP13SPRFS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOS2FBFSS2sp3sp1S1R4STKg4STKs4STKf2sp3sp1S1R4STKg4STKs4STKf2sp3sp1S2FBS1R4STKg4STKs4STKf3sp1S2sp2lo3sp13SP1S1R1n4rawp3ACV3RCES3sp14SP1RS1R3NS14STKg4STKs4STKf5STKg02sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALO3ACPS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCES3sp1S2sp2lo3sp1S1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCES2FBS3sp1S2FBFS3sp1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS2FBS2sp3sp13SP1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALO1a2Da4DLO'S1R2FB2F21a2DaFS2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S2FBS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP1S1R2FB3ACV2F1FS2FBS1R4STKg4STKs4STKf2sp1n2lo3slo4SLOS4SLOL3SLO3LOS3sp14rawp3SP13ALO3RCESS2lo3sp1S1AS2FBS2FBS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2sp2lo3SLO3sp13SP1S1i2HiS2FB1c2HcFS1R2lo3LOSS1R3HIA1h2sp3TOP3sp13SP1S2sp3sp13SP1S2FBS2FBS3sp1S2FBS1n2FB4rawp4APRFFS1R4STKg4STKs4STKf2sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS3sp13SP11a1k2H2S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F11a1k2H2S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F1S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3ALO2F1SS3sp12r04SP1M1q1r1H2H02q02H42FB3F64S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S2FB1a1k2H3S1A2FB4APPA1a1k2H12H2S1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1AFS2FBS2lo3sp1S1R1n2lo3LOS4rawp3ALO3RCES1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf3sp1S2sp2lo3sp13SP1S1n2FB4rawp4APRFSS1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS3sp13SP13ALOSS2sp2lo3sp13SP1FS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS2FB2F0S1R4STKg4STKs4STKf2sp2lo3slo4SLOL3SLO3sp13SP1S1R4STKg4STKs4STKf2sp1A2lo3slo4ASTK4SLOS4SLOL3SLO3LOS3sp13SP11a1k2H2S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOS2FB3sp13SP13ALO2F11a1k2H2FFFFFFFFFFFFFFFFFFFFFFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF1n2lo2bs3LEN2Hn3LFB3LOS3sp13alg4rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2C12C22C33ALO3RCE2LAS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAFS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs3LEN2Hn4SLOS4SLOL3SLO3LFB3sp13alg4rawp1P4END22rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2C12C22C33ALO3RCE2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB4ALO13sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO4FBLO2F12LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4FBLO2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2F12LAS1R4STKg4STKs4STKf2LF1A1n2lo2bs3LFB4ALO13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R4STKg4STKs4STKf2LF2sp1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NB03NRT2LF1n2lo2bs2Hn3LFB3LOS3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3ALO2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R4STKg4STKs4STKf2LF2sp1A1n2bs3LFB2FB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC3SPR2F82F02LAFS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAFS1R4STKg4STKs4STKf2LF1n2lo2bs3LFB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo3slo2bs2Hn4SLOS4SLOL3SLO3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC3ALO2LAS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2LF1n3slo2bs4SLOS3LFB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAFS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1A1n2lo3slo2bs4ASTK2Hn4SLOS4SLOL3SLO3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAFFFS1R3HIA3NS14STKg4STKs4STKf5STKg03NB03NRT1h2LF2sp1n3slo2bs2Hn3TOP3LFB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2HT2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R3NS14STKg4STKs4STKf5STKg03NA03NB03NRT2LF2sp1n2lo2bs2Hn3SLO3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2LAS1R4STKg4STKs4STKf2LF2sp1n2lo2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SP13SZC2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB3sp13alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC4SP1R2LAS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02LAS1R4STKg4STKs4STKf2LF1n2bs3LFB2FB3alg4rawp2rt2p03ver2vp3dtg4dpad4dlen2dq3j562q22q33sj03SZC2F02LA". (* [comment removed for export] *)
  #[using="IMG NS1 DIMG HMND GETTAG PHIg FFRg CNTg STKg C24c GETCERTS PHIs FFRs CNTs STKs GETSIGNERS STKf PKFREE PHIg_mono FFRg_mono CNTg_mono PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint PHIf_mono FFRf_mono STKg0 AMS MCI CINFO NA0 NB0 NRT AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPA SPH TPV LFB C24H LOS ALO1"] Lemma from_978e8 : forall (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 v48 v80 : word) (g4 g12 g16 g18 g22 j32 alg : list byte)
      (rawp P END2 : Z) (rt p0 ver vp dtg dpad : word) (dlen dq : Z) (j56 q2 q3 : list byte) (sj0 : signer_junk)
      mc moc hc (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s9v : word),
    dvA FB sp1 X0 PHIa FFRa w0 w1 w2 g4 (le8 (Z_to_bv 64 P)) g12 g16 g18 g22 FSHGL (Z_to_bv 64 FB) (Z_to_bv 64 A) j32 v48 alg v80
        ([C4 rt; C4 p0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 rawp); C4 ver; C4 vp] ++ buf_cells dtg dpad dlen dq ++ [CB 8 j56]
         ++ [CB 744 (zeros 744)] ++ [CB 8 q2; CB 416 (zeros 416); CB 8 q3] ++ signer_cells 0 0 sj0)
        [(rawp, n)] mc moc hc ->
    rw_cells asegs mc rawp [CB (Z.to_nat n) bs] -> 0 < rawp -> (rawp + n <= A \/ A + 1440 <= rawp) ->
    rawp <= P -> P <= END2 -> END2 <= rawp + n ->
    rawp <= dq -> 0 <= dlen -> dq + dlen <= rawp + n ->
    PHIa <= 2 * n + AVOL_CALL -> FFRa <= fr_charge (d + 1) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) s4v (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 END2) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (A + 32)) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97ecc) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D RAWB RP RA C1 C2 C3 Q1 Q2 Q3 BPHI BFFR BUD BUDF UW.
    cbv beta in D. dvA_open D. tail_prep.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (WCA0 : wcover R LB LF (bv_unsigned sp) X0 A 1440) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    lazymatch type of HHc with HM _ _ _ _ ?LB2x _ _ => set (LB2 := LB2x) in HHc end.
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
    pose proof (PHIg_mono 0 n ltac:(clear - Hn; lia)) as PG0. pose proof (FFRg_mono 0 n (d + 1) ltac:(clear - Hn; lia)) as FG0.
    (* [comment removed for export] *)
    cb8_to_c8 G8 (@nil cell). rewrite le_bytes_to_word_le8 in G8.
    splitat RSL 4%nat ALG. splitat ALG 1%nat SE.
    assert (LA : length alg = 24%nat) by (destruct ALG as [[Hwf _] _]; exact (proj1 Hwf)).
    assert (AOBS : aobj asegs AL (hcs asegs R HIA hc) mc (sp1 + 56) 24).
    { apply (aobj_of_sshad (hcs asegs R HIA hc) mc slo (bv_unsigned sp) (sp1 + 56) 2 CSOKc SSc);
        [clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia| clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCSc| clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia| clear - SP1; lia]. }
    assert (AOSE : aobj asegs AL (hcs asegs R HIA hc) mc (sp1 + 80) 8).
    { apply (aobj_of_sshad (hcs asegs R HIA hc) mc slo (bv_unsigned sp) (sp1 + 80) 0 CSOKc SSc);
        [clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia| clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCSc| clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia| clear - SP1; lia]. }
    unfold buf_cells, signer_cells in CELLS. cbn [app] in CELLS.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 426584) with (Z_to_bv 64 (arl_amemset R)) by (rewrite AMS; reflexivity).
    apply (u8arr_of_rw_cells asegs) in ALG.
    pose proof (artA_amemset asegs R HIA (arl_amemset R)) as SPM.
    acallxA_sp sp1
      (eapply SPM with (h := hc) (LB := LB2) (LF := (FB, 256) :: LF) (DST := sp1 + 56) (v := 0) (n := 24) (lo := lo) (ds := alg); clear SPM;
         rewrite ?(unsigned_lit sp1) by exact SP1R;
         first [ exact ALG | exact AOBS | exact LOS | reflexivity
               | lazymatch goal with
                 | |- _ = arl_amemset R \/ _ => left; reflexivity
                 | |- HM _ _ _ hc _ _ _ => eassumption
                 | |- Z.of_nat (length alg) = 24 => rewrite LA; reflexivity
                 | |- 0 <= 0 < 256 => clear; lia
                 | |- stk _ _ lo _ => assumption
                 | |- lo <= _ - arl_need_amem R => clear - SLO SP1 NS1 NB0 NA0 NRT STKg0 STKs0 STKf0; lia
                 | |- crange _ lo _ => eapply crange_sub; [exact SCSc| clear; lia| clear - SP1; lia]
                 | |- mem_inv _ _ => assumption
                 | |- sp1 + 56 + 24 <= lo \/ _ => right; clear; lia
                 | |- 24 = 0 \/ _ => right; clear - SP1 SPH; lia
                 | |- 24 < _ => clear; lia
                 | |- client_wrange _ _ _ _ _ _ => apply client_wrange_stack; [clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| rewrite HTc; clear - SP1 TOP; lia]
                 | |- _ <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                 end
               | match goal with |- ?g => idtac "AMEMSET-PRE-LEFT:" g end ]).
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AMEMSET-LEFT:" g end.
    try clear SPM.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    lazymatch goal with H : u8arr _ m1 (sp1 + 56) _ |- _ =>
      apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; change (Z.to_nat 24) with 24%nat in H;
      pose proof (rw_cells_reshape asegs _ _ _ (buf_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0) H ltac:(cbn; repeat split; exact I) ltac:(vm_compute; reflexivity)) as BS1; clear H end.
    lazymatch goal with H : ?x = Z_to_bv 64 (sp1 + 56) |- _ => subst x | _ => idtac end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with HH : HM _ _ _ hc _ _ m1 |- _ => rename HH into HH1 end.
    lazymatch goal with MI : mem_inv _ m1 |- _ => rename MI into MI1 end.
    lazymatch goal with SS : sshad _ _ m1 slo (bv_unsigned sp) |- _ => rename SS into SS1 | _ => idtac "no SS1" end.
    lazymatch goal with ST : stk _ m1 lo sp1 |- _ => rename ST into ST1 | _ => idtac "no ST1" end.
    lazymatch goal with RB : rw_cells _ m1 rawp _ |- _ => rename RB into RAWB1 end.
    frame_aobj FSH (FB + 64) 1%nat as OPP.
    assert (CWP : client_wrange L (LB2 ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) (FB + 64) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    destruct (sshad_split asegs AL m1 slo sp1 (bv_unsigned sp) SS1 ltac:(clear - SP1 SLO SLOL NS1 STKg0 STKs0 STKf0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi]. clear SS1.
    pose proof CINFO as CI'. unfold pkcs7_cinfo_stmtA, A_PKCS7_CINFO_G in CI'.
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply CI' with (h := hc) (LB := LB2) (LF := (FB, 256) :: LF) (PP := FB + 64) (SEQE := sp1 + 80) (BS := sp1 + 56) (P := P) (END := END2) (BUF := rawp) (bs := bs)
                     (lo := lo) (slo := slo) (tg0 := Z_to_bv 64 0) (pad := Z_to_bv 64 0) (len0 := 0) (q0 := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold PKCS7_CINFO_STACK_A;
        first [ exact HH1 | exact G8 | exact BS1 | exact OPP | exact AOSE | exact AOBS | exact CWP | exact ST1 | exact SSlo | exact SLOS | exact SLOL | exact MI1 | exact TPV | exact C1 | exact C2 | exact RP | reflexivity
              | lazymatch goal with
                | |- (length _ < 512)%nat => cbn [length]; clear - LFB; lia
                | |- rw_cells _ m1 (sp1 + 80) _ => eassumption
                | |- bytes_at _ m1 rawp bs => exact (cb_bytes_at _ _ _ _ RAWB1)
                | |- END2 <= rawp + Z.of_nat (length bs) => rewrite LEN; exact C3
                | |- rawp + Z.of_nat (length bs) < 2 ^ 63 => rewrite LEN; clear - RCE ACV; lia
                | |- FB + 64 + 8 <= sp1 + 80 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- FB + 64 + 8 <= sp1 + 56 \/ _ => left; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- sp1 + 80 + 8 <= sp1 + 56 \/ _ => right; clear; lia
                | |- _ = 0 \/ FB + 64 + 8 <= rawp \/ _ => right; rewrite LEN; clear - APRF; lia
                | |- _ = 0 \/ sp1 + 80 + 8 <= rawp \/ _ => right; right; rewrite LEN; clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- _ = 0 \/ sp1 + 56 + 24 <= rawp \/ _ => right; right; rewrite LEN; clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- (FB + 64) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- (sp1 + 80) mod 8 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- (sp1 + 56) mod 8 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < FB + 64 /\ _ => split; [clear - F0; lia| clear - F1 ACV; lia]
                | |- 0 < sp1 + 80 /\ _ => split; [clear - SP1 SLO LOS ALO ACP NS1 STKg0 STKs0 STKf0; lia| clear - SP1 SPR; lia]
                | |- 0 < sp1 + 56 /\ _ => split; [clear - SP1 SLO LOS ALO ACP NS1 STKg0 STKs0 STKf0; lia| clear - SP1 SPR; lia]
                | |- lo <= sp1 - 4240 => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                | |- lo <= sp1 - 144 - arl_need_smalloc R => clear - SLO SP1 NS1 NB0 NRT STKg0 STKs0 STKf0; lia
                | |- 0 <= arl_need_smalloc R => exact NS1
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- FB + 64 + 8 <= lo \/ _ => left; clear - F1 ALO LOS; lia
                | |- sp1 + 80 + 8 <= lo \/ _ => right; clear; lia
                | |- sp1 + 56 + 24 <= lo \/ _ => right; clear; lia
                | |- _ = 0 \/ rawp + _ <= lo \/ _ => right; left; rewrite LEN; clear - RCE ALO LOS; lia
                | |- client_range _ _ _ (FB + 64) _ => eapply client_range_block; [exact IND| clear; lia| clear; lia]
                | |- client_range _ _ _ (sp1 + 80) _ => apply client_range_stack; clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia
                | |- client_range _ _ _ (sp1 + 56) _ => apply client_range_stack; clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia
                | |- client_range _ _ _ rawp _ => rewrite LEN; eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia]
                | |- client_wrange _ _ _ _ (sp1 + 80) _ => apply client_wrange_stack; [clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia| rewrite HTc; clear - SP1 TOP; lia]
                | |- client_wrange _ _ _ _ (sp1 + 56) _ => apply client_wrange_stack; [clear - SP1 SLO NS1 STKg0 STKs0 STKf0; lia| rewrite HTc; clear - SP1 TOP; lia]
                | |- aobj _ _ _ m1 rawp _ => rewrite LEN; eassumption
                end
              | match goal with |- ?g => idtac "CINFO-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 PO.
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & h2 & r & p' & se & tg & len & q
                    & -> & HH2 & Ecs & Etop & Estk & Eflag & Evol & Efr & HKiff & HP2 & MI2 & ST2 & SS2 & Ea0 & Hr & FPP2 & SE2 & BS2 & Hp' & HOK).
    subst ua0. clear CI'.
    replace (ret_pc (Z_to_bv 64 0x97ef0)) with (Z_to_bv 64 0x97ef0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in HP2, ST2, SS2 by exact SP1R. rewrite HSc in HP2.
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m2).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (HP2w : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) ((FB + 64, FB + 64 + 8) :: [(sp1 + 80, sp1 + 80 + 8); (sp1 + 56, sp1 + 56 + 24)]) m1 m2).
      { subst LB2. eapply presA_weaken; [exact HP2| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros xq Hx; exact Hx]. }
      pose proof (presA_drop_fresh_gen R LB LF sp1 sp1 (hstkhi asegs R HIA h) [(sp1 + 80, sp1 + 80 + 8); (sp1 + 56, sp1 + 56 + 24)] FB 256 (FB + 64) (FB + 64 + 8) m1 m2 HP2w FRSH
                    ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - F1 FBLO SP1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as HP2d.
      pose proof (presA_drop_low LB LF sp1 (bv_unsigned sp) sp1 (hstkhi asegs R HIA h) (sp1 + 80) (sp1 + 80 + 8) [(sp1 + 56, sp1 + 56 + 24)] m1 m2 HP2d
                    ltac:(clear - SP1; lia) ltac:(clear - SP1; lia) ltac:(clear - ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia) (proj1 WL)) as HP2e.
      pose proof (presA_drop_low LB LF (bv_unsigned sp) (bv_unsigned sp) sp1 (hstkhi asegs R HIA h) (sp1 + 56) (sp1 + 56 + 24) [] m1 m2 HP2e
                    ltac:(clear; lia) ltac:(clear - SP1; lia) ltac:(clear - ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia) (proj1 WL)) as HP2f.
      eapply presA_weaken; [exact HP2f| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear - SP1 LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia| intros xq Hx; exact I]. }
    clear PRES.
    assert (SI1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES2))|].
      intros a Ha. exact (si_outside1 L SI A 1440 a AOD Ha). }
    assert (SI2 : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SI1| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. ddestruct (si_data SI a Ha) as (Da & _ & _). pose proof (art_data_lo asegs R HIA) as DLO'. cbn.
      split; [clear - Da F2; lia|]. split; [clear - Da DLO' ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia|]. split; [clear - Da DLO' ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| exact I]. }
    clear SIc SI1 PRES2 WL2 WCA2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJF : forall a k, FB <= a -> a + k <= FB + 256 -> (a + k <= FB + 64 \/ FB + 72 <= a) -> disjoint_from [(FB + 64, FB + 64 + 8); (sp1 + 80, sp1 + 80 + 8); (sp1 + 56, sp1 + 56 + 24)] a k).
    { intros a k H1 H2 H3. cbn. split; [clear - H3; lia|]. split; [clear - H1 H2 F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia|]. split; [clear - H1 H2 F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| exact I]. }
    assert (DJA : forall a k, A <= a -> a + k <= A + 1440 -> disjoint_from [(FB + 64, FB + 64 + 8); (sp1 + 80, sp1 + 80 + 8); (sp1 + 56, sp1 + 56 + 24)] a k).
    { intros a k H1 H2. cbn. split; [clear - H1 H2 APPA; lia|]. split; [clear - H2 ASTK LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia|]. split; [clear - H2 ASTK LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| exact I]. }
    assert (CRsub : forall a k, A <= a -> a + k <= A + 1440 -> client_range L (LB2 ++ fdata ((FB, 256) :: LF)) sp1 a k).
    { intros a k H1 H2. apply (client_range_lower L _ lo sp1 a k); [| clear - H2 ALO1; unfold RepCrt.PKCS7_SIZE, P_pkcs7_top.PKCS7_SIZE in *; lia].
      eapply client_range_inside; [exact CWAc| intros b Hb; exact Hb| exact H1| exact H2]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) LB2 ((FB, 256) :: LF) sp1 sp1 (hstkhi asegs R HIA h) [(FB + 64, FB + 64 + 8); (sp1 + 80, sp1 + 80 + 8); (sp1 + 56, sp1 + 56 + 24)] m1 m2 FB _ CSOKc) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in FHD; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G4; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G12; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G16; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G18; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in G22; [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJF; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| cbn [cells_size csize Nat.add]; cbn; repeat split; clear - SP1 F1 ALO LOS SLO NS1 STKg0 STKs0 STKf0; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in RSL; [| apply client_range_stack; clear; lia| cbn [cells_size csize Nat.add]; cbn; repeat split; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in STa; [| clear; lia| cbn; repeat split; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in STb; [| clear; lia| cbn; repeat split; clear - F1 ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SShi; [| clear; lia| clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m2 slo sp1 (bv_unsigned sp) SS2 SShi ltac:(clear - SP1 SLOL SLO NS1 STKg0 STKs0 STKf0; lia)) as SSm2. clear SS2 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in CELLS; [| cbn [cells_size csize Nat.add]; apply CRsub; clear; lia| cbn [cells_size csize Nat.add]; apply DJA; clear; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in RAWB1;
      [| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); eapply client_range_block; [apply in_or_app; left; exact RIN| clear; lia| clear; lia]
       | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - Hn; lia); cbn; split; [clear - APRF; lia| split; [clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| split; [clear - RCE ALO LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia| exact I]]] ].
    assert (OBJ2 : aobj asegs AL CS m2 A 1440).
    { eapply presA_aobj0; [exact CSOK| exact HP2| exact OBJA| intros xq Hx; eapply hcs_below_top; exact Hx| right; split; [apply CRsub; clear; lia| clear; lia]]. }
    clear OBJA ST1 SSlo MI1 HP2 G8 OPP CWP AOBS AOSE OBUF HH1.
    (* [comment removed for export] *)
    pose proof FPP2 as G8'. blob8 G8'.
    pose proof BS2 as BS2b. unfold buf_cells in BS2b. apply rw_cells_blob in BS2b. cbn [cells_size csize Nat.add] in BS2b.
    joinr RSL BS2b. joinr RSL SE2.
    intros mo9 [HK9 MF9]. pose proof (mo_frame_trans _ _ _ MFc MF9) as MF9'. clear HKc MFc.
    subst LB2.
    eapply (from_9790c FB sp1 PHIa FFRa w0 w1 w2 v48 g4 g12 g16 g18 g22 j32 rawp P END2 r p' se tg (Z_to_bv 64 0) len q rt p0 ver vp dtg dpad dlen dq j56 q2 q3 sj0 m2 mo9 h2);
      first [ exact RA | exact RP | exact C1 | exact C2 | exact C3 | exact Q1 | exact Q2 | exact Q3 | exact Hr | exact Hp' | exact HOK | exact BPHI | exact BFFR | exact BUD | exact BUDF | exact UW
            | lazymatch goal with
              | |- rw_cells _ m2 rawp _ => exact RAWB1
              | |- A_pkcs7_parse_C24.dvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  cbv delta [A_pkcs7_parse_C24.dvA] beta;
                  split; [exact HH2|]; split; [apply (proj2 (HKiff mo9)); exact HK9|]; split; [exact MF9'|];
                  split; [rewrite Etop; exact HTc|]; split; [rewrite Estk; exact HSc|]; split; [rewrite Eflag; exact HFc|];
                  split; [intros xq Hx; rewrite Ecs; exact (HCSc xq Hx)|]; split; [rewrite Evol; exact HVc|]; split; [rewrite Efr; exact HFRc|];
                  split; [exact PRESb|]; split; [exact SI2|];
                  repeat match goal with |- _ /\ _ => split end;
                  first [ exact G8' | exact RSL | exact OBJ2 | eassumption | reflexivity
                        | lazymatch goal with |- rw_cells _ m2 A _ => unfold buf_cells, signer_cells; cbn [app]; exact CELLS end
                        | match goal with H : ?a <= ?x <= ?b |- ?a' <= ?x' => first [exact (proj1 H) | exact (proj2 H)] end
                        | first [ c24_dva Hn | match goal with |- ?g => idtac "DVA2-LEFT:" g end ] ]
              end
            | match goal with |- ?g => idtac "F97608-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
