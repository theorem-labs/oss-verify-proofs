(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_crt_free P_pkcs7_top P_pkcs7_free.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_read_binary_stmt A_platform_zeroize
     A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_mpi_stmtA A_mpi_zeroize_and_free A_crt_stmts A_x509_crl_free A_x509_crt_free A_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_top24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.
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
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)


(* [comment removed for export] *)



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
Local Ltac zchk_fails ::= constr:([0x98348]).
Local Ltac zchk_new ::= constr:([0x981b8; 0x981bc; 0x98230; 0x98234; 0x9826c; 0x98270; 0x982a8; 0x982ac]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HFREE : arl_free R = A_WRAP_FREE_CF.
  Hypothesis NEEDF : 0 <= arl_need_free R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis NEEDM : 0 <= arl_need_malloc R.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis SHALLOW : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  Hypothesis ZFREE : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Variable PK : pk_class asegs.
  Variables (PHIpk : Z -> Z) (FFRpk : Z -> Z -> Z) (STKpk : Z).
  Hypothesis STKpk0 : 0 <= STKpk.
  Hypothesis PHIpk0 : forall k, 0 <= k -> 0 <= PHIpk k.
  Hypothesis FFRpk0 : forall k d, 0 <= k -> 0 <= d -> 0 <= FFRpk k d.
  Hypothesis PHIpk_mono : forall k k', 0 <= k <= k' -> PHIpk k <= PHIpk k'.
  Hypothesis FFRpk_mono : forall k k' d, 0 <= k <= k' -> FFRpk k d <= FFRpk k' d.
  Hypothesis PKFREE : pk_free_stmtA asegs R HIA PK PHIpk FFRpk STKpk A_PK_FREE.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  (* [comment removed for export] *)
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2613541441.2300000?S1R5NEEDF5NEEDM". (* [comment removed for export] *)
  Let NRT : arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Let CRTFREE : x509_crt_free_stmtA asegs R HIA PK (PHIcf PHIpk) (FFRcf FFRpk) (STKcf R STKpk) A_X509_CRT_FREE
    := A_x509_crt_free_walk R HIA IMG HFREE NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK PHIpk FFRpk STKpk PHIpk0 PHIpk_mono FFRpk_mono PKFREE DIMG.
  Let CRLFREE : x509_crl_free_stmtA asegs R HIA (X509_CRL_FREE_STACK_A R) A_X509_CRL_FREE
    := x509_crl_freeA R HIA IMG HFREE NEEDF NEEDA PZ.

  Section Live.
    Variables (h : HST asegs R HIA) (LBn LB LF : list blk).
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
              (A lo d : Z) (po : p7_own) (pj : p7_junk).
    Hypothesis HH : HM asegs R HIA h (LBn ++ LB) LF m.
    Hypothesis HK0 : HK asegs R HIA h mo.
    Hypothesis LIVE : pkcs7_live asegs PK m (LBn ++ LB) A po pj.
    Hypothesis SMALL : po_rawlen po < 2 ^ 40 /\ co_rawlen (po_crt po) < 2 ^ 40.
    Hypothesis NDn : List.NoDup LBn.
    Hypothesis IFF : forall b, In b LBn <-> In b (p7_blocks po).
    Let NDO : List.NoDup (map fst (LBn ++ LB)). Proof. exact (HMND _ _ _ _ HH). Qed.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A 1440.
    Hypothesis DS : A + 1440 <= lo \/ bv_unsigned sp <= A.
    Hypothesis LOS : arl_stklo R <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - STKp7f R STKpk.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= htop asegs R HIA h.
    Hypothesis TP : tp = Z_to_bv 64 (arl_tp R).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.
    Hypothesis UWO : uw_obj R A 1440 d.
    Hypothesis BUD : havol asegs R HIA h + PHIp7f PHIpk (Z.of_nat (length LBn)) <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + FFRp7f FFRpk (Z.of_nat (length LBn)) d <= FR_MAX.

    Let ND : List.NoDup (map fst (p7_blocks po)).
    Proof. ddestruct LIVE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N). exact N. Qed.
    Let SUB : forall b, In b (p7_blocks po) -> In b LBn.
    Proof. intros b Hb. apply (proj2 (IFF b)). exact Hb. Qed.
    Let HA : 0 < A. Proof. ddestruct LIVE as (_ & _ & X & _). exact X. Qed.
    Let HAL : A mod 8 = 0. Proof. ddestruct LIVE as (_ & X & _). exact X. Qed.
    Let AB : A + 1440 <= 2 ^ 64. Proof. ddestruct LIVE as (_ & _ & _ & X & _). exact X. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L29280787994.7900000:S2sp1A1d1H". (* [comment removed for export] *)
    Let D0 : 0 <= d. Proof. destruct UWO as [[_ H]|H]; lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Let LENk : Z.of_nat (length LBn) = Z.of_nat (length (p7_blocks po)).
    Proof.
      f_equal. apply Permutation.Permutation_length. apply Permutation.NoDup_Permutation; [exact NDn| | exact IFF].
      pose proof ND as N. clear - N. induction (p7_blocks po) as [|b l IH]; [constructor|]. cbn in N. inversion N; subst.
      constructor; [| apply IH; assumption]. intros C. apply H1. apply in_map. exact C.
    Qed.

    (* [comment removed for export] *)
    Definition pinv (D : list blk) (cs : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop :=
      HM asegs R HIA hc (Lc ++ LB) LF mc /\ HK asegs R HIA hc moc /\ mo_frame mo moc
      /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h /\ hflag asegs R HIA hc = hflag asegs R HIA h
      /\ (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hc x)
      /\ havol asegs R HIA hc <= havol asegs R HIA h + PHIpk (Z.of_nat (length (p7_blocks po)))
      /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRpk (Z.of_nat (length (p7_blocks po))) d + fr_charge d * Z.of_nat (length D)
      /\ (forall b, In b Lc -> In b LBn)
      /\ (forall b, In b LBn -> ~ In (fst b) (map fst D) -> In b Lc)
      /\ presW asegs R HIA h (Lc ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 1440)] m mc
      /\ rw_cells asegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs mc A cs
      /\ aobj asegs AL (hcs asegs R HIA h) mc A 1440
      /\ mem_inv asegs mc /\ stk asegs mc lo (bv_unsigned sp + -64).

    Ltac pinv_open CI :=
      destruct CI as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & KEEPc & HPXc & FR & CELLS & OBJc & MIc & STc).

    Local Notation POST := (pkcs7_free_postA24 asegs R HIA (PHIp7f PHIpk) (FFRp7f FFRpk)
                              h LB LBn LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A lo d m mo).
    Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).

    Ltac facts :=
      pose proof (hcs_ok asegs R HIA h) as CSOK; pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_val R) as ACV;
      pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOP; pose proof (hcs_stack asegs R HIA h) as SCS0;
      pose proof IMG as IMG'; unfold asan_img_ok in IMG'; unfold STKp7f, STKcf in SLO;
      assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by
        (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STKpk0 NRT SPTOP HTOP; lia]);
      lazymatch goal with HHc : HM _ _ _ ?hc _ _ ?mc |- _ => pose proof (hm_wlow asegs R HIA hc _ _ mc HHc) as WLc end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L23806482211.1200000TS1R3HIA1h2sp1A2lo2DS3lo'3Hlo1a2Ha2Hs". (* [comment removed for export] *)
    #[using="HIA h lo CW DS"] Lemma obj_client_range : forall LBx lo', (forall b, In b LB -> In b LBx) -> lo' <= bv_unsigned sp ->
      client_range L (LBx ++ fdata LF) lo' A 1440.
    Proof.
      intros LBx lo' HI Hlo a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]].
      - left. clear - Hs Ha DS Hlo. lia.
      - right; left. exact Hd.
      - right; right. exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI, Hb| right; exact Hb].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L15756354262.4L18821501791.9L22069022898.5L57124690773.000000>00W00h00iS1R2lo3LOS3ALOS1B1k2B'2j'2FB1n2H12H22APS1R4DIMG1B1k4BimgS". (* [comment removed for export] *)
    #[using="R HIA DIMG h LB LF m lo HH CW LOS"] Lemma obj_apart : forall B k, In (B, k) LBn -> 0 < k -> B + k <= A \/ A + 1440 <= B.
    Proof.
      intros B k HB Hk. destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR BA]. rewrite Forall_forall in BR.
      ddestruct (BR (B, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HB)) as (B0 & _ & Bce & Bimg). cbn [fst snd] in B0, Bce, Bimg.
      pose proof (art_lo asegs R HIA) as ALO.
      eapply (client_wrange_apart L (LB ++ fdata LF) lo (htop asegs R HIA h) A 1440 B k CW); [clear; lia| exact Hk| clear - ALO LOS; lia| exact Bce| clear - Bimg DIMG; lia|].
      intros B' j' Hb'. rewrite <- app_assoc in BA. apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
      - exact (blocks_apart_app LBn (LB ++ LF) (B, k) (B', j') BA HB ltac:(apply in_app_iff; left; exact Hb')).
      - destruct (fdata_sub LF _ Hb') as ([FB n] & HF & H1 & H2). cbn [fst snd] in H1, H2.
        pose proof (blocks_apart_app LBn (LB ++ LF) (B, k) (FB, n) BA HB ltac:(apply in_app_iff; right; exact HF)) as AP. cbn [fst snd] in AP.
        clear - AP H1 H2. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L9893535660.4000009S1A1B1k1H". (* [comment removed for export] *)
    #[using="R HIA DIMG h LBn LB LF m lo HH IFF CW LOS SUB"] Lemma p7_blocks_disjoint : forall b, In b (p7_blocks po) -> 0 < snd b -> disjoint_from [(A, A + 1440)] (fst b) (snd b).
    Proof.
      intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [| exact I].
      pose proof (obj_apart B k (SUB _ Hb) Hk) as H. clear - H. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L58393483671.400000<S1R1b2B03Bce". (* [comment removed for export] *)
    #[using="Type"] Lemma blocks_below_hm : forall (hc : HST asegs R HIA) Lall mc, HM asegs R HIA hc Lall LF mc -> blocks_below Lall alloc_ceiling.
    Proof.
      intros hc Lall mc HHc b Hb. destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [BR _]. rewrite Forall_forall in BR.
      ddestruct (BR b ltac:(apply in_app_iff; left; exact Hb)) as (B0 & _ & Bce & _). clear - B0 Bce. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L12283411672.140L14106684376.140L15756354262.4  L16069803299.7  L1892436950.4   L26892418956.1  L34423640368.7  L35653441506.11 L36438381062.140L37714553091.1  L40281191306.3  L41288976216.140L44866992728.140L48206917934.1  L48429268312.140L49343544681.139L50845182722.2  L5145216728.140 L53852091175.2  L57124690773.0  L60098763854.3  L62018535662.1  L67158371251.140L8431881505.1   L861591149.2    L8722184664.140 Q15647465701.140Q18361779941.140Q21892409478.140Q27911346950.140Q31259021925.140Q32659483621.140Q33913884038.140Q36438381062.140Q3834437894.140 Q39935438854.140Q41139626469.140Q44652823653.140Q51223427429.140Q59830607717.140Q66534604422.140Q9839219590.140 00000J00d01201K01Y01]02402T03@03C03L03f04@04C04]05705>05X05_05`05j05m06G06J06P06j07E07`08C08f09A09\0:?0:b0;E0;h0<C0<^0=90=T0>70>ZS1R5STKpk3LBn2sp1A2po1D2csS1R5STKpk3LBn2sp1A2po1D2csS1R2lo3LOS3ALOS1R3HIA5PHIpk1h2po2hc3HVcS3LBn2LB2Lc2CIS2spS1R5STKpk3NRT2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R5STKpk3NRT3LBn2sp1A2lo2po3SLO3SPR2HA1D2csS1AS1R3HIA1hS1R5STKpk3LBn2sp1A2po1D2csS1R5STKpk3LBn2sp1A2po1D2csS1AS1R5STKpk3LBn2sp1A2po1D2csS1R5STKpk3LBn2sp1A2po1D2csS2sp2loS1R5STKpk3LBn2sp1A2po1D2csS2cs2SZSS1R2lo3LOSS1RS1R5STKpk3LBn2sp1A2po1D2csS1AS1d2D0S1R5STKpk3LBn2sp1A2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3LBn2sp2lo2po1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2csS1R5STKpk3NRT3LBn2sp2lo2po3SLO1D2cs". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ PK STKpk HMND NRT pj HH LIVE NDn IFF CW DS LOS SLO SP16 SPTOP SPR UWO ND HA D0 LENk"] Lemma tail_97cac : forall D cs Lc mc moc hc (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
      pinv D cs Lc mc moc hc -> Z.of_nat (cells_size cs) = 1440 -> Z.of_nat (length D) <= Z.of_nat (length (p7_blocks po)) ->
      aevtS asegs POST
        (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x982f0) fc None mc (seg_rom asegs)) moc).
    Proof.
      intros D cs Lc mc moc hc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 CI SZ LD. pinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR STc (bv_unsigned sp).
      apply rw_cells_CB_of in CELLS; [| clear - SZ; lia]. rewrite <- (Nat2Z.id (cells_size cs)), SZ in CELLS. change (Z.to_nat 1440) with (Z.to_nat 1440) in CELLS.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m1 end.
      pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ. specialize SPZ with (h := hc). rewrite HTc in SPZ.
      eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
      { eapply SPZ with (LB := Lc ++ LB) (LF := LF) (A := A) (n := 1440) (lo := lo);
         first [ exact HHc | exact CELLS | exact HA | exact LOS | exact OBJcc | exact DS | exact SP16 | reflexivity
               | lazymatch goal with
                 | |- 0 <= 1440 => clear; lia
                 | |- 1440 < _ => clear; lia
                 | |- stk _ m1 lo _ => assumption
                 | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                 | |- _ <= htop _ _ _ _ => exact SPTOP
                 | |- mem_inv _ m1 => assumption
                 | |- client_wrange _ _ _ _ A 1440 => eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact CW| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]]]; clear - LOS; lia
                 end
               | match goal with |- ?g => idtac "PZT-LEFT:" g end ]. }
      clear SPZ. cbv beta. intros ms' PO.
      ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & CZ2 & ST2 & HH2).
      change (Z.to_nat 1440) with 1440%nat in CZ2.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold pkcs7_free_postA24, P_pkcs7_top.PKCS7_SIZE.
      deexists 15. dexists m2, mo9, hc, Lc.
      split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
      split.
      { (* [comment removed for export] *)
        lazymatch type of HPXc with presW _ _ _ _ _ _ _ _ _ _ ?mq =>
          assert (HPX2 : presW asegs R HIA h (Lc ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 1440)] m m2) end.
        { eapply presW_munch; [exact HPXc| exact MU2| exact WM2| |].
          - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OBJc)| clear; lia| clear; lia]|].
            apply Forall_cons; [cbn [fst snd]; exact SCS| apply Forall_nil].
          - apply Forall_cons; [cbn [fst snd]; apply wcover_inside; cbn; clear; lia|].
            apply Forall_cons; [cbn [fst snd]; eapply wcover_of_wlow; [ddestruct HPXc as (_ & _ & _ & BL); split; [exact BL| apply (art_data_lo asegs R HIA)]| clear - ALO LOS; lia| clear; lia]| apply Forall_nil]. }
        eapply presA_weaken; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPX2)| intros b Hb; apply in_app_iff; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
      split; [unfold PHIp7f; rewrite LENk; clear - HVc; lia|].
      split; [unfold FFRp7f; rewrite ?(Z.max_r 0 (fr_charge d)) by (unfold fr_charge; clear - D0; lia); rewrite LENk; unfold fr_charge in *; clear - HFRc LD D0; nia|].
      split; [unfold pkcs7_zero; exact CZ2|].
      (* [comment removed for export] *)
      assert (NDLc : List.NoDup Lc).
      { apply NoDup_of_map_fst. pose proof (HMND _ _ _ _ HHc) as NDx. rewrite map_app in NDx. apply List.NoDup_app_remove_r in NDx. exact NDx. }
      split; [apply List.NoDup_incl_length; [exact NDLc| intros b Hb; exact (SUBLc b Hb)]|]. split; [exact HH2|].
      (* [comment removed for export] *)
      rewrite !cnt24_app. pose proof (cnt24_incl Lc LBn NDLc ltac:(intros b Hb; exact (SUBLc b Hb))) as CI. clear - CI. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    
    #[using="PK pj LIVE IFF ND SUB"] Lemma pinv_seg_in D S Rr cs Lc mc moc hc :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ S ++ Rr -> forall b, In b S -> In b Lc.
    Proof.
      intros CI E b Hb. ddestruct CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEEP & _).
      apply KEEP; [apply SUB; rewrite E; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      pose proof ND as N. rewrite E, !map_app in N.
      apply (NoDup_app_notin_l _ _ (fst b) N). apply in_or_app. left. apply in_map. exact Hb.
    Qed.

    #[using="UWO D0"] Lemma pinv_skip D S cs Lc mc moc hc : pinv D cs Lc mc moc hc -> pinv (D ++ S) cs Lc mc moc hc.
    Proof.
      intros CI. ddestruct CI as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8v & C9 & C10 & KEEP & Crest).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8v (conj _ (conj C10 (conj _ Crest))))))))))).
      - rewrite app_length, Nat2Z.inj_add. unfold fr_charge in *. clear - C9 D0. nia.
      - intros b Hb Hn. apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
    Qed.

    
    #[using="Type"] Lemma pinv_remodel D cs Lc mc moc hc mo' : pinv D cs Lc mc moc hc -> HK asegs R HIA hc mo' -> mo_frame moc mo' -> pinv D cs Lc mc mo' hc.
    Proof.
      intros CI HK' MF'. ddestruct CI as (C1 & C2 & C3 & Crest). split; [exact C1|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact C3| exact MF']| exact Crest].
    Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L40281191306.3L48507982664.8L59440733340.1L62018535662.1L67996112456.100000900T00X00[00_S1R3HIA1hS1R5STKpk3NRT2sp2lo3LOS3SLOS2spS1RS2sp". (* [comment removed for export] *)
    #[using="NEEDF NEEDM STKpk NRT CW DS LOS SLO"] Lemma pinv_after D S cs cs' Lc L' mc moc hc m' mo' (h' : HST asegs R HIA) X' :
      pinv D cs Lc mc moc hc ->
      (forall b, In b L' -> In b Lc) -> (forall b, In b Lc -> ~ In (fst b) (map fst S) -> In b L') ->
      HM asegs R HIA h' (L' ++ LB) LF m' -> HK asegs R HIA h' mo' -> mo_frame moc mo' ->
      htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
      (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
      havol asegs R HIA h' <= havol asegs R HIA h + PHIpk (Z.of_nat (length (p7_blocks po))) ->
      hfr asegs R HIA h' <= hfr asegs R HIA h + FFRpk (Z.of_nat (length (p7_blocks po))) d + fr_charge d * Z.of_nat (length (D ++ S)) ->
      presA asegs R (L' ++ LB) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hc) X' mc m' ->
      (forall x, outside [(A, A + 1440)] x -> outside X' x) -> disjoint_from X' (bv_unsigned sp + -64) 64 ->
      rw_cells asegs m' A cs' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -64) ->
      pinv (D ++ S) cs' L' m' mo' h'.
    Proof.
      intros CI HS HKP HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP XO XD C' MI' ST'.
      ddestruct CI as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & KEEPc & HPXc & FR & CELLS & OBJc & MIc & STc).
      assert (SUBL' : forall b, In b (L' ++ LB) -> In b (Lc ++ LB)) by (apply lb_sub_app; exact HS).
      pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. unfold STKp7f, STKcf in SLO.
      split; [exact HH'|]. split; [exact HK'|]. split; [eapply mo_frame_trans; eassumption|].
      split; [congruence|]. split; [congruence|]. split; [congruence|].
      split; [intros x Hx; apply HCS', HCSc, Hx|].
      split; [exact HV'|]. split; [exact HFR'|].
      split; [intros b Hb; apply SUBLc, HS, Hb|].
      split.
      { intros b Hb Hn. apply HKP.
        - apply KEEPc; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
        - intros C. apply Hn. rewrite map_app. apply in_or_app. right. exact C. }
      split; [eapply presW_call; [eapply (presW_sub_blocks_fn asegs R HIA); [exact HPXc| exact SUBL']| exact HP| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HSc; clear; lia| exact XO]|].
      split; [eapply presA_rw_cells; [exact HP| exact FR| apply client_range_stack; cbn; clear; lia| exact XD]|].
      split; [exact C'|].
      split; [eapply presA_aobj0; [exact CSOK| exact HP| exact OBJc| intros x Hx; rewrite HSc; eapply hcs_below_top; exact Hx| right; split; [apply obj_client_range; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]| clear - LOS SLO STKpk0 NRT; lia]]|].
      split; [exact MI'| exact ST'].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L17450493156.108L4942181911.9   L67996112456.1  00000E00e00iS3LBn2sp1A2po1D2Rr2csS1R3HIA5PHIpk1h2po2hc2h'3HV'3HVcS2sp". (* [comment removed for export] *)
    #[using="NEEDF NEEDM PK STKpk NRT pj LIVE IFF CW DS LOS SLO ND SUB"] Lemma pinv_after_free D a n Rr cs Lc mc moc hc m' mo' (h' : HST asegs R HIA) :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ [(a, n)] ++ Rr ->
      HM asegs R HIA h' (lb_remove a (Lc ++ LB)) LF m' -> HK asegs R HIA h' mo' -> mo_frame moc mo' ->
      htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
      (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
      havol asegs R HIA h' <= havol asegs R HIA hc + AVOL_CALL -> hfr asegs R HIA h' <= hfr asegs R HIA hc + fr_charge d ->
      presA asegs R (lb_remove a (Lc ++ LB)) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -64) -> Z.of_nat (cells_size cs) = 1440 ->
      pinv (D ++ [(a, n)]) cs (lb_remove a Lc) m' mo' h'.
    Proof.
      intros CI E HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP MI' ST' SZ.
      assert (HINa : In a (map fst Lc)).
      { replace a with (fst (a, n)) by reflexivity. apply in_map. eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI E). left. reflexivity. }
      rewrite (lb_remove_app_l a Lc LB HINa) in HH', HP.
      assert (LEN : Z.of_nat (length (p7_blocks po)) = Z.of_nat (length D) + 1 + Z.of_nat (length Rr)) by (rewrite E, !app_length; cbn [length]; lia).
      pose proof CI as CI'. ddestruct CI' as (_ & _ & _ & _ & _ & _ & _ & HVc & HFRc & _ & _ & _ & _ & CELLS & _).
      eapply pinv_after with (X' := []); [exact CI| | | exact HH'| exact HK'| exact MF'| exact HT'| exact HS'| exact HF'| exact HCS'| | | exact HP| intros x _; exact I| exact I
        | eapply presA_rw_cells; [exact HP| exact CELLS| rewrite SZ; apply obj_client_range; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]| exact I] | exact MI'| exact ST'].
      - intros b Hb. eapply In_lb_remove. exact Hb.
      - intros b Hb Hn. apply In_lb_remove_keep'; [exact Hb|]. intros C. apply Hn. left. symmetry. exact C.
      - unfold AVOL_CALL in HV'. clear - HV' HVc. lia.
      - rewrite app_length, Nat2Z.inj_add. cbn [length]. unfold fr_charge in *. clear - HFR' HFRc D0. nia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L14945532690.6L22706556809.8L23538145875.3L23615739305.3L40818068068.9L59440733340.1L62018535662.100000B00^00j01401T01X01[S1a1n3wlo3whi4HWhiS1a1n3wlo3whi4HWlo4HWhi1x2HxS1a3wlo4HWloS1R3HIA2hcS1R5STKpk3NRT2sp2lo3LOS3ALO4SLO'S2spS1R". (* [comment removed for export] *)
    #[using="NEEDF NEEDM PK STKpk DIMG HMND NRT pj LIVE IFF CW DS LOS SLO SPR ND SUB HA"] Lemma pinv_after_store_free D a n Rr cs Lc mc moc hc wlo whi m0 m' mo' (h' : HST asegs R HIA) :
      pinv D cs Lc mc moc hc -> p7_blocks po = D ++ [(a, n)] ++ Rr ->
      munch [(wlo, whi)] mc m0 -> wmono asegs mc m0 -> a <= wlo -> whi <= a + n ->
      HM asegs R HIA h' (lb_remove a (Lc ++ LB)) LF m' -> HK asegs R HIA h' mo' -> mo_frame moc mo' ->
      htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
      (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
      havol asegs R HIA h' <= havol asegs R HIA hc + AVOL_CALL -> hfr asegs R HIA h' <= hfr asegs R HIA hc + fr_charge d ->
      presA asegs R (lb_remove a (Lc ++ LB)) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hc) [] m0 m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -64) -> Z.of_nat (cells_size cs) = 1440 ->
      pinv (D ++ [(a, n)]) cs (lb_remove a Lc) m' mo' h'.
    Proof.
      intros CI E MU WM HWlo HWhi HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP MI' ST' SZ.
      assert (HINb : In (a, n) Lc) by (eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI E); left; reflexivity).
      pose proof CI as CI'. destruct CI' as (HHc & _).
      pose proof (art_lo asegs R HIA) as ALO. pose proof SLO as SLO'. unfold STKp7f, STKcf in SLO'.
      assert (HP0 : presA asegs R (lb_remove a (Lc ++ LB)) LF (bv_unsigned sp + -64) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m0).
      { eapply (presA_drop_freed R HIA DIMG LF sp A HA SPR (Lc ++ LB) mc hc a n m0 _ _ HHc ltac:(apply in_app_iff; left; exact HINb) (HMND _ _ _ _ HHc));
          [clear - ALO LOS SLO' STKpk0 NRT; lia|].
        eapply presA_weaken with (W := [(wlo, whi)]) (LB := lb_remove a (Lc ++ LB)) (LF := LF) (SP := bv_unsigned sp + -64) (SSP := arl_stklo R) (TOP := hstkhi asegs R HIA hc);
            [ eapply (presA_of_munch asegs R) with (CS := hcs asegs R HIA hc);
                [ exact (hcs_ok asegs R HIA hc)
                | apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (hm_blocks_cs asegs R HIA hc _ _ _ HHc a n ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HINb))| clear - HWlo; lia| clear - HWlo HWhi; lia]| apply Forall_nil]
                | intros c Hc; eapply (cshd_hcs asegs R HIA hc (Lc ++ LB) LF mc (arl_stklo R) c HHc ltac:(clear; lia));
                  destruct Hc as [Hs|[(b & Hb & Hx)|Hr]]; [left; exact Hs| right; left; exists b; split; [eapply In_lb_remove; exact Hb| exact Hx]| right; right; exact Hr]
                | exact MU | exact WM ]
            | intros b Hb; exact Hb | intros b Hb; exact Hb | clear; lia | clear; lia | clear; lia
            | intros x Hx; cbn [outside] in Hx |- *; clear - Hx HWlo HWhi; lia ]. }
      eapply pinv_after_free; [exact CI| exact E| exact HH'| exact HK'| exact MF'| exact HT'| exact HS'| exact HF'| exact HCS'| exact HV'| exact HFR'
                              | eapply presA_trans; [exact HP0| exact HP] | exact MI'| exact ST'| exact SZ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L26892418956.1000004S2sp". (* [comment removed for export] *)
    #[using="Type"] Lemma pinv_presx D cs Lc mc moc hc : pinv D cs Lc mc moc hc ->
      heap_presx asegs L (Lc ++ LB) (bv_unsigned sp) [(A, A + 1440)] m mc.
    Proof.
      intros CI. ddestruct CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPX & _).
      eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPX))| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    
    
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    Ltac leave := let mo1 := fresh "mo" in let HK1 := fresh "HKg" in let MF1 := fresh "MFg" in intros mo1 [HK1 MF1].

    (* [comment removed for export] *)
    Ltac free_node cur sz E1 LEN1 HINc retpc :=
      lazymatch goal with |- _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) LF m1, CI0 : pinv _ _ ?Lc m1 ?moc ?hc, MIc : mem_inv _ m1,
                          HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _, SZ : Z.of_nat (cells_size _) = 1440 |- _ =>
      replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite HFREE; reflexivity);
      eapply aevtA_call;
      [ let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in
        intros mo1 [HK1 MF1];
        eapply (heapA_free asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := LF) (A := cur) (n := sz) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKp7f, STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
          lazymatch goal with HTc : htop _ _ _ hc = _, HSc : hstkhi _ _ _ hc = _ |- _ => rewrite ?HTc, ?HSc | _ => idtac end;
          first [ exact HHc | exact HK1 | apply in_app_iff; left; exact HINc | exact LOS | exact TP | exact MIc | reflexivity
                | lazymatch goal with
                  | |- stk _ m1 lo _ => assumption
                  | |- lo <= _ => unfold STKp7f, STKcf in SLO; clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; unfold PHIp7f in BUD;
                        let PH := fresh "PH" in pose proof (PHIpk0 (Z.of_nat (length (p7_blocks po))) ltac:(clear; lia)) as PH;
                        let B' := fresh "BUD'" in pose proof BUD as B'; rewrite LENk in B'; clear - HVc B' PH; lia
                  | |- uwc _ _ _ _ _ _ _ => rewrite (unsigned_lit A) by (clear - HA AB; lia); eapply uw_obj_uwc; [exact UWO| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRp7f in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia);
                        let B' := fresh "BUDF'" in pose proof BUDF as B'; rewrite LENk in B'; unfold fr_charge in *; clear - HFRc B' LEN1 D0; nia
                  end
                | match goal with |- ?g => idtac "FREE-NODE-LEFT:" g end ]
      | cbv beta;
        let ms' := fresh "ms'" in let mox := fresh "mox" in let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in let PO := fresh "PO" in
        intros ms' mox (mo1 & [HK1 MF1] & PO);
        let ms2 := fresh "ms2" in let mo2 := fresh "mo2" in let EE := fresh "EE" in
        destruct PO as (ms2 & mo2 & EE & PO); injection EE as ?Em1 ?Em2; subst ms2 mo2;
        unfold call_postA in PO;
        let m' := fresh "m'" in let E0 := fresh "E0" in
        destruct PO as (?w0 & ?w1 & ?w2 & ?wa0 & ?wa1 & ?wa2 & ?wa3 & ?wa4 & ?wa5 & ?wa6 & ?wa7 & ?w3 & ?w4 & ?w5 & ?w6 & m' & E0 & PO); subst ms';
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKp7f, STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
        let h' := fresh "h'" in
        destruct PO as (?MI' & ?ST' & ?MF' & ?HP' & h' & ?HT' & ?HS' & ?HF' & ?HK' & ?HCS' & ?HV' & ?HFR' & ?HH');
        fix_ret retpc;
        lazymatch goal with MI' : mem_inv _ m', ST' : stk _ m' lo _, MF' : mo_frame mo1 ?mo', HP' : presA _ _ _ _ _ _ _ _ m1 m',
                            HT' : htop _ _ _ h' = _, HS' : hstkhi _ _ _ h' = _, HF' : hflag _ _ _ h' = _, HK' : HK _ _ _ h' ?mo',
                            HCS' : forall x, _ -> hcs _ _ _ h' x, HV' : havol _ _ _ h' <= _, HFR' : hfr _ _ _ h' <= _, HH' : HM _ _ _ h' _ LF m' |- _ =>
          let CI1 := fresh "CI1" in
          pose proof (pinv_after_free _ _ _ _ _ _ _ _ _ _ _ _ (pinv_remodel _ _ _ _ _ _ _ CI0 HK1 MF1) E1 HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP' MI' ST' SZ) as CI1;
          apply (aevtA_enter asegs (KF asegs R HIA h' mo') _ _ _ (conj HK' (mo_frame_refl mo')));
          repeat match goal with Lw : ainv_laws _ _ |- _ => clear Lw | Kv : kinv_laws _ _ _ |- _ => clear Kv end;
          pose proof (AIh_laws asegs R HIA h') as LAWS; pose proof (KF_kinv asegs R HIA h' mo') as KINV
        end ]
      end end.

    (* [comment removed for export] *)
    Ltac free_node_st cur sz E1 LEN1 HINc retpc MU WM :=
      lazymatch goal with |- _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) LF m1, CI0 : pinv _ _ ?Lc _ ?moc ?hc, MIc : mem_inv _ m1,
                          HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _, SZ : Z.of_nat (cells_size _) = 1440 |- _ =>
      replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite HFREE; reflexivity);
      eapply aevtA_call;
      [ let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in
        intros mo1 [HK1 MF1];
        eapply (heapA_free asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := LF) (A := cur) (n := sz) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKp7f, STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
          lazymatch goal with HTc : htop _ _ _ hc = _, HSc : hstkhi _ _ _ hc = _ |- _ => rewrite ?HTc, ?HSc | _ => idtac end;
          first [ exact HHc | exact HK1 | apply in_app_iff; left; exact HINc | exact LOS | exact TP | exact MIc | reflexivity
                | lazymatch goal with
                  | |- stk _ m1 lo _ => assumption
                  | |- lo <= _ => unfold STKp7f, STKcf in SLO; clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; unfold PHIp7f in BUD;
                        let PH := fresh "PH" in pose proof (PHIpk0 (Z.of_nat (length (p7_blocks po))) ltac:(clear; lia)) as PH;
                        let B' := fresh "BUD'" in pose proof BUD as B'; rewrite LENk in B'; clear - HVc B' PH; lia
                  | |- uwc _ _ _ _ _ _ _ => rewrite (unsigned_lit A) by (clear - HA AB; lia); eapply uw_obj_uwc; [exact UWO| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRp7f in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia);
                        let B' := fresh "BUDF'" in pose proof BUDF as B'; rewrite LENk in B'; unfold fr_charge in *; clear - HFRc B' LEN1 D0; nia
                  end
                | match goal with |- ?g => idtac "FREE-NODE-LEFT:" g end ]
      | cbv beta;
        let ms' := fresh "ms'" in let mox := fresh "mox" in let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in let PO := fresh "PO" in
        intros ms' mox (mo1 & [HK1 MF1] & PO);
        let ms2 := fresh "ms2" in let mo2 := fresh "mo2" in let EE := fresh "EE" in
        destruct PO as (ms2 & mo2 & EE & PO); injection EE as ?Em1 ?Em2; subst ms2 mo2;
        unfold call_postA in PO;
        let m' := fresh "m'" in let E0 := fresh "E0" in
        destruct PO as (?w0 & ?w1 & ?w2 & ?wa0 & ?wa1 & ?wa2 & ?wa3 & ?wa4 & ?wa5 & ?wa6 & ?wa7 & ?w3 & ?w4 & ?w5 & ?w6 & m' & E0 & PO); subst ms';
        rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKp7f, STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
        let h' := fresh "h'" in
        destruct PO as (?MI' & ?ST' & ?MF' & ?HP' & h' & ?HT' & ?HS' & ?HF' & ?HK' & ?HCS' & ?HV' & ?HFR' & ?HH');
        fix_ret retpc;
        lazymatch goal with MI' : mem_inv _ m', ST' : stk _ m' lo _, MF' : mo_frame mo1 ?mo', HP' : presA _ _ _ _ _ _ _ _ m1 m',
                            HT' : htop _ _ _ h' = _, HS' : hstkhi _ _ _ h' = _, HF' : hflag _ _ _ h' = _, HK' : HK _ _ _ h' ?mo',
                            HCS' : forall x, _ -> hcs _ _ _ h' x, HV' : havol _ _ _ h' <= _, HFR' : hfr _ _ _ h' <= _, HH' : HM _ _ _ h' _ LF m' |- _ =>
          let CI1 := fresh "CI1" in
          pose proof (pinv_after_store_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pinv_remodel _ _ _ _ _ _ _ CI0 HK1 MF1) E1 MU WM ltac:(clear; lia) ltac:(clear; lia) HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP' MI' ST' SZ) as CI1;
          apply (aevtA_enter asegs (KF asegs R HIA h' mo') _ _ _ (conj HK' (mo_frame_refl mo')));
          repeat match goal with Lw : ainv_laws _ _ |- _ => clear Lw | Kv : kinv_laws _ _ _ |- _ => clear Kv end;
          pose proof (AIh_laws asegs R HIA h') as LAWS; pose proof (KF_kinv asegs R HIA h' mo') as KINV
        end ]
      end end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L12286320127.3  L1595391607.9   L17991598320.159L26436464977.1  L28813939468.3  L29627432490.1  L30985182006.11 L33658634174.7  L35653441506.11 L40228640085.0  L46425565324.194L47028033785.160L47699686939.1  L57840041431.5  L60098763854.3  L64723157409.0  L66151427842.16 L6698450252.3   L861591149.2    L9175481134.1   Q25019582490.161Q29612090062.161Q32352309670.162Q47700973017.162Q47713708799.161Q61338516829.16200000;00Y01K01N01W01\02@02W03703803f04P04U04g05105205M05X05^05b06G06l07g08L09109VS1A3cur3APcS1R3HIA5PHIpk1h2po2hc3HVc4BUD'S1R5STKpk3LBn2sp1A2po2cs3cur1D4HPOS3pre2nx4post2NBS1AS1A2HA2ABS3curS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R5STKpk3NRT2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3LBn2sp1A2po2cs3cur1D3pre2nx4post3NXBS1R5STKpk3LBn2sp1A2po2cs3cur1D3pre2nx4postS3curS1R3HIA1h2sp5SPTOPS1R2lo3LOSSS2sp2r04SP161q1r1H2H02q02H4S2Rr4rest1DS1d2D0S2poS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2sp1A2po3SPR2HA2cs3cur1D4HALn4HPOS3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4post". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PK STKpk PHIpk0 DIMG NRT pj HH LIVE NDn IFF CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND SUB HA AB D0 LENk"] Lemma loopC : forall (w9 w18 w20 w21 : word) (Rr : list blk) cs (names : list Z) (cur : Z) D Lc mc moc hc
                         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
      names <> [] -> name_chain asegs (fun _ => True) m (LBn ++ LB) cur names ->
      p7_blocks po = D ++ SNAME names ++ Rr ->
      pinv D cs Lc mc moc hc -> Z.of_nat (cells_size cs) = 1440 ->
      (forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME names) cs Lc' mc' moc' hc' ->
          aevtS asegs POST
            (mkCfg (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) w9 y10 y11 y12 y13 y14 y15 y16 y17 w18 (Z_to_bv 64 (al_sb AL)) w20 w21 y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x982d4) fc None mc' (seg_rom asegs)) moc')) ->
      aevtS asegs POST
        (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) w9 (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 w18 (Z_to_bv 64 (al_sb AL)) w20 w21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x982a8) fc None mc (seg_rom asegs)) moc).
    Proof.
      intros w9 w18 w20 w21 Rr cs names. induction names as [|n1 rest IH];
        intros cur D Lc mc moc hc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 HNE HC E CI SZ K; [congruence|].
      pose proof CI as CI0. pinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & _ & HALn & HPOS & pre & nx & post & H1 & H2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in H2.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
      pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC') as NXB.
      assert (HINc : In (cur, 64) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 E). unfold SNAME. cbn [map]. left. reflexivity. }
      pose proof (obj_apart cur 64 (SUBLc _ HINc) ltac:(clear; lia)) as APc.
      assert (HNX : rw_cells asegs mc (cur + 48) [C8 (Z_to_bv 64 nx)]).
      { eapply presA_rw_cells; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPXc)| exact HNX0| |].
        - eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; left; exact HINc| clear; lia| cbn [cells_size csize Nat.add]; clear; lia].
        - cbn [cells_size csize Nat.add disjoint_from]. clear - APc. lia. }
      clear HNX0 HNODE.
      pose proof (hm_aobj_block asegs R HIA hc (Lc ++ LB) LF mc cur 64 HHc ltac:(apply in_app_iff; left; exact HINc)) as OA.
      assert (E1 : p7_blocks po = D ++ [(cur, 64)] ++ (SNAME rest ++ Rr)) by (rewrite E; unfold SNAME, NAME_SIZE; cbn [map app]; reflexivity).
      assert (LEN1 : Z.of_nat (length D) + 1 <= Z.of_nat (length (p7_blocks po))) by (rewrite E1, !app_length; cbn [length]; clear; lia).
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      free_node cur 64 E1 LEN1 HINc 0x982cc.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KN; zify_cond KN.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KN by (clear - NXB; lia).
        destruct (chain_nonnull asegs _ _ _ _ _ _ _ HC' KN) as (a2 & rest2 & ER).
        leave. eapply (IH nx (D ++ [(cur, 64)])); [rewrite ER; congruence| exact HC'| rewrite E1, <- app_assoc; reflexivity| eapply pinv_remodel; [exact CI1| eassumption| eassumption]| exact SZ|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 CI'.
        eapply K. rewrite <- app_assoc in CI'. exact CI'.
      - rewrite ?unsigned_lit in KN by (clear - NXB; lia).
        pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst rest.
        (* [comment removed for export] *)
        leave. eapply K. eapply pinv_remodel; [| eassumption| eassumption].
        replace (D ++ SNAME [cur]) with (D ++ [(cur, 64)]) by (unfold SNAME, NAME_SIZE; reflexivity). exact CI1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L12286320127.3  L1326225569.0   L1595391607.9   L17991598320.158L26436464977.1  L28813939468.3  L29627432490.1  L30985182006.11 L33658634174.7  L35653441506.11 L40228640085.0  L46425565324.193L47028033785.159L47699686939.1  L57840041431.5  L60098763854.3  L66151427842.16 L6698450252.3   L861591149.2    L9175481134.1   Q25019582490.160Q29612090062.160Q32352309670.161Q47700973017.161Q47713708799.160Q61338516829.16100000;00<00Z01L01O01X01]02A02X03803903g04Q04V04h05205M05X05^05b06G06l07g08L09109VS1A3cur3APcSS1R3HIA5PHIpk1h2po2hc3HVc4BUD'S1R5STKpk3LBn2sp1A2po2cs3cur1D4HPOS3pre2nx4post2NBS1AS1A2HA2ABS3curS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R5STKpk3NRT2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3LBn2sp1A2po2cs3cur1D3pre2nx4post3NXBS1R5STKpk3LBn2sp1A2po2cs3cur1D3pre2nx4postS3curS1R3HIA1h2sp5SPTOPS1R2lo3LOSS2sp2r04SP161q1r1H2H02q02H4S2Rr4rest1DS1d2D0S2poS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2sp1A2po3SPR2HA2cs3cur1D4HALn4HPOS3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4postS1R5STKpk3LBn2po2cs3cur1D3pre2nx4post". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PK STKpk PHIpk0 DIMG NRT pj HH LIVE NDn IFF CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND SUB HA AB D0 LENk"] Lemma loopA : forall (w9 w18 w20 : word) (Rr : list blk) cs (names : list Z) (cur : Z) D Lc mc moc hc
                         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
      names <> [] -> name_chain asegs (fun _ => True) m (LBn ++ LB) cur names ->
      p7_blocks po = D ++ SNAME names ++ Rr ->
      pinv D cs Lc mc moc hc -> Z.of_nat (cells_size cs) = 1440 ->
      (forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME names) cs Lc' mc' moc' hc' ->
          aevtS asegs POST
            (mkCfg (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) w9 y10 y11 y12 y13 y14 y15 y16 y17 w18 (Z_to_bv 64 (al_sb AL)) w20 y21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9825c) fc None mc' (seg_rom asegs)) moc')) ->
      aevtS asegs POST
        (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) w9 (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 w18 (Z_to_bv 64 (al_sb AL)) w20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x98230) fc None mc (seg_rom asegs)) moc).
    Proof.
      intros w9 w18 w20 Rr cs names. induction names as [|n1 rest IH];
        intros cur D Lc mc moc hc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 HNE HC E CI SZ K; [congruence|].
      pose proof CI as CI0. pinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      destruct (chain_uncons asegs _ _ _ _ _ _ _ _ HC) as (<- & _ & HALn & HPOS & pre & nx & post & H1 & H2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in H2.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
      pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HC') as NXB.
      assert (HINc : In (cur, 64) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 E). unfold SNAME. cbn [map]. left. reflexivity. }
      pose proof (obj_apart cur 64 (SUBLc _ HINc) ltac:(clear; lia)) as APc.
      assert (HNX : rw_cells asegs mc (cur + 48) [C8 (Z_to_bv 64 nx)]).
      { eapply presA_rw_cells; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPXc)| exact HNX0| |].
        - eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; left; exact HINc| clear; lia| cbn [cells_size csize Nat.add]; clear; lia].
        - cbn [cells_size csize Nat.add disjoint_from]. clear - APc. lia. }
      clear HNX0 HNODE.
      pose proof (hm_aobj_block asegs R HIA hc (Lc ++ LB) LF mc cur 64 HHc ltac:(apply in_app_iff; left; exact HINc)) as OA.
      assert (E1 : p7_blocks po = D ++ [(cur, 64)] ++ (SNAME rest ++ Rr)) by (rewrite E; unfold SNAME, NAME_SIZE; cbn [map app]; reflexivity).
      assert (LEN1 : Z.of_nat (length D) + 1 <= Z.of_nat (length (p7_blocks po))) by (rewrite E1, !app_length; cbn [length]; clear; lia).
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      free_node cur 64 E1 LEN1 HINc 0x98254.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KN; zify_cond KN.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KN by (clear - NXB; lia).
        destruct (chain_nonnull asegs _ _ _ _ _ _ _ HC' KN) as (a2 & rest2 & ER).
        leave. eapply (IH nx (D ++ [(cur, 64)])); [rewrite ER; congruence| exact HC'| rewrite E1, <- app_assoc; reflexivity| eapply pinv_remodel; [exact CI1| eassumption| eassumption]| exact SZ|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 CI'.
        eapply K. rewrite <- app_assoc in CI'. exact CI'.
      - rewrite ?unsigned_lit in KN by (clear - NXB; lia).
        pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst rest.
        leave. eapply K. eapply pinv_remodel; [| eassumption| eassumption].
        replace (D ++ SNAME [cur]) with (D ++ [(cur, 64)]) by (unfold SNAME, NAME_SIZE; reflexivity). exact CI1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Ltac blocks_eq E := rewrite E; cbn [signer_blocks fst snd]; unfold SNAME, SIGNER_SIZE, NAME_SIZE; repeat rewrite <- app_assoc; cbn [map app]; reflexivity.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@D38544389549.186D66069387920.186D9520186312.186 L14022206393.2  L14686260540.1  L16888294652.158L24425476304.2  L26436464977.1  L28813939468.3  L30985182006.11 L32027975233.0  L33658634174.7  L35653441506.11 L38308634325.0  L38790691617.0  L38965490467.1  L39924338763.9  L4689685756.158 L5457211416.1   L5731133105.1   L57840041431.5  L60098763854.3  L6393052521.160 L64982588698.3  L66151427842.16 L6698450252.3   L861591149.2    L9175481134.1   Q1113788111.161 Q1113788111.183 Q11801279589.186Q14480193773.182Q14492448884.160Q22090054029.161Q22090054029.183Q23405925126.160Q29402318989.161Q34333372241.183Q3741646287.161 Q45082815691.161Q45095277549.160Q50775916550.160Q50780176543.182Q52041007307.184Q5455387083.161 Q5455387083.183 Q5455472244.182 Q5468120813.160 Q56910164340.160Q66071302288.185Q9517943240.185 00000100b01S01Y01\02@02H02K02T03803903P04004104204504T05805;05>05P05Z06C06L06g06o07507907S08008\09909S0:C0;60;P0<@0<e0=?0=Y0>30>M0>j0?P0?j0@G0@d0A>0AX0BD0C0FS1R5STKpk3LBn2sp1A2po2cs2ns1a1D2NB2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp1A2po2cs2ns1a1D2NB2HB5Ha_st5Hl_stS2ns1DS1aS1R5STKpk3LBn2sp1A2po2cs1a1D4HPOS2NBS3nxt2B2S1AS1A2HA2ABS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0SS1R5STKpk3NRT2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSSS1aS1R3HIA5PHIpk1h2po3hc'3HVc4BUD'S1R5STKpk3LBn2sp1A2po2cs1a1D4HPOS2NBS1aS1aS1R3HIA1h2sp5SPTOPS1R2lo3LOSS1R5STKpk3LBn2sp1A2po2cs1a1D5inext2NB3INBS1A1a3APaS2sp2r04SP161q1r1H2H02q02H4S2ns1r1DS1d2D0S2poS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NB2HB5Ha_st5Hl_stS1R5STKpk3LBn2po2cs2ns1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2sp1A2po3SPR2HA2cs1a1D4HALs4HPOS2NBS1R5STKpk3LBn2sp1A2po3SPR2HA2cs2ns1a1D4HALs4HPOS2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2sp1A2po3SPR2HA2cs1a1D4HALs4HPOS2NBS1R5STKpk3LBn2po2cs2ns1a1D4HPOS2NB2HBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NB2HB5Ha_stS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs1a1D2NBS1R5STKpk3LBn2po2cs2ns1a1D2NB2HB5Ha_st5Hl_stS1R5STKpk3LBn2po2cs2ns1a1D2NB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PZ PK STKpk PHIpk0 DIMG HMND NRT pj HH LIVE NDn IFF CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND SUB HA AB D0 LENk"] Lemma loopB : forall cs, Z.of_nat (cells_size cs) = 1440 ->
      forall (sg : list (Z * list Z)) (a : Z) D Lc mc moc hc
             (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
      sg <> [] -> signer_chain asegs m (LBn ++ LB) a sg ->
      p7_blocks po = D ++ signer_blocks sg ++ [] ->
      pinv D cs Lc mc moc hc ->
      aevtS asegs POST
        (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 a) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (al_sb AL)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x9826c) fc None mc (seg_rom asegs)) moc).
    Proof.
      intros cs SZ sg. induction sg as [|[a' ns] r IH];
        intros a D Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 HNE HC E CI; [congruence|].
      pose proof CI as CI0. pinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      destruct (signer_chain_uncons asegs _ _ _ _ _ _ HC) as (<- & _ & HALs & HPOS & inext & nxt & sj & HNODE0 & HN0 & HC').
      assert (Ea : p7_blocks po = D ++ (SNAME ns ++ [(a, 200)]) ++ (signer_blocks r ++ [])) by blocks_eq E.
      assert (HINc : In (a, 200) Lc).
      { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 Ea). apply in_or_app. right. left. reflexivity. }
      pose proof (obj_apart a 200 (SUBLc _ HINc) ltac:(clear; lia)) as APa.
      assert (HNODE : rw_cells asegs mc a (signer_cells inext nxt sj)).
      { eapply presA_rw_cells; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPXc)| exact HNODE0| |].
        - eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; left; exact HINc| clear; lia| cbn [cells_size csize Nat.add signer_cells]; clear; lia].
        - cbn [cells_size csize Nat.add signer_cells disjoint_from]. clear - APa. lia. }
      unfold signer_cells in HNODE.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. cbn [cells_size csize Nat.add] in NB.
      pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HN0) as INB.
      assert (NXB : 0 <= nxt < 2 ^ 64).
      { destruct r as [|[a2 ns2] r2]; [cbn in HC'; subst nxt; clear; lia|].
        destruct (signer_chain_uncons asegs _ _ _ _ _ _ HC') as (<- & _ & _ & _ & i2 & n2 & j2 & HR2 & _).
        pose proof (rw_cells_bound _ _ _ _ HR2) as B2. cbn [cells_size csize Nat.add signer_cells] in B2. clear - B2. lia. }
      pose proof (hm_aobj_block asegs R HIA hc (Lc ++ LB) LF mc a 200 HHc ltac:(apply in_app_iff; left; exact HINc)) as OA.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      assert (K5c : forall Lc' mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 : word),
          pinv (D ++ SNAME ns) cs Lc' mc' moc' hc' ->
          aevtS asegs POST
            (mkCfg (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 a) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (a + 80)) (Z_to_bv 64 (al_sb AL))
                            (Z_to_bv 64 nxt) (Z_to_bv 64 (Z.shiftr (a + 80) 3 + al_sb AL)) y22 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x982d4) fc None mc' (seg_rom asegs)) moc')).
      { intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31 CI'.
        pose proof CI' as CI1. clear HHc HKc MFc HTc HSc HFc HCSc HVc HFRc SUBLc KEEPc HPXc FR CELLS OBJc MIc STc CI0 WLc OBJcc CSOKc HNODE OA LAWS KINV.
        ddestruct CI' as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & KEEPc & HPXc & FR & CELLS & OBJc & MIc & STc).
        rename CI1 into CI0.
        pose proof (hcs_ok asegs R HIA hc') as CSOKc.
        assert (E1 : p7_blocks po = (D ++ SNAME ns) ++ [(a, 200)] ++ (signer_blocks r ++ [])) by blocks_eq E.
        assert (HINc' : In (a, 200) Lc').
        { eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI0 E1). left. reflexivity. }
        assert (LEN1 : Z.of_nat (length (D ++ SNAME ns)) + 1 <= Z.of_nat (length (p7_blocks po))) by (rewrite E1; rewrite !app_length; cbn [length]; clear; lia).
        (* [comment removed for export] *)
        pose proof (hm_aobj_block asegs R HIA hc' (Lc' ++ LB) LF mc' a 200 HHc ltac:(apply in_app_iff; left; exact HINc')) as OA.
        assert (INW : In (a, 200) ((Lc' ++ LB) ++ fdata LF)) by (apply in_app_iff; left; apply in_app_iff; left; exact HINc').
        destruct (blocks_below_hm _ _ _ HHc (a, 200) ltac:(apply in_app_iff; left; exact HINc')) as [_ Bce]. cbn [fst snd] in Bce.
        assert (HNODE : rw_cells asegs mc' a (signer_cells inext nxt sj)).
        { eapply presA_rw_cells; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPXc)| exact HNODE0| |].
          - eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; left; exact HINc'| clear; lia| cbn [cells_size csize Nat.add signer_cells]; clear; lia].
          - cbn [cells_size csize Nat.add signer_cells disjoint_from]. clear - APa. lia. }
        unfold signer_cells in HNODE.
        (* [comment removed for export] *)
        clear HPXc FR CELLS OBJc.
        apply (aevtA_enter asegs (KF asegs R HIA hc' moc') _ _ _ (conj HKc (mo_frame_refl moc'))).
        pose proof (AIh_laws asegs R HIA hc') as LAWS. pose proof (KF_kinv asegs R HIA hc' moc') as KINV.
        pose proof (munch_refl [(a + 80, a + 88)] mc') as MU. pose proof (wmono_refl asegs mc') as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        clear HNODE OA.
        zstep. zstep.
        free_node_st a 200 E1 LEN1 HINc' 0x982e8 MU WM.
        (* [comment removed for export] *)
        zstep. zstep. if_cases KN; zify_cond KN.
        - rewrite ?unsigned_lit in KN by (clear - NXB; lia).
          destruct (signer_chain_nonnull asegs _ _ _ _ HC' KN) as (a2 & ns2 & r2 & ER).
          leave. eapply (IH nxt ((D ++ SNAME ns) ++ [(a, 200)])); [rewrite ER; congruence| exact HC'| blocks_eq E| eapply pinv_remodel; [exact CI1| eassumption| eassumption]].
        - rewrite ?unsigned_lit in KN by (clear - NXB; lia).
          pose proof (signer_chain_null_inv asegs _ _ _ ltac:(rewrite <- KN; exact HC')) as ER. subst r.
          leave. eapply tail_97cac; [eapply pinv_remodel; [exact CI1| eassumption| eassumption]| exact SZ|].
          rewrite E1, !app_length. cbn [length]. clear. lia. }
      (* [comment removed for export] *)
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KI by (clear - INB; lia).
        pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- KI; exact HN0)) as EN. subst ns.
        leave. eapply K5c. eapply pinv_remodel; [| eassumption| eassumption]. apply pinv_skip. exact CI0.
      - rewrite ?unsigned_lit in KI by (clear - INB; lia).
        destruct (chain_nonnull asegs _ _ _ _ _ _ _ HN0 KI) as (n1 & rest & EN).
        leave. eapply (loopC (Z_to_bv 64 a) (Z_to_bv 64 (a + 80)) (Z_to_bv 64 nxt) (Z_to_bv 64 (Z.shiftr (a + 80) 3 + al_sb AL)) ([(a, 200)] ++ signer_blocks r ++ []) cs ns inext D);
          [rewrite EN; congruence| exact HN0| blocks_eq E| eapply pinv_remodel; [exact CI0| eassumption| eassumption]| exact SZ| exact K5c].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Definition RAWC : list cell :=
      [C4 (pj_rawtag pj); C4 (pj0 pj); C8 (Z_to_bv 64 (po_rawlen po)); C8 (Z_to_bv 64 (po_rawp po)); CB 40 (pj1 pj)].
    (* [comment removed for export] *)
    Definition cellsZ (inext : Z) : list cell :=
      RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj); CB 416 (zeros 416); CB 8 (pj3 pj)]
      ++ signer_cells inext (po_signers_next po) (pj_s0 pj).
    Definition D3 : list blk := [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po) ++ SNAME (po_names0 po).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@D16116793040.145D44450165448.145K13363616908.145L13357287419.2  L32027975233.0  L35653441506.11 L60098763854.3  L60837607228.2  L61569962261.1  Q11801279589.145Q16114545872.144Q16116793040.145Q16679598351.142Q2664849588.141 Q2664898315.142 Q30695267487.141Q34362328320.145Q36742008045.142Q42755330731.143Q44447922376.144Q44450165448.145Q53219435181.141Q8041752945.142 00000T01801j01k01l02L02V02]02a03B03c04D04V04h05:05L05m06M06k07L07m08?08WS1R5STKpk3LBn2sp1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp1A2po2HB5Ha_st5Hl_stS1R5STKpk3NRT3LBn2sp1A2lo2po2DS3SLO2HB5Ha_st5Hl_stFSS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R2lo3LOSS2po2B2S2poS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp1A2po3SPR2HA3HALS1R5STKpk3LBn1A2po2AB2HB5Ha_stS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn1A2po2HB5Ha_st5Hl_stS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2po2HA2HB". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PZ PK STKpk PHIpk0 DIMG HMND NRT HH LIVE NDn IFF CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND SUB HA HAL AB D0 LENk"] Lemma from_97c28 : forall Lc mc moc hc (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
      pinv D3 (cellsZ (po_issuer0_next po)) Lc mc moc hc ->
      aevtS asegs POST
        (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (po_signers_next po)) x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (A + 1320)) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr (A + 1320) 3 + al_sb AL)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x9825c) fc None mc (seg_rom asegs)) moc).
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 CI. pose proof CI as CI0. pinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
      pose proof LIVE as LV. ddestruct LV as (_ & _ & _ & _ & RP & RL & _ & _ & _ & HN0 & HSC & _).
      assert (SNB : 0 <= po_signers_next po < 2 ^ 64).
      { destruct (po_signers po) as [|[a2 ns2] r2] eqn:ES; [cbn in HSC; rewrite HSC; clear; lia|].
        destruct (signer_chain_uncons asegs _ _ _ _ _ _ HSC) as (EE & _ & _ & _ & i2 & n2 & j2 & HR2 & _).
        pose proof (rw_cells_bound _ _ _ _ HR2) as B2. cbn [cells_size csize Nat.add signer_cells] in B2. clear - B2. lia. }
      pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HN0) as INB.
      unfold cellsZ, RAWC, signer_cells in CELLS. cbn [app] in CELLS.
      assert (CWc : client_wrange L ((Lc ++ LB) ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) A 1440).
      { rewrite HTc. eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact CW| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]]]. clear - LOS; lia. }
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      pose proof (munch_refl [(A + 1320, A + 1328)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      assert (CI1 : pinv D3 (cellsZ 0) Lc m0 moc hc).
      { split; [exact HHc|]. split; [exact HKc|]. split; [exact MFc|]. split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|].
        split; [exact HCSc|]. split; [exact HVc|]. split; [exact HFRc|]. split; [exact SUBLc|]. split; [exact KEEPc|].
        split; [exact HPXc|]. split; [exact FR|]. split; [unfold cellsZ, RAWC, signer_cells; cbn [app]; exact CELLS|].
        split; [exact OBJc|]. split; [assumption| exact STc]. }
      (* [comment removed for export] *)
      zstep. if_cases KS; zify_cond KS.
      - rewrite ?unsigned_lit in KS by (clear - SNB; lia).
        pose proof (signer_chain_null_inv asegs _ _ _ ltac:(rewrite <- KS; exact HSC)) as ER.
        leave. eapply tail_97cac; [eapply pinv_remodel; [exact CI1| eassumption| eassumption]| reflexivity|].
        replace (p7_blocks po) with (D3 ++ signer_blocks (po_signers po)) by (unfold D3, p7_blocks, SNAME; repeat rewrite <- app_assoc; reflexivity).
        rewrite app_length, Nat2Z.inj_add. clear. lia.
      - rewrite ?unsigned_lit in KS by (clear - SNB; lia).
        destruct (signer_chain_nonnull asegs _ _ _ _ HSC KS) as (a2 & ns2 & r2 & ER).
        leave. eapply (loopB (cellsZ 0) eq_refl (po_signers po) (po_signers_next po) D3);
          [rewrite ER; congruence| exact HSC| unfold D3, p7_blocks, SNAME; repeat rewrite <- app_assoc; rewrite app_nil_r; reflexivity| eapply pinv_remodel; [exact CI1| eassumption| eassumption]].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Definition REST (inext : Z) : list cell := [CB 8 (pj2 pj); CB 416 (zeros 416); CB 8 (pj3 pj)] ++ signer_cells inext (po_signers_next po) (pj_s0 pj).
    Definition D2 : list blk := [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po).

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@D13554616751.132D13554616751.133D30841324822.133D35881667587.132D35881667587.133K54978542206.132K54978542206.133L11803631744.9  L11807598354.1  L12283411672.129L13301871092.129L14106684376.128L15538036464.2  L17646078182.128L21832304075.6  L22706556809.3  L26436464977.1  L26691467756.2  L28122880816.1  L28813939468.3  L28814043710.129L29150016769.2  L30064439387.10 L30985182006.11 L30987395472.11 L31056940152.128L32027975233.0  L32409531553.0  L33658634174.7  L3404525308.2   L34541106770.2  L34994544387.129L35653441506.11 L3681866161.7   L3825037791.4   L39420562502.8  L39887139444.129L40778157368.1  L40834179097.132L40870879649.0  L41288976216.129L42580453297.3  L43055530543.126L43553371276.7  L44277782651.1  L44866992728.129L45898055924.129L48429268312.129L48767683599.232L50220027580.1  L5145216728.129 L51723252737.2  L51925114228.129L52575544124.1  L53969727459.2  L54968017161.2  L56641262943.4  L57840041431.5  L57933933556.129L59308628179.3  L59308632561.3  L60098763854.3  L60837606325.2  L60837742364.129L60837743493.234L62018535662.1  L62533485541.1  L63524367375.232L63962036340.128L63972703454.2  L65337174320.1  L65857814072.1  L66151427842.16 L67158371251.129L67761081556.1  L67996112456.1  L7274816372.129 L8201234081.0   L861591149.2    L8722184664.129 L9175481134.1   L981347863.9    L9946835889.7   P34527753303.132P34527753303.133Q11801279589.132Q11801279589.133Q15457446739.129Q15457446739.130Q15643324129.128Q16679598351.234Q18235909853.132Q18365925601.129Q18694146040.132Q19120365881.132Q21798041355.132Q21879645826.129Q22712450012.132Q22712450012.133Q25157988860.132Q25513505925.131Q25513505925.132Q25662358575.132Q2653971038.233 Q2664898315.234 Q27166391111.233Q27907200258.129Q30693039733.233Q31228709292.132Q31271525473.129Q31394594844.132Q32655500769.129Q33918256002.129Q34362328320.132Q34362328320.133Q35014437530.132Q35717497884.132Q36425882626.129Q36742008045.234Q3830427394.129 Q39939554818.129Q40509833325.130Q40932771343.234Q41152393185.129Q43928033258.130Q44648843873.129Q44990612123.132Q44990612123.133Q46143417837.234Q49303080105.129Q49303289227.130Q49698585326.130Q49698585326.131Q49962066831.130Q51235796833.129Q5280591280.129 Q53230313543.233Q53969758199.132Q54048540290.129Q54057591853.132Q55819530078.233Q55834382859.234Q58784009562.133Q59843137889.129Q6416456232.132 Q64255486968.132Q66522067074.129Q7377275490.131 Q7377275490.132 Q8799150965.233 Q9843367298.128 00001302E03H04;05@06507<07X07[08008E08Z08c09809M09U09X09b09e09n0:I0:O0;20;V0<=0<X0<Y0<Z0=10=60=70=L0=l0>?0>K0>e0?:0?=0?R0?S0?h0@00@W0@n0A10AF0A[0B00BK0BN0Bc0Bi0C>0CA0CH0CI0CU0Cg0D<0DE0DO0DY0D`0EJ0Ec0Ef0Ej0FE0FZ0F`0Fc0Ff0GG0G\0G`0Gd0H90H:0H@0HU0HY0I:0IQ0JP0Ka0LF0M=0MS0Mi0N?0NQ0NR0Nh0O<0Ol0Om0PK0Q00Qg0R;0Rc0S]0S^0T00TB0TT0U20UD0U\0V20VB0VX0W60W70W80WL0WM0Wk0XK0Xi0YG0Yg0Z90ZO0Ze0[;0\90]F0]f0^80^J0^j0_J0_\0`20`D0`V0`j0a<0a=0aO0aa0b_0c50cI0cJ0ch0dX0eW0ei0fGS1R5NEEDF5STKpk3NRT3LBn2ra2sp1A2lo2po3LOS3SLO3SPR2HA2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT3LBn2sp2s01A2lo2po3LOS3SLO3SPR2HA2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5NEEDF5STKpk3NRT3LBn2sp2s61A2lo2po3LOS3SLO3SPR2HA2HB5Ha_st5Hl_stS1R3HIA5STKpk1h3LBn2ra2sp1A2po5SPTOP2HB5Ha_st5Hl_stS1R3HIA5STKpk1h3LBn2sp2s01A2po5SPTOP2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3NRT3LBn2ra2sp1A2lo2po2DS3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT3LBn2sp2s01A2lo2po2DS3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3NRT2sp1A2lo2DS3SLOS1AS1R5STKpk3LBn2sp1A2poS1R5STKpk3LBn2sp1A2poS1R5STKpk3LBn2sp1A2poS2po4LENcS1R5STKpk3LBn2sp1A2poS1R3HIA5PHIpk1h2po2PHS1A1x2HxS1AS2po5SMALLS1AS1A2HA2ABS1R5STKpk3LBn2sp1A2po2HA2ABS1A2HAS1R3HIA5PHIpk1h2po2h13HV12PM2h23HV2S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR3ALO3ACVS1R5STKpk3LBn2sp1A2po2HA2ABSSS1R5STKpk3NRT2sp2lo3SLOS1A1aFS1R5STKpk3LBn2sp1A2poS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R5STKpk2sp2lo3SLOS2sp1A2lo2DSS1R3HIA5PHIpk1h2po2PH4BUD'S1R5STKpk3LBn2sp1A2poS1AS1R5STKpk3LBn2sp1A2poSS1R5STKpk3LBn2sp1A2poS1A1a2HaS1R5STKpk3NRT3LBn2sp1A2lo2po3SLO3SPR2HAS1R3HIA5FFRpk1h1d2po2FFS1AS1R5STKpk3LBn2sp1A2poS1R5STKpk3LBn2sp1A2poS1R5STKpk3LBn2sp1A2poS1R5STKpk3LBn2sp1A2po2HA2ABS1AS1R5STKpk3LBn2sp1A2poS1A2HAS1R5STKpk3LBn2sp1A2poS1AS1R3ACVFS2sp1A2lo2DSS1R3HIA1h2sp5SPTOPS1R5STKpk3LBn2sp1A2poS1A2HA2K0S2po2RP2KRS1R2lo3LOSS2po2B9S1R5STKpk3LBn2sp1A2po3SPR2HA3ACV2RP2RL3RCES1R5STKpk3LBn2sp1A2po3INBS1RS2poS1R5STKpk3LBn2sp1A2po2HA2ABS1R5STKpk3LBn2sp1A2poS1A2ABS1AS1AS2sp2r04SP161q1r1H2H02q02H41A3HALS1R5STKpk3LBn2sp1A2poS2poS2spS1R5STKpk3LBn2sp1A2poSS1d2D0S1R5STKpk3LBn2sp1A2poS2poS1R3HIA5PHIpk1h2po2h13HV12PM4BUD'S1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT3LBn2ra2sp2lo2po3LOS3SLO3ALO2RL3RCE2HB5Ha_st5Hl_stS1R5STKpk3NRT3LBn2sp2s02lo2po3LOS3SLO3ALO2RL3RCE2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3LBn2ra2sp2po2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp2s02po2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3LBn2sp2po2HBS1R5STKpk3LBn2sp2po2HBS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn1A2poFS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn2po3EHIS1R5STKpk3NRT3LBn2sp2s62lo2po3SLO2HB5Ha_st5Hl_stFS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3LBn2ra2sp2po2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp2s02po2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3LBn2po3EHIS1R5STKpk3LBn2ra2sp2lo2po2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp2s02lo2po2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3LBn1A2poS1R5STKpk3LBn2po3ELO3EHIS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn2poS1R5STKpk3LBn2sp2lo2poS1R5STKpk3NRT3LBn2sp2lo2po3SLOFFS1R5STKpk3LBn2po3EHIFS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3LBn2sp1A2po3SPR2HA3HALS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3LBn2sp1A2po3SPR2HA3HALS1R5STKpk3LBn1A2poS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn2sp2po2HBS1R5STKpk3LBn2sp2lo2poS1R5NEEDF5STKpk3NRT3LBn2ra2sp2lo2po3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT3LBn2sp2s02lo2po3LOS3SLO3ALO2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5STKpk3LBn2sp1A2po3SPR2HA3HALS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn2sp2po3SPR2HB5Ha_stS1R5STKpk3LBn2sp2po3SPR2HB5Ha_stS1R5STKpk3LBn1A2poS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5STKpk3LBn2po3EHIS1R5STKpk3LBn1A2poFS1R5STKpk3LBn1A2poS1R5STKpk3LBn1A2poS1R5NEEDF5STKpk3NRT3LBn2sp2s62lo2po3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5STKpk3LBn2sp2lo2poS1R5STKpk3LBn2po3ELOFS1R5STKpk3NRT3LBn2sp2lo2po3SLOS1R5STKpk3NRT3LBn2ra2sp2lo2po3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT3LBn2sp2s02lo2po3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5STKpk3LBn1A2poS1R5STKpk3NRT3LBn2sp2lo2po3SLO". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDA NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 FFRpk0 PHIpk_mono FFRpk_mono PKFREE DIMG HMND NRT CRTFREE CRLFREE po pj HH HK0 LIVE SMALL NDn IFF NDO CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND SUB HA HAL AB D0 LENk"] Lemma entry_live : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m -> aobj asegs AL (hcs asegs R HIA h) m A 1440 ->
      aevtS asegs POST
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x9818c) fc None m (seg_rom asegs)) mo).
    Proof.
      intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI OBJ.
      (* [comment removed for export] *)
      pose proof HH as HHc. lazymatch type of HH with ?t => change t with (hidden t) in HH end.
      pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
      pose proof (hm_top asegs R HIA h _ _ _ HHc) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0.
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (EGOT & ELO & EHI). unfold STKp7f, STKcf in SLO.
      assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STKpk0 NRT SPTOP HTOP; lia]).
      pose proof (hm_wlow asegs R HIA h _ _ _ HHc) as WLc.
      pose proof (presW_init asegs R HIA h (LBn ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 1440)] HHc ltac:(clear; lia)) as HPXc.
      pose proof LIVE as LV. ddestruct LV as (CELLS & _ & _ & _ & RP & RL & RIN & RWC & OWNC & HN0 & HSC & _).
      lazymatch type of LIVE with ?t => change t with (hidden t) in LIVE end.
      rewrite pkcs7_cells_eq in CELLS. unfold p7cells, crt_cells, signer_cells in CELLS. cbn [app] in CELLS.
      destruct (hm_apart asegs R HIA h _ _ _ HHc) as [BR0 _]. rewrite Forall_forall in BR0.
      destruct (BR0 _ ltac:(apply in_app_iff; left; exact RIN)) as (_ & _ & RCE & _). cbn [fst snd] in RCE.
      pose proof (chain_addr_range asegs _ _ _ _ _ _ _ HN0) as INB.
      assert (SNB : 0 <= po_signers_next po < 2 ^ 64).
      { destruct (po_signers po) as [|[a9 ns9] r9] eqn:ES; [cbn in HSC; rewrite HSC; clear; lia|].
        destruct (signer_chain_uncons asegs _ _ _ _ _ _ HSC) as (EE & _ & _ & _ & i9 & n9 & j9 & HR9 & _).
        pose proof (rw_cells_bound _ _ _ _ HR9) as B9. cbn [cells_size csize Nat.add signer_cells] in B9. clear - B9. lia. }
      assert (HINr : In (po_rawp po, po_rawlen po) LBn) by (apply SUB; unfold p7_blocks; left; reflexivity).
      pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      (* [comment removed for export] *)
      zstep. carve_frame 64%nat ST. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [rewrite ?unsigned_lit in K0 by (clear - HA AB; lia); exfalso; clear - K0 HA; lia|]. clear K0.
      zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (hm_abase asegs R HIA h _ LF mc HHc) as AB0; pose proof (abase_got _ _ _ AB0) as GOT; pose proof (abase_gsb _ _ _ AB0) as GSB end.
      rewrite EGOT in GOT.
      zstep. zstep. clear GOT GSB AB0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KR; zify_cond KR; [rewrite ?unsigned_lit in KR by (clear - RP RCE ACV; lia); exfalso; clear - KR RP; lia|]. clear KR.
      zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
      clear MU WM.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -64) _ |- _ => rename FRx into FR end.
      assert (CI0 : pinv [] (RAWC ++ crt_cells (po_crt po) (pj_crt pj) ++ REST (po_issuer0_next po)) LBn m0 mo h).
      { split; [exact HHc|]. split; [exact HK0|]. split; [apply mo_frame_refl|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros x Hx; exact Hx|].
        split; [pose proof (PHIpk0 (Z.of_nat (length (p7_blocks po))) ltac:(clear; lia)) as PH; clear - PH; lia|].
        split; [pose proof (FFRpk0 (Z.of_nat (length (p7_blocks po))) d ltac:(clear; lia) D0) as FF; cbn [length Z.of_nat]; rewrite Z.mul_0_r; clear - FF; lia|].
        split; [intros b Hb; exact Hb|]. split; [intros b Hb _; exact Hb|].
        split; [exact HPXc|]. split; [exact FR|].
        split; [unfold RAWC, REST, crt_cells, signer_cells; cbn [app]; exact CELLS|].
        split; [exact OBJ|]. split; [assumption| assumption]. }
      assert (HVc : havol asegs R HIA h <= havol asegs R HIA h + PHIpk (Z.of_nat (length (p7_blocks po)))) by (pose proof (PHIpk0 (Z.of_nat (length (p7_blocks po))) ltac:(clear; lia)) as PH; clear - PH; lia).
      assert (HFRc : hfr asegs R HIA h <= hfr asegs R HIA h + FFRpk (Z.of_nat (length (p7_blocks po))) d + fr_charge d * Z.of_nat (length (@nil blk)))
        by (pose proof (FFRpk0 (Z.of_nat (length (p7_blocks po))) d ltac:(clear; lia) D0) as FF; cbn [length Z.of_nat]; rewrite Z.mul_0_r; clear - FF; lia).
      lazymatch goal with MIx : mem_inv _ m0 |- _ => rename MIx into MIc end.
      assert (E1 : p7_blocks po = [] ++ [(po_rawp po, po_rawlen po)] ++ (crt_blocks (po_crt po) ++ SNAME (po_names0 po) ++ signer_blocks (po_signers po))) by (unfold p7_blocks, SNAME; reflexivity).
      assert (LEN1 : Z.of_nat (length (@nil blk)) + 1 <= Z.of_nat (length (p7_blocks po))) by (rewrite E1, !app_length; cbn [length]; clear; lia).
      assert (SZ : Z.of_nat (cells_size (RAWC ++ crt_cells (po_crt po) (pj_crt pj) ++ REST (po_issuer0_next po))) = 1440) by reflexivity.
      clear CELLS FR OBJ.
      (* [comment removed for export] *)
      free_node (po_rawp po) (po_rawlen po) E1 LEN1 HINr 0x981ec.
      cbn [app] in CI1.
      lazymatch goal with X : havol _ _ _ ?hq <= havol _ _ _ h + AVOL_CALL |- _ => rename X into HV1; rename hq into h1 end.
      lazymatch goal with X : hfr _ _ _ h1 <= hfr _ _ _ h + _ |- _ => rename X into HFR1 end.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      clear HHc HPXc HVc HFRc MIc SZ LEN1.
      repeat match goal with H : rw_cells _ m0 _ _ |- _ => clear H | H : stk _ m0 _ _ |- _ => clear H | H : aobj _ _ _ m0 _ _ |- _ => clear H
                             | H : presA _ _ _ _ _ _ _ _ m0 _ |- _ => clear H | H : mem_inv _ m0 |- _ => clear H end.
      (* [comment removed for export] *)
      zstep. zstep.
      pose proof CI1 as CI1'. ddestruct CI1' as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & KEEPc & HPXc & FR & CELLS & OBJc & MIc & STc).
      destruct (rw_cells_split3 asegs m1 A _ _ _ CELLS) as (C1 & C2 & C3). clear CELLS.
      change (Z.of_nat (cells_size RAWC)) with 64 in C2, C3.
      change (Z.of_nat (cells_size (crt_cells (po_crt po) (pj_crt pj)))) with 744 in C3. replace (A + 64 + 744) with (A + 808) in C3 by (clear; lia).
      assert (E2 : p7_blocks po = [(po_rawp po, po_rawlen po)] ++ crt_blocks (po_crt po) ++ (SNAME (po_names0 po) ++ signer_blocks (po_signers po))) by (unfold p7_blocks, SNAME; reflexivity).
      assert (CRTIN : forall b, In b (crt_blocks (po_crt po)) -> In b (lb_remove (po_rawp po) LBn)) by (intros b Hb; eapply (pinv_seg_in _ _ _ _ _ _ _ _ CI1 E2); exact Hb).
      assert (ND1 : List.NoDup (map fst (lb_remove (po_rawp po) LBn ++ LB))).
      { assert (HINa : In (po_rawp po) (map fst LBn)) by (replace (po_rawp po) with (fst (po_rawp po, po_rawlen po)) by reflexivity; apply in_map; exact HINr).
        rewrite <- (lb_remove_app_l _ LBn LB HINa). apply nodup_fst_lb_remove. exact NDO. }
      assert (OWN1 : crt_own_ok asegs PK m1 (lb_remove (po_rawp po) LBn ++ LB) (A + 64) (po_crt po) (pj_crt pj)).
      { eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling); [exact OWNC| intros b Hb; apply in_app_iff; left; exact (CRTIN b Hb)| exact (pinv_presx _ _ _ _ _ _ CI1)| exact (blocks_below_hm _ _ _ HHc)| clear - ACV; lia| exact MIc|].
        intros b Hb Hk. apply p7_blocks_disjoint; [| exact Hk]. rewrite E2. apply in_app_iff. right. apply in_app_iff. left. exact Hb. }
      assert (LENc : Z.of_nat (length (crt_blocks (po_crt po))) + 1 <= Z.of_nat (length (p7_blocks po))) by (rewrite E2, !app_length; cbn [length]; clear; lia).
      assert (PM : PHIpk (Z.of_nat (length (crt_blocks (po_crt po)))) <= PHIpk (Z.of_nat (length (p7_blocks po)))) by (apply PHIpk_mono; clear - LENc; lia).
      assert (FM : FFRpk (Z.of_nat (length (crt_blocks (po_crt po)))) d <= FFRpk (Z.of_nat (length (p7_blocks po))) d) by (apply FFRpk_mono; clear - LENc; lia).
      pose proof BUD as BUD'. unfold PHIp7f in BUD'. rewrite LENk in BUD'. pose proof BUDF as BUDF'. unfold FFRp7f in BUDF'; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF' by (unfold fr_charge; clear - D0; lia). rewrite LENk in BUDF'.
      eapply aevtA_call.
      { intros mop [HKp MFp].
        eapply CRTFREE with (h := h1) (LBo := lb_remove (po_rawp po) LBn) (LB := LB) (LF := LF) (A := A + 64) (f := po_crt po) (j := pj_crt pj) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia); rewrite ?HTc, ?HSc;
          first [ exact HHc | exact HKp | exact CRTIN | exact ND1 | exact LOS | exact TP | exact MIc | exact STc | reflexivity
                | lazymatch goal with
                  | |- crt_at _ _ m1 _ (A + 64) _ _ => split; [exact C2|]; split; [clear - HAL; Z.div_mod_to_equations; lia|]; split; [clear - HA; lia|]; split; [unfold CRT_SIZE; clear - AB; lia| exact OWN1]
                  | |- 0 < A + 64 => clear - HA; lia
                  | |- (A + 64) mod 8 = 0 => clear - HAL; Z.div_mod_to_equations; lia
                  | |- co_rawlen _ < _ => clear - SMALL; lia
                  | |- aobj _ _ _ m1 (A + 64) _ => unfold CRT_SIZE; eapply aobj_sub; [eapply aobj_cs_mono; [exact HCSc| exact OBJc]| clear; lia| clear; lia]
                  | |- client_wrange _ _ _ _ (A + 64) _ => unfold CRT_SIZE; intros a Ha; apply CW; clear - Ha; lia
                  | |- A + 64 + _ <= lo \/ _ => unfold CRT_SIZE; clear - DS; lia
                  | |- lo <= _ => unfold STKcf; clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold PHIcf; unfold AVOL_CALL in HV1; clear - HV1 BUD' PM; lia
                  | |- uw_obj R (A + 64) _ d => unfold CRT_SIZE; eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRcf; rewrite ?(Z.max_r 0 (fr_charge d)) by (unfold fr_charge; clear - D0; lia); unfold fr_charge in *; clear - HFR1 BUDF' FM LENc D0; nia
                  end
                | match goal with |- ?g => idtac "CRT-LEFT:" g end ]. }
      cbv beta. (intros msq moq dd_H; ddestruct dd_H as (mop & [HKp MFp] & PO)).
      ddestruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & mo2 & h2 & L2
                      & E0 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & SUB2 & KEEP2 & CZ2).
      injection E0 as Ems Emo. subst msq moq.
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, HP2 by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia). unfold CRT_SIZE in HP2.
      fix_ret 0x981f4.
      assert (CI2 : pinv D2 (cellsZ (po_issuer0_next po)) L2 m2 mo2 h2).
      { unfold D2. eapply (pinv_after _ _ _ _ _ _ _ _ _ _ _ _ [(A + 64, A + 64 + 744)] (pinv_remodel _ _ _ _ _ _ _ CI1 HKp MFp) SUB2 KEEP2 HH2 HK2 MF2 HT2 HS2 HF2 HCS2);
          [ unfold PHIcf in HV2; unfold AVOL_CALL in HV1; clear - HV2 HV1 PM; lia
          | unfold FFRcf in HFR2; rewrite ?(Z.max_r 0 (fr_charge d)) in HFR2 by (unfold fr_charge; clear - D0; lia); rewrite app_length; cbn [length]; rewrite Nat2Z.inj_add; unfold fr_charge in *; clear - HFR2 HFR1 FM D0; nia
          | exact HP2
          | intros x Hx; cbn [outside] in Hx |- *; clear - Hx; lia
          | cbn [disjoint_from]; clear - DS SLO STKpk0 NRT; lia
          | | exact MI2 | exact ST2 ].
        unfold cellsZ. apply rw_cells_join3.
        - eapply presA_rw_cells; [exact HP2| exact C1| change (Z.of_nat (cells_size RAWC)) with 64; intros a Ha; apply (obj_client_range (L2 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia| clear - Ha; lia]| cbn [cells_size csize Nat.add disjoint_from RAWC]; clear; lia].
        - change (Z.of_nat (cells_size RAWC)) with 64. exact CZ2.
        - change (Z.of_nat (cells_size RAWC)) with 64. change (Z.of_nat (cells_size [CB 744 (zeros 744)])) with 744. replace (A + 64 + 744) with (A + 808) by (clear; lia).
          eapply presA_rw_cells; [exact HP2| exact C3| unfold REST; intros a Ha; apply (obj_client_range (L2 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia| revert Ha; cbn [cells_size csize Nat.add signer_cells app]; clear; lia]| unfold REST; cbn [cells_size csize Nat.add disjoint_from signer_cells app]; clear; lia]. }
      clear C1 C2 C3 HHc HKc MFc HTc HSc HFc HCSc HVc HFRc SUBLc KEEPc HPXc FR OBJc MIc STc CI1 OWN1 CRTIN ND1 HP2 HV1 HFR1 HV2 HFR2 SUB2 KEEP2 CZ2 HH2.
      (* [comment removed for export] *)
      pose proof CI2 as CI2'. ddestruct CI2' as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & KEEPc & HPXc & FR & CELLS & OBJc & MIc & STc).
      pose proof (hcs_ok asegs R HIA h2) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      change (rw_cells asegs m2 A ((RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]) ++ [CB 416 (zeros 416)]
                                   ++ ([CB 8 (pj3 pj)] ++ signer_cells (po_issuer0_next po) (po_signers_next po) (pj_s0 pj)))) in CELLS.
      destruct (rw_cells_split3 asegs m2 A _ _ _ CELLS) as (C1 & C2 & C3). clear CELLS.
      change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816 in C2, C3.
      change (Z.of_nat (cells_size [CB 416 (zeros 416)])) with 416 in C3. replace (A + 816 + 416) with (A + 1232) in C3 by (clear; lia).
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo2) _ _ _ (conj HK2 (mo_frame_refl mo2))).
      repeat match goal with Lw : ainv_laws _ _ |- _ => clear Lw | Kv : kinv_laws _ _ _ |- _ => clear Kv end.
      pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo2) as KINV.
      zstep. zstep.
      pose proof CRLFREE as SCRL. unfold x509_crl_free_stmtA, A_X509_CRL_FREE in SCRL. specialize SCRL with (h := h2). rewrite HTc in SCRL.
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo2).
      { eapply SCRL with (LB := L2 ++ LB) (LF := LF) (A := A + 816) (lo := lo);
          rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia);
          first [ exact HHc | exact C2 | exact LOS | exact TP | exact MIc | exact STc | reflexivity
                | lazymatch goal with
                  | |- 0 < A + 816 => clear - HA; lia
                  | |- (A + 816) mod 8 = 0 => clear - HAL; Z.div_mod_to_equations; lia
                  | |- aobj _ _ _ m2 (A + 816) _ => eapply aobj_sub; [exact OBJcc| clear; lia| clear; lia]
                  | |- client_wrange _ _ _ _ (A + 816) _ => eapply client_wrange_inside; [exact CW| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]| clear; lia| clear; lia]
                  | |- A + 816 + _ <= lo \/ _ => clear - DS; lia
                  | |- lo <= _ => unfold X509_CRL_FREE_STACK_A; clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  end
                | match goal with |- ?g => idtac "CRL-LEFT:" g end ]. }
      clear SCRL. cbv beta. intros ms' PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & h3 & -> & MI3 & ST3 & HP3 & HH3 & Ecs3 & ET3 & ES3 & EF3 & EV3 & EFR3 & HKI3 & CZ3).
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST3, HP3 by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia).
      fix_ret 0x981fc.
      assert (CI3 : pinv D2 (cellsZ (po_issuer0_next po)) L2 m3 mo2 h3).
      { pose proof (pinv_after _ [] _ (cellsZ (po_issuer0_next po)) _ L2 _ _ _ m3 mo2 h3 [(A + 816, A + 816 + 416)] CI2
                      (fun b Hb => Hb) (fun b Hb _ => Hb) HH3 ltac:(apply (proj2 (HKI3 mo2)); exact HKc) (mo_frame_refl mo2)) as PA.
        rewrite app_nil_r in PA. apply PA; clear PA.
        - exact ET3.
        - exact ES3.
        - exact EF3.
        - intros x Hx. rewrite Ecs3. exact Hx.
        - rewrite EV3. exact HVc.
        - rewrite EFR3. exact HFRc.
        - exact HP3.
        - intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia.
        - cbn [disjoint_from]. clear - DS SLO STKpk0 NRT. lia.
        - unfold cellsZ.
          change (rw_cells asegs m3 A ((RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]) ++ [CB 416 (zeros 416)]
                                       ++ ([CB 8 (pj3 pj)] ++ signer_cells (po_issuer0_next po) (po_signers_next po) (pj_s0 pj)))).
          apply rw_cells_join3.
          + eapply presA_rw_cells; [exact HP3| exact C1| change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816; intros a Ha; apply (obj_client_range (L2 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia| clear - Ha; lia]| cbn [cells_size csize Nat.add disjoint_from RAWC app]; clear; lia].
          + change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816. exact CZ3.
          + change (Z.of_nat (cells_size (RAWC ++ [CB 744 (zeros 744)] ++ [CB 8 (pj2 pj)]))) with 816. change (Z.of_nat (cells_size [CB 416 (zeros 416)])) with 416. replace (A + 816 + 416) with (A + 1232) by (clear; lia).
            eapply presA_rw_cells; [exact HP3| exact C3| intros a Ha; apply (obj_client_range (L2 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia| revert Ha; cbn [cells_size csize Nat.add signer_cells app]; clear; lia]| cbn [cells_size csize Nat.add disjoint_from signer_cells app]; clear; lia].
        - exact MI3.
        - exact ST3. }
      clear C1 C2 C3 HHc HPXc FR OBJc OBJcc MIc STc CI2 HP3 CZ3 HH3.
      (* [comment removed for export] *)
      pose proof CI3 as CI3'. ddestruct CI3' as (HHc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPXc & FR & CELLS & OBJc & MIc & STc).
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      unfold cellsZ, RAWC, signer_cells in CELLS. cbn [app] in CELLS.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      assert (ED3 : D3 = D2 ++ SNAME (po_names0 po)) by (unfold D3, D2; rewrite <- app_assoc; reflexivity).
      (* [comment removed for export] *)
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        rewrite ?unsigned_lit in KI by (clear - INB; lia).
        pose proof (chain_null_inv asegs _ _ _ _ _ _ ltac:(rewrite <- KI; exact HN0)) as EN.
        leave. eapply from_97c28. rewrite ED3. apply pinv_skip. eapply pinv_remodel; [exact CI3| apply (proj2 (HKI3 _)); eassumption| eassumption].
      - rewrite ?unsigned_lit in KI by (clear - INB; lia).
        destruct (chain_nonnull asegs _ _ _ _ _ _ _ HN0 KI) as (n1 & rest & EN).
        leave. eapply (loopA _ _ _ (signer_blocks (po_signers po) ++ []) (cellsZ (po_issuer0_next po)) (po_names0 po) (po_issuer0_next po) D2);
          [rewrite EN; congruence| exact HN0| unfold D2, p7_blocks, SNAME; repeat rewrite <- app_assoc; rewrite app_nil_r; reflexivity
          | eapply pinv_remodel; [exact CI3| apply (proj2 (HKI3 _)); eassumption| eassumption]| reflexivity|].
        intros Lc' mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 CI'.
        eapply from_97c28. rewrite ED3. exact CI'.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Live.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01R0@D13554616751.107D13554616751.108D30841324822.108D35881667587.107D35881667587.108K54978542206.107K54978542206.108L12283411672.104L13301871092.104L14106684376.103L14106684376.104L14844034785.1  L17646078182.103L21832304075.6  L26892418956.1  L28814043710.104L29280787994.85 L31056940152.103L34994544387.104L35653441506.11 L36425882626.104L39887139444.104L40281191306.3  L40834179097.107L41288976216.104L43055530543.101L44866992728.104L45898055924.104L48429268312.104L49345641752.103L5145216728.104 L51925114228.104L54968017161.2  L57933933556.104L59308628179.3  L60098763854.3  L62018535662.1  L63962036340.103L67158371251.104L7274816372.104 L861591149.2    L8722184664.104 Q11801279589.107Q11801279589.108Q15457446739.104Q15457446739.105Q15643324129.103Q15643324129.104Q18235909853.107Q18365925601.104Q18694146040.107Q19120365881.107Q21798041355.107Q21879645826.104Q22712450012.107Q22712450012.108Q25157988860.107Q25513505925.106Q25513505925.107Q25662358575.107Q27907200258.104Q31228709292.107Q31271525473.104Q31394594844.107Q32655500769.104Q33918256002.104Q34362328320.107Q34362328320.108Q35014437530.107Q35717497884.107Q36425882626.104Q3830427394.104 Q39939554818.104Q40509833325.105Q41152393185.104Q43928033258.105Q44648843873.104Q44990612123.107Q44990612123.108Q49303080105.104Q49303289227.105Q49698585326.105Q49698585326.106Q49962066831.105Q51235796833.104Q5280591280.104 Q53969758199.107Q54048540290.104Q54057591853.107Q58784009562.108Q59843137889.104Q6416456232.107 Q64255486968.107Q66522067074.104Q7377275490.106 Q7377275490.107 Q9843367298.103 Q9843367298.104 00000l02703303_04]05K06K06Y06g07507C07H07V07l08008D08N08b09009P0:00:>0:G0:U0:c0;C0;Q0;_0;m0<;0<I0<W0<X0<f0<o0=90=<0=J0=X0=f0=l0>:0>X0?H0?W0?f0@50@D0@E0@T0@a0AJ0AK0Ab0B@0C00C=0C^0DQ0DR0Di0E:0EI0ER0Ea0F80F90F:0FG0FH0F_0G60GM0Gf0H50HD0HS0IJ0JP0J[0Jf0K?0KX0Kc0L20L=0LJ0LU0LV0MM0M\0Mi0Mj0NA0Nj0Ob0P90PPS1R5NEEDF5STKpk3NRT2ra2sp1A2lo2HA3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT2sp2s01A2lo2HA3LOS3SLO3SPR2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5NEEDF5STKpk3NRT2sp2s61A2lo2HA3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R3HIA5STKpk1h2ra2sp1A5SPTOP2HB5Ha_st5Hl_stS1R3HIA5STKpk1h2sp2s01A5SPTOP2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3NRT2ra2sp1A2lo2DS3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT2sp2s01A2lo2DS3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS3LBnS1R5STKpk2sp1AS1R3HIA5PHIpk1h3LBn2PHS2spS1R5STKpk2sp1A2HA2ABS2sp1A1d1HS1R5STKpk2sp1A2HA2ABS1R5STKpk2sp1AS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R5STKpk3NRT2sp1A2lo2HA3SLO3SPRS1R5STKpk2sp1AS1R3HIA1hS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk3NRT2sp1A2lo2HA3SLO3SPRS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AFS1R5STKpk2sp1AS1A2HA2K0S1R2lo3LOSS1RS1R5STKpk2sp1AS1R5STKpk2sp1AS1R5STKpk2sp1AS1d2D0S1R5STKpk2sp1AS1R5STKpk2ra2sp2HB5Ha_st5Hl_stS1R5STKpk2sp2s02HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk2sp2HBS1R5STKpk2sp2HBS1R5STKpk2sp2loS1R5STKpk2sp2loFS1R5STKpk2sp2loS1R5STKpk3EHIS1R5STKpk3NRT2sp2s62lo3SLO2HB5Ha_st5Hl_stFS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk2ra2sp2HB5Ha_st5Hl_stS1R5STKpk2sp2s02HB5Ha_st5Hl_st2s12s22s32s42s52s6S1R5STKpk3EHIS1R5STKpk2ra2sp2lo2HB5Ha_st5Hl_stS1R5STKpk2sp2s02lo2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3ELO3EHIS1R5STKpk2sp2loS1R5STKpkS1R5STKpk2sp2loS1R5STKpk3NRT2sp2lo3SLOFFS1R5STKpk3EHIFS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk2sp2loS1R5STKpk2sp2HBS1R5STKpk2sp2loS1R5NEEDF5STKpk3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp3SPR2HB5Ha_stS1R5STKpk2sp3SPR2HB5Ha_stS1R5STKpk1AS1R5STKpk2sp2loS1R5STKpk1AS1R5STKpk3EHIS1R5STKpk1AFS1R5NEEDF5STKpk3NRT2sp2s62lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5STKpk2sp2loS1R5STKpk3ELOFS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s5S1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDF NEEDM PHIpk0 FFRpk0 NRT"] Lemma entry_zero : forall (h : HST asegs R HIA) (LBn LB LF : list blk)
      (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (A lo d : Z),
    HM asegs R HIA h (LBn ++ LB) LF m -> HK asegs R HIA h mo ->
    pkcs7_zero asegs m A -> A mod 8 = 0 -> 0 < A -> A + 1440 <= 2 ^ 64 ->
    aobj asegs AL (hcs asegs R HIA h) m A 1440 ->
    client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A 1440 ->
    (A + 1440 <= lo \/ bv_unsigned sp <= A) ->
    stk asegs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - STKp7f R STKpk ->
    bv_unsigned sp <= htop asegs R HIA h -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> tp = Z_to_bv 64 (arl_tp R) -> 0 <= bv_unsigned sp < 2 ^ 64 -> uw_obj R A 1440 d ->
    aevtS asegs (pkcs7_free_postA24 asegs R HIA (PHIp7f PHIpk) (FFRp7f FFRpk) h LB LBn LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A lo d m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9818c) fc None m (seg_rom asegs)) mo).
  Proof.
    intros h LBn LB LF ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo A lo d
           HHc HK0 PZ0 HAL HA AB OBJ CW DS ST LOS SLO SPTOP SP16 MI TP SPR UWO.
    assert (D0 : 0 <= d) by (destruct UWO as [[_ H]|H]; lia).
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_top asegs R HIA h _ _ _ HHc) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (EGOT & ELO & EHI). unfold STKp7f, STKcf in SLO.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STKpk0 NRT SPTOP HTOP; lia]).
    pose proof (hm_wlow asegs R HIA h _ _ _ HHc) as WLc.
    pose proof (presW_init asegs R HIA h (LBn ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 1440)] HHc ltac:(clear; lia)) as HPXc.
    unfold pkcs7_zero in PZ0. rename PZ0 into CELLS.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    (* [comment removed for export] *)
    zstep. carve_frame 64%nat ST. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [rewrite ?unsigned_lit in K0 by (clear - HA AB; lia); exfalso; clear - K0 HA; lia|]. clear K0.
    zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (hm_abase asegs R HIA h _ LF mc HHc) as AB0; pose proof (abase_got _ _ _ AB0) as GOT; pose proof (abase_gsb _ _ _ AB0) as GSB end.
    rewrite EGOT in GOT.
    zstep. zstep. clear GOT GSB AB0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    lazymatch goal with FRH : rw_cells _ m0 (bv_unsigned sp + -64) _, STH : stk _ m0 lo _ |- _ => release_frame FRH STH (bv_unsigned sp) end.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold pkcs7_free_postA24, P_pkcs7_top.PKCS7_SIZE.
    deexists 15. dexists m0, mo9, h, LBn.
    split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact MF9|].
    split; [eapply presA_weaken; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPXc)| intros b Hb; apply in_app_iff; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [intros x Hx; exact Hx|].
    split; [unfold PHIp7f; pose proof (PHIpk0 (Z.of_nat (length LBn)) ltac:(clear; lia)) as PH; clear - PH; lia|].
    split; [unfold FFRp7f; rewrite ?(Z.max_r 0 (fr_charge d)) by (unfold fr_charge; clear - D0; lia); pose proof (FFRpk0 (Z.of_nat (length LBn)) d ltac:(clear; lia) D0) as FF; unfold fr_charge; clear - FF D0; nia|].
    split; [unfold pkcs7_zero; exact CELLS|]. split; [apply le_n|]. split; [exact HHc| apply Z.le_refl].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG HFREE NEEDF NEEDA NEEDM PZ SHALLOW SEQFREE ZFREE PHIpk0 FFRpk0 PHIpk_mono FFRpk_mono PKFREE DIMG HMND NRT CRTFREE CRLFREE"] Theorem A_pkcs7_free_walk24 :
    pkcs7_free_stmtA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) (PHIp7f PHIpk) (FFRp7f FFRpk) (STKp7f R STKpk) A_PKCS7_FREE.
  Proof.
    unfold pkcs7_free_stmtA24, A_PKCS7_FREE. intros h LB LBn LF. intros until st. intros HH HK REP HAL HA OBJ CW DS ST LOS SLO SPTOP SP16 SP47 MI TP BUD UWO BUDF ->.
    unfold P_pkcs7_top.PKCS7_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    destruct REP as (REP & SMALL).
    destruct st as [[po pj]|].
    - ddestruct REP as (LIVE & NDn & IFF). cbn [p7small] in SMALL.
      eapply entry_live; eassumption.
    - ddestruct REP as (PZ0 & _ & _ & AB). unfold RepCrt.PKCS7_SIZE in AB.
      eapply entry_zero; eassumption.
  Qed.
End Walk.
