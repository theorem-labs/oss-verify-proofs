(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa RepCrt RepPk CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_rsa_free P_ecp_group_free P_ecp_keypair_free P_pk_wrap_rsa P_pk_wrap_eckey P_pk_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_platform_zeroize
     A_free_seq A_rsa_free A_ecp_group_free A_ecp_keypair_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
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
Definition A_RSA_FREE_WRAP : Z := 0x0b1f74.     (* [comment removed for export] *)
Definition A_ECKEY_FREE_WRAP : Z := 0x0b22f0.   (* [comment removed for export] *)
Definition A_WRAP_FREE_PK : Z := 0x6947c.        (* [comment removed for export] *)  (* [comment removed for export] *)
Notation RSA_FREE_WRAP_STACK_A := 96 (only parsing).      (* [comment removed for export] *)
Notation ECKEY_FREE_WRAP_STACK_A := 176 (only parsing).   (* [comment removed for export] *)
Definition RSA_FREE_WRAP_PHI : Z := RSA_FREE_PHI + AVOL_CALL.
Definition RSA_FREE_WRAP_FR (d : Z) : Z := RSA_FREE_FR + fr_charge d.
Definition ECKEY_FREE_WRAP_PHI : Z := KF_PHI + AVOL_CALL.
Definition ECKEY_FREE_WRAP_FR (d : Z) : Z := KF_FR 0 + fr_charge d.

Definition wrap_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LBf LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PHI FR lo : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' mo' h',
    c = mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom segs)) mo'
    /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
    /\ presA segs R LBf LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [] m m'
    /\ htop segs R HIA h' = htop segs R HIA h /\ hstkhi segs R HIA h' = hstkhi segs R HIA h
    /\ hflag segs R HIA h' = hflag segs R HIA h /\ HK segs R HIA h' mo'
    /\ (forall x, hcs segs R HIA h x -> hcs segs R HIA h' x)
    /\ havol segs R HIA h' <= havol segs R HIA h + PHI
    /\ hfr segs R HIA h' <= hfr segs R HIA h + FR
    /\ HM segs R HIA h' LBf LF m'.

Definition rsa_free_wrap_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
         (C : Z) (r : rsa_st) (lo d : Z),
    HM segs R HIA h LB LF m -> HK segs R HIA h mo ->
    rsa_at segs m LB C r ->
    stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - RSA_FREE_WRAP_STACK_A - arl_need_rt R ->
    bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) -> mem_inv segs m ->
    havol segs R HIA h + RSA_FREE_WRAP_PHI <= AVOL_MAX -> uw_obj R (bv_unsigned s0) 1 d -> hfr segs R HIA h + RSA_FREE_WRAP_FR d <= FR_MAX ->
    a0 = Z_to_bv 64 C ->
    aevtS segs (wrap_free_postA segs R HIA h (lb_remove C (rsa_free_LB r LB)) LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                  RSA_FREE_WRAP_PHI (RSA_FREE_WRAP_FR d) lo m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

Definition eckey_free_wrap_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
         (A : Z) (k : ecp_kp) (lo d : Z),
    HM segs R HIA h LB LF m -> HK segs R HIA h mo ->
    ecp_keypair_at segs MT m LB A k -> In (A, 256) LB -> mpds_apart (kp_mpds k) ->
    (forall dd, In dd (kp_mpds k) -> md_own dd = LHeap -> md_p dd <> A) -> A mod 16 = 0 -> A + 256 <= 2^64 ->
    stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - ECKEY_FREE_WRAP_STACK_A - arl_need_rt R ->
    bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) -> mem_inv segs m ->
    havol segs R HIA h + ECKEY_FREE_WRAP_PHI <= AVOL_MAX -> uw_obj R (bv_unsigned s0) 1 d -> hfr segs R HIA h + ECKEY_FREE_WRAP_FR d <= FR_MAX ->
    a0 = Z_to_bv 64 A ->
    aevtS segs (wrap_free_postA segs R HIA h (lb_remove A (kp_free_LB k LB)) LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                  ECKEY_FREE_WRAP_PHI (ECKEY_FREE_WRAP_FR d) lo m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

Section Wraps.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable MT : list modp_ent.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HFREE : arl_free R = A_WRAP_FREE_PK.
  Hypothesis RSAFREE : rsa_free_stmtA asegs R HIA A_RSA_FREE.
  Hypothesis KPFREE : ecp_keypair_free_stmtA asegs R HIA MT A_ECP_KEYPAIR_FREE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis NEEDF : 0 <= arl_need_free R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2613541441.11000009S1R5NEEDF". (* [comment removed for export] *)
  Let NRT : arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L2402939234.3 L26892418956.1L31466854983.8L44035707464.8L58413175681.7L58870443372.1L62018535662.1L6724843687.9 00000:00>00X01201I01M01P01mS1R3HIA2h0S2spS1R3HIA2h01h1d2FR3HFR4BUDFS1R3HIA2h01h3PHI2HV2h23HV2S1R3HIA2h01h3PHI2HV3BUDS2s0S1RS1R3HIA2h01h1d2FR3HFR2h24HFR2". (* [comment removed for export] *)
  #[using="HFREE"] Lemma free_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (mo0 : Model) (h0 h : HST asegs R HIA) (LBc LF : list blk) (C n lo d PHI FR : Z),
    HM asegs R HIA h LBc LF m -> In (C, n) LBc ->
    htop asegs R HIA h = htop asegs R HIA h0 -> hstkhi asegs R HIA h = hstkhi asegs R HIA h0 -> hflag asegs R HIA h = hflag asegs R HIA h0 ->
    (forall x, hcs asegs R HIA h0 x -> hcs asegs R HIA h x) ->
    havol asegs R HIA h + AVOL_CALL <= havol asegs R HIA h0 + PHI -> hfr asegs R HIA h + fr_charge d <= hfr asegs R HIA h0 + FR ->
    havol asegs R HIA h0 + PHI <= AVOL_MAX -> hfr asegs R HIA h0 + FR <= FR_MAX ->
    presW asegs R HIA h0 (lb_remove C LBc) LF (bv_unsigned sp) (arl_stklo R) [] m0 m ->
    stk asegs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - arl_need_free R ->
    bv_unsigned sp <= htop asegs R HIA h0 -> bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 (arl_tp R) -> mem_inv asegs m ->
    uw_obj R (bv_unsigned s0) 1 d ->
    aevtA asegs (KF asegs R HIA h mo0) (wrap_free_postA asegs R HIA h0 (lb_remove C LBc) LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PHI FR lo m0 mo0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_WRAP_FREE_PK) fc None m (seg_rom asegs)).
  Proof.
    intros until FR. intros HH CIN HTc HSc HFc HCSc HV HFR BUD BUDF PXA ST LOS SLO SPTOP SPA TP MI UWS.
    replace (Z_to_bv 64 A_WRAP_FREE_PK) with (Z_to_bv 64 (arl_free R) : word) by (rewrite HFREE; reflexivity).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_free asegs R HIA) with (h := h) (LB := LBc) (LF := LF) (A := C) (n := n) (lo := lo) (d := d);
        first [ exact HH | exact HK1 | exact CIN | exact ST | exact LOS | exact SLO | exact SPA | exact TP | exact MI | reflexivity
              | lazymatch goal with
                | |- _ <= htop _ _ _ _ => rewrite HTc; exact SPTOP
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HV BUD; lia
                | |- uwc _ _ _ _ _ _ _ => eapply uw_obj_uwc; [exact UWS| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFR BUDF; lia
                end
              | match goal with |- ?gg => idtac "FREE-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & (ms2 & mo2 & E & PO))). injection E as <- <-.
    unfold call_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & E2 & MI2 & ST2 & MF2 & PX2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2).
    subst ms'.
    apply aevtS_now. unfold wrap_free_postA. deexists 15. dexists m2, mox, h2.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|].
    split. { eapply (presW_presA asegs R HIA h0).
             eapply presW_call; [exact PXA| exact PX2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HSc; clear; lia| intros x Hx; exact Hx]. }
    split; [rewrite HT2; exact HTc|]. split; [rewrite HS2; exact HSc|]. split; [rewrite HF2; exact HFc|]. split; [exact HK2|].
    split; [intros x Hx; apply HCS2, HCSc, Hx|]. split; [clear - HV HV2; lia|]. split; [clear - HFR HFR2; lia|]. exact HH2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac wr_facts h HH :=
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := L)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOP;
    destruct (hm_apart asegs R HIA h _ _ _ HH) as [HBR HAP].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0@D13156179990.105D31501237935.104D35881667587.104D35881667587.105L11774327555.101L11978020448.7  L14956293327.6  L18022427737.4  L1814381067.6   L20433961190.100L2397629480.6   L31401241662.128L32049487064.100L32049487064.129L3210077857.0   L34061135516.1  L3523383060.9   L35653441506.7  L36898637104.5  L3834309877.129 L40281191306.3  L41598571912.8  L43015428978.6  L43057222721.98 L43819654436.4  L46748113268.100L49339055580.7  L49530003784.1  L55980858593.128L56552377779.101L56552377779.129L60098763854.3  L62018535662.1  L62705181399.5  L66151427842.16 L6744284215.5   Q13296972522.102Q14525642139.104Q15643324129.100Q15647862038.129Q20685106778.105Q22712450012.104Q22712450012.105Q25513505925.103Q25513505925.104Q36801578553.104Q3830427394.101 Q3834309877.129 Q45914037331.101Q49698585326.102Q49698585326.103Q51223032982.129Q51235796833.101Q58146298210.103Q59321350679.104Q59321350679.105Q67528989526.104Q67528989526.105Q9838829173.129 Q9843367298.100 00000`01P02602\02b03:03K03W03j04004D04J04P04V04W04[05>05X05e06?06H06_07207L07Y07_08:08>08D08J08P08Z08]08o09I09Y09`0:K0:R0:Y0;D0;Z0<00<I0<b0=E0=V0=g0=n0>?0>P0>W0>^0?A0?B0?C0?f0@I0@Z0@kS1R3NRT2sp2s01C2lo3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3NRT2ra2sp1C2lo3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1C5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01C5SPTOP2HB5Ha_st5Hl_stS2sp1CS1R5NEEDR2sp1C2lo3SLO2SXS1R3NRT2sp2lo3SLOS2sp1C2lo2SXS1R3HIA1h1d2h24HFR2S2sp1CS1R1C2lo3LOS3ALO3C4_S2sp1CS2sp1CS2sp1CSS2spS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACP3SPRS1R3HIA1h2sp2lo5SPTOP4HTOPS1R2sp2lo3SLOS1R3NRT2sp1C2lo3SLO3SPR2C0S1R3HIA1hS1R2sp2lo3LOS3ALO2dd2I4S1R3HIA1h1d4BUDF2D0S1R3NRT2sp1C2lo3SLO3SPR2C0S1R3HIA1h3BUDS2sp1CS1R5NEEDR2sp2lo3LOS3SLO3ALOS2spS2sp1CS2sp1CS2sp1CS1R2lo3LOSS1RS1R3HIA1h2sp5SPTOPS2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h2h23HV2S2sp2HBS1R3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2sp2loS2sp2loS1R3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS2sp2HBS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp2loS2sp2loS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stFFS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLO". (* [comment removed for export] *)
  #[using="HFREE RSAFREE NEEDR NEEDF DIMG HMND NRT"] Lemma A_rsa_free_wrap_walk : rsa_free_wrap_stmtA asegs R HIA A_RSA_FREE_WRAP.
  Proof.
    unfold rsa_free_wrap_stmtA, A_RSA_FREE_WRAP. intros until d.
    intros HH HK0 RA ST LOS SLO SPTOP SPA TP MI BUD UWS BUDF ->.
    wr_facts h HH. change (blkfacts L (LB ++ LF)) in HBR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWS) as D0.
    pose proof RA as RAc. ddestruct RAc as (_ & _ & _ & _ & _ & _ & _ & ALL & CAL & C0 & CB & CIN & PN & PE & PNE). unfold RSA_CTX_SIZE in CB, CIN.
    destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact CIN)) as (_ & _ & C4_ & C5_).
    assert (SX : C + 232 <= lo) by (clear - C4_ ALO LOS; lia).
    set (LBr := lb_remove C (rsa_free_LB r LB)).
    assert (SUBr : forall b, In b LBr -> In b LB) by (intros b Hb; subst LBr; apply In_lb_remove in Hb; apply rsa_free_LB_sub in Hb; exact Hb).
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB LBr LF (bv_unsigned sp) (arl_stklo R) [] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) SUBr) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. pose proof (conj RA ALL) as RAbox. clear RA ALL.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _]. destruct RAbox as [RA ALL].
    assert (RA1 : rsa_at asegs m1 LB C r).
    { eapply rsa_at_munch; [exact RA| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - SX; lia|].
      intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m LB (LB ++ LF) dd) as (_ & _ & I3 & I4 & _);
        [apply (proj1 (Forall_forall _ _) ALL); exact Hd| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia]. }
    clear MU0 WM0 MIm RA ALL.
    (* [comment removed for export] *)
    zstep.
    pose proof RSAFREE as SG. unfold rsa_free_stmtA, A_RSA_FREE in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (C := C) (r := r) (lo := lo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by (clear - SPR SLO NEEDR LOS ALO ACP; lia);
        first [ exact HK1 | exact RA1 | exact LOS | exact TP | reflexivity
              | lazymatch goal with
                | |- HM _ _ _ h LB LF _ => assumption
                | |- stk _ _ lo _ => assumption
                | |- lo <= _ => clear - SLO NEEDR; lia
                | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- mem_inv _ _ => assumption
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold RSA_FREE_WRAP_PHI in BUD; unfold RSA_FREE_PHI, AVOL_CALL in *; clear - BUD; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold RSA_FREE_WRAP_FR in BUDF; unfold RSA_FREE_FR, fr_charge in *; clear - BUDF D0; lia
                end
              | match goal with |- ?gg => idtac "RSA-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PX2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CIN2).
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST2, PX2 by (clear - SPR SLO NEEDR LOS ALO ACP; lia).
    unfold RSA_CTX_SIZE in PX2, CIN2.
    replace (ret_pc (Z_to_bv 64 0xb1f88)) with (Z_to_bv 64 0xb1f88 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ =>
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ PX2 FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - SX SLO NEEDR; lia)) as FR2; clear FRx end.
    assert (PX2' : presA asegs R LBr LF (bv_unsigned sp + -16) (arl_stklo R) (hstkhi asegs R HIA h) [] m1 m2).
    { rewrite <- HS2. eapply (presA_drop_freed asegs R HIA h2 (rsa_free_LB r LB) LF LBr [] C 232 m2 m1 m2); [exact HH2| exact CIN2| | exact DI1| exact DI2| clear - SLO NEEDR LOS ALO; lia|].
      - intros b x Hb Hx. subst LBr. split; [eapply In_lb_remove; exact Hb|]. intros E. apply (lb_remove_fst_neq _ _ _ (HMND _ _ _ _ HH2) Hb). rewrite E. reflexivity.
      - rewrite HS2. eapply presA_weaken; [exact PX2| subst LBr; intros b Hb; eapply In_lb_remove; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PXA2 : presW asegs R HIA h LBr LF (bv_unsigned sp) (arl_stklo R) [] m m2).
    { eapply presW_call; [exact PXA| exact PX2'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    clear PXA PX2 PX2' SG RA1.
    repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                         | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc. pose proof (crange_mono _ _ _ _ HCS2 SCS) as SCSc.
    zstep. zstep. zstep. zstep. release_frame FR2 ST2 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    subst LBr. unfold A_WRAP_FREE_PK.
    eapply free_tail with (h0 := h) (n := 232) (d := d); first [exact HH2 | exact CIN2 | exact PXA2 | exact UWS | eassumption | reflexivity
      | lazymatch goal with
        | |- havol _ _ _ _ + _ <= _ => unfold RSA_FREE_WRAP_PHI; clear - HV2; lia
        | |- hfr _ _ _ _ + _ <= _ => unfold RSA_FREE_WRAP_FR; clear - HFR2; lia
        | |- lo <= _ => clear - SLO NEEDR NRT; lia
        end
      | match goal with |- ?gg => idtac "TAIL-LEFT:" gg end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0100@D13156179990.108D31501237935.107D35881667587.107D35881667587.108L11774327555.104L12288711042.7  L13510597680.5  L14956293327.6  L17387139489.0  L1771265424.7   L20433961190.103L24026884470.4  L24028945090.6  L25026442954.6  L31401241662.130L32049487064.103L32049487064.131L34061135516.1  L3523383060.9   L35653441506.7  L36835244415.4  L37714553091.1  L3834309877.131 L39280637297.0  L40281191306.3  L41598571912.8  L43055537601.101L46748113268.103L49339055580.7  L49530003784.1  L55980858593.130L56552377779.104L56552377779.131L60098763854.3  L62018535662.1  L62705181399.5  L6353690033.3   L65439589905.1  L66151427842.16 L6744284215.5   Q13296972522.105Q14525642139.107Q15643324129.103Q15647862038.131Q20685106778.108Q22712450012.107Q22712450012.108Q25513505925.106Q25513505925.107Q36801578553.107Q3830427394.104 Q3834309877.131 Q45914037331.104Q49698585326.105Q49698585326.106Q51223032982.131Q51235796833.104Q58146298210.106Q59321350679.107Q59321350679.108Q67528989526.107Q67528989526.108Q9838829173.131 Q9843367298.103 00000`01P02602\02b03:03G03X03Y03l04204?04R04f04l05205805<05_06906E06H06b06c06l07C07]07c08>08B08H08N08T08^08a09309;09>09X09h09o0:Z0:a0:h0;S0;i0<?0<X0=10=T0=e0>60>=0>N0>_0>f0>m0?P0?Q0?R0@50@X0@i0A:S1R3NRT2sp2s01A2lo3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3NRT2ra2sp1A2lo3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1A5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01A5SPTOP2HB5Ha_st5Hl_stS2sp1AS1R5NEEDR2sp1A2lo3SLO2SXS1R2sp2lo3SLOS1R3NRT2sp2lo3SLOSS1R3HIA1h1d2h24HFR2S2sp1AS1R3HIA1h3BUDS1R3HIA1h1d4BUDF2D0S1R1A2lo3LOS3ALO3C4_S2sp1AS2sp1AS2sp1AS2spS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACP3SPRS1R3HIA1h2sp2lo5SPTOP4HTOPS2sp1A2lo2SXS1AS1R3NRT2sp1A2lo3SLO3SPR2C0SS1R3HIA1hS1R2sp2lo3LOS3ALO2dd2I4S1R3NRT2sp1A2lo3SLO3SPR2C0S2sp1AS1R5NEEDR2sp2lo3LOS3SLO3ALOS2spS2sp1AS2sp1AS2sp1AS1R2lo3LOSS1RS1R3HIA1h2sp5SPTOPS1A1a2HaS1AS2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h2h23HV2S2sp2HBS1R3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2sp2loS2sp2loS1R3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS2sp2HBS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp2loS2sp2loS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stFFS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLO". (* [comment removed for export] *)
  #[using="HFREE KPFREE NEEDR NEEDF DIMG HMND NRT"] Lemma A_eckey_free_wrap_walk : eckey_free_wrap_stmtA asegs R HIA MT A_ECKEY_FREE_WRAP.
  Proof.
    unfold eckey_free_wrap_stmtA, A_ECKEY_FREE_WRAP. intros until d.
    intros HH HK0 K CIN DIS PNE AL16 AB ST LOS SLO SPTOP SPA TP MI BUD UWS BUDF ->.
    wr_facts h HH. change (blkfacts L (LB ++ LF)) in HBR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWS) as D0.
    destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact CIN)) as (C0 & _ & C4_ & C5_).
    assert (SX : A + 256 <= lo) by (clear - C4_ ALO LOS; lia).
    assert (CINF : In (A, 256) (kp_free_LB k LB)).
    { unfold kp_free_LB, grp_free_LB. apply lb_free_mpds_keep; [apply lb_free_mpds_keep; [exact CIN|]|];
        intros dd Hd O E; refine (PNE dd _ O (eq_sym E)); first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]. }
    set (LBr := lb_remove A (kp_free_LB k LB)).
    assert (SUBf : forall b, In b (kp_free_LB k LB) -> In b LB) by (intros b Hb; unfold kp_free_LB, grp_free_LB in Hb; do 2 apply lb_free_mpds_sub in Hb; exact Hb).
    assert (SUBr : forall b, In b LBr -> In b LB) by (intros b Hb; subst LBr; apply In_lb_remove in Hb; apply SUBf; exact Hb).
    pose proof (hm_aobj_block asegs R HIA h LB LF m A 256 HH CIN) as OBJ.
    pose proof (uw_obj_block asegs R HIA h LB LF m A 256 A 256 0 HH ltac:(apply in_app_iff; left; exact CIN) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as UWO.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB LBr LF (bv_unsigned sp) (arl_stklo R) [] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) SUBr) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. pose proof (conj K I) as Kbox. clear K.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _]. destruct Kbox as [K _].
    assert (K1 : ecp_keypair_at asegs MT m1 LB A k).
    { eapply ecp_keypair_at_munch; [exact K| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - SX; lia|].
      intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m LB (LB ++ LF) dd) as (_ & _ & I3 & I4 & _);
        [eapply kp_mpds_mpdr; [exact K| exact Hd]| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia]. }
    clear MU0 WM0 MIm K.
    (* [comment removed for export] *)
    zstep.
    pose proof KPFREE as SG. unfold ecp_keypair_free_stmtA, A_ECP_KEYPAIR_FREE, ECP_KEYPAIR_SIZE in SG.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG with (h := h) (LB := LB) (LF := LF) (A := A) (k := k) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by (clear - SPR SLO NEEDR LOS ALO ACP; lia);
        first [ exact HK1 | exact K1 | exact DIS | exact LOS | exact TP | exact UWO | reflexivity
              | lazymatch goal with
                | |- HM _ _ _ h LB LF _ => assumption
                | |- client_wrange _ _ _ _ A 256 => intros a Ha; right; right; exists (A, 256); split; [apply in_app_iff; left; exact CINF| cbn; clear - Ha; lia]
                | |- A + 256 <= lo \/ _ => left; exact SX
                | |- aobj _ _ _ _ A 256 => assumption
                | |- stk _ _ lo _ => assumption
                | |- lo <= _ => clear - SLO NEEDR; lia
                | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                | |- mem_inv _ _ => assumption
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold ECKEY_FREE_WRAP_PHI in BUD; unfold KF_PHI, GF_PHI, AVOL_CALL in *; clear - BUD; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold ECKEY_FREE_WRAP_FR in BUDF; unfold KF_FR, GF_FR, fr_charge in *; clear - BUDF D0; lia
                end
              | match goal with |- ?gg => idtac "KP-LEFT:" gg end ]. }
    cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO).
    injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & PX2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & KZ).
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST2, PX2 by (clear - SPR SLO NEEDR LOS ALO ACP; lia).
    unfold ECP_KEYPAIR_SIZE in PX2.
    replace (ret_pc (Z_to_bv 64 0xb2304)) with (Z_to_bv 64 0xb2304 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ =>
      pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ PX2 FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(cbn; clear - SX SLO NEEDR; lia)) as FR2; clear FRx end.
    assert (PX2' : presA asegs R LBr LF (bv_unsigned sp + -16) (arl_stklo R) (hstkhi asegs R HIA h) [] m1 m2).
    { rewrite <- HS2. eapply (presA_drop_freed asegs R HIA h2 (kp_free_LB k LB) LF LBr [] A 256 m2 m1 m2); [exact HH2| exact CINF| | exact DI1| exact DI2| clear - SLO NEEDR LOS ALO; lia|].
      - intros b x Hb Hx. subst LBr. split; [eapply In_lb_remove; exact Hb|]. intros E. apply (lb_remove_fst_neq _ _ _ (HMND _ _ _ _ HH2) Hb). rewrite E. reflexivity.
      - rewrite HS2. eapply presA_weaken; [exact PX2| subst LBr; intros b Hb; eapply In_lb_remove; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PXA2 : presW asegs R HIA h LBr LF (bv_unsigned sp) (arl_stklo R) [] m m2).
    { eapply presW_call; [exact PXA| exact PX2'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    clear PXA PX2 PX2' SG K1.
    repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                         | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (hcs_ok asegs R HIA h2) as CSOKc. pose proof (crange_mono _ _ _ _ HCS2 SCS) as SCSc.
    zstep. zstep. zstep. zstep. release_frame FR2 ST2 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    subst LBr. unfold A_WRAP_FREE_PK.
    eapply free_tail with (h0 := h) (n := 256) (d := d); first [exact HH2 | exact CINF | exact PXA2 | exact UWS | eassumption | reflexivity
      | lazymatch goal with
        | |- havol _ _ _ _ + _ <= _ => unfold ECKEY_FREE_WRAP_PHI; clear - HV2; lia
        | |- hfr _ _ _ _ + _ <= _ => unfold ECKEY_FREE_WRAP_FR; unfold KF_FR, GF_FR, fr_charge in *; clear - HFR2 D0; lia
        | |- lo <= _ => clear - SLO NEEDR NRT; lia
        end
      | match goal with |- ?gg => idtac "TAIL-LEFT:" gg end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Wraps.

Lemma A_rsa_free_wrap_spec : forall R (HIA : artA asegs R),
  asan_img_ok (arl_AL R) -> arl_free R = A_WRAP_FREE_PK -> rsa_free_stmtA asegs R HIA A_RSA_FREE ->
  0 <= arl_need_rt R -> 0 <= arl_need_free R ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  (forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  rsa_free_wrap_stmtA asegs R HIA A_RSA_FREE_WRAP.
Proof. intros. eapply A_rsa_free_wrap_walk; eauto. Qed.

Lemma A_eckey_free_wrap_spec : forall R (HIA : artA asegs R) MT,
  asan_img_ok (arl_AL R) -> arl_free R = A_WRAP_FREE_PK -> ecp_keypair_free_stmtA asegs R HIA MT A_ECP_KEYPAIR_FREE ->
  0 <= arl_need_rt R -> 0 <= arl_need_free R ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  (forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  eckey_free_wrap_stmtA asegs R HIA MT A_ECKEY_FREE_WRAP.
Proof. intros. eapply A_eckey_free_wrap_walk; eauto. Qed.
