(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_div_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_core_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_cmp_int A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24 A_mpi_div_mpi_M_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_shift_l_c24 A_mpi_add_sub_sz_c24 A_mpi_add_sub_o_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Unset Lia Cache.

Section WalkF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_DV.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_DV.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (X A B lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_DIV_MPI_STACK_A - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 320 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_DV in UARG; unfold A_SMALLOC_2_DV in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Variables (dX dA dB : mpd) (d : Z) (es : list mpd) (PHIb FRb : Z).   (* [comment removed for export] *)
  Hypothesis XE : X = md_addr dX.
  Hypothesis AE : A = md_addr dA.
  Hypothesis BE : B = md_addr dB.
  Hypothesis HNDk : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis H0M : HM asegs R HIA h LB LF m.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis W0AS : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis W0BLK : md_own dX = LHeap -> In (md_p dX, 4 * md_n dX) LB /\ 1 <= md_n dX.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis D0 : 0 <= d.

  Local Notation POSTD := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                             (div_mpi_rem_Rs LB dX dA dB) PHIb FRb lo m mo0).

  Section Fr.
  (* [comment removed for export] *)
  Variables (FB sp1 : Z) (w0 w1 w2 : word) (gapn : nat).
  Hypothesis SP1 : bv_unsigned sp - 304 <= sp1 <= bv_unsigned sp - 288.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis GAP : Z.of_nat gapn = bv_unsigned sp + -104 - (sp1 + 184).
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 256.
  Hypothesis CFB : crange CS FB 256.
  Hypothesis APF : forall B0 j, In (B0, j) LF -> FB + 256 <= B0 \/ B0 + j <= FB.
  Hypothesis ESF : Forall (fun e => client_range L (LB ++ fdata LF) lo (md_addr e) 16
                     /\ (md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ 1 <= md_n e)
                     /\ (md_addr e + 16 <= lo \/ bv_unsigned sp <= md_addr e)
                     /\ (md_own dX = LHeap -> md_addr e + 16 <= md_p dX \/ md_p dX + 4 * md_n dX <= md_addr e)
                     /\ (md_own dX <> LHeap \/ md_own e = LNull \/ md_p dX + 4 * md_n dX <= md_p e \/ md_p e + 4 * md_n e <= md_p dX)
                     /\ (md_addr dX + 16 <= md_addr e \/ md_addr e + 16 <= md_addr dX)
                     /\ (md_own e <> LNull -> md_addr dX + 16 <= md_p e \/ md_p e + 4 * md_n e <= md_addr dX)) es.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34979112605.700000KS1R5NEEDR2sp2lo3SLO3sp13SP1". (* [comment removed for export] *)
  Let LOC : lo <= sp1. Proof. clear - SLO SP1 NEEDR. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1540877545.300000<S2sp3sp13SP1". (* [comment removed for export] *)
  Let CSP : sp1 <= bv_unsigned sp. Proof. clear - SP1. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43689629866.7700000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
  Let FN64 : 64 <= 256. Proof. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L66151427842.1600000JS2FB2r03F641q1r1H2H02q02H4". (* [comment removed for export] *)
  Let FB8 : FB mod 8 = 0. Proof. clear - F64. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation LF1 := ((FB, 256) :: LF).
  Local Notation CSTA := (A_mpi_client2.cstateA asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es).
  Local Notation dv_sp := (A_mpi_div_mpi_C.dv_sp).
  Local Notation DCS := (A_mpi_div_mpi_C.DCS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FB sp1 w0 w1 w2 gapn).
  Local Notation SH4 := (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)).
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_DIV_MPI <= C24MAX.     (* [comment removed for export] *)
  Local Notation UWCD mq := (uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
  (* [comment removed for export] *)
  Local Notation C_CLEAN_X := (A_mpi_div_mpi_C.dv_CLEAN_X R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF).
  Local Notation S_cs_store := (A_mpi_div_mpi_S_c24.cs_store R HIA IMG NEEDR h LB LF ra sp m lo LOS SLO TOP LFB dX es DIMG H0M XW W0AS FB sp1 gapn SP1 F64 FRSH CFB ESF).
  Local Notation S_dcs_ok := (A_mpi_div_mpi_S_c24.dcs_ok ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FB sp1 w0 w1 w2 gapn).
  Local Notation S_uwcd_store := (A_mpi_div_mpi_S_c24.uwcd_store R HIA IMG NEEDR h sp lo LOS SLO d sp1 SP1).
  Local Notation S_opv_of_mpd := (A_mpi_div_mpi_S_c24.opv_of_mpd R HIA IMG).
  Local Notation S_cs_opv_ext := (A_mpi_div_mpi_S_c24.cs_opv_ext R HIA IMG NEEDR h LB LF ra sp m lo LOS SLO LFB dX es XW FB sp1 gapn SP1 FRSH ESF).
  Local Notation S_cs_opv_w := (A_mpi_div_mpi_S_c24.cs_opv_w R HIA IMG NEEDR h LB LF ra sp m lo LOS SLO LFB dX es XW W0AS FB sp1 gapn SP1 FRSH).
  Local Notation S_uwc_presA := (A_mpi_div_mpi_S_c24.uwc_presA_s R LF ra sp LFB FB sp1 gapn).
  Local Notation opv := (A_mpi_div_mpi_S_c24.opv R HIA).
  Local Notation SHB := (Z_to_bv 64 (Z.shiftr B 3 + al_sb AL)).
  Local Notation SHA10 := (Z_to_bv 64 (Z.shiftr (A + 10) 3 + al_sb AL)).
  Local Notation SHB8 := (Z_to_bv 64 (Z.shiftr (B + 8) 3 + al_sb AL)).
  Local Notation COK := (A_mpi_client2.chunk_okA (bv_unsigned sp) sp1 FB 256).
  Local Notation T2C t2pad := [C8 (Z_to_bv 64 (FB + 128)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 3); C4 t2pad].
  (* [comment removed for export] *)
  Local Notation RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6 :=
    (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) s7v s8v (Z_to_bv 64 FB) s10v s11v t3 t4 t5 t6).
  (* [comment removed for export] *)
  Local Notation DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq :=
    (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 SHB8 (Z_to_bv 64 (B + 8)) (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 FB) c128 c136 (Z_to_bv 64 FB))
         (T2C t2pad) [] gb [C4 u0; C4 u1; C4 u2] jq).

  Hypothesis COPY : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.   (* [comment removed for export] *)
  Hypothesis CSR : mpi_core_shift_r_stmtA asegs R HIA A_MPI_CORE_SHIFT_R.
  Hypothesis CMPI : mpi_cmp_int_stmtA asegs AL A_MPI_CMP_INT.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis IA2 : md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) -> img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  (* [comment removed for export] *)
  Variables (PF FF : Z).
  Hypothesis FIN_PHI : grow_PHI MPI_MAX_LIMBS + 4 * AVOL_CALL <= PF.
  Hypothesis FIN_FR : copy_FR d + 4 * fr_charge (d + 1) <= FF.

  #[using="Type"] Lemma uwc_raise_m : forall mx LO' TOP' vv F0' F1' dd, uwc asegs mx LO' TOP' vv F0' dd -> F1' + 16 <= vv -> uwc asegs mx LO' TOP' vv F1' dd.
  Proof.
    intros mx LO' TOP' vv F0' F1' dd HU HF. inversion HU; subst; [apply uwc_stop; assumption| eapply uwc_link; eassumption| apply uwc_cap; assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L26496199141.3 L29515765010.11L62037211595.7 L8931608776.1  L9366540546.10 00000<00X01301801_S2sp3sp13SP1S1R3HIA1h3sp12wa2wb2Hw2a02HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACP". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO SP1"] Lemma uwcd_munch : forall W mq m2, UWCD mq -> munch W mq m2 -> Forall (fun w => snd w <= sp1 + 184) W -> UWCD m2.
  Proof.
    intros W mq m2 UW MU HW. rt_facts.
    eapply uwc_floor with (F := sp1 + 184); [| clear; lia].
    eapply uwc_munch; [eapply uwc_raise_m; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
    intros a0 Ha. clear - HW Ha. induction HW as [|[wa wb] W' Hw _ IH]; [exact I|]. cbn [outside fst snd] in *. split; [lia| exact IH].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18080337898.5 L35663928186.7 L457170510.6   L57413683421.13L59652475261.3 L60098763854.3 L62018535662.1 L6203936179.1  L8931608776.1  00000@00U00f01P01Z01d01g01l021S1R2lo3LOS1a3HLAS1R3HIA1h2sp2lo3TOP1HS2sp2lo3sp13SP11aS1R3HIA1h2sp2lo3LOS3TOP3sp13SP11a3HLA1x2HxS2lo1a3HLAS1R2lo3LOSS1RS3sp1S3sp1". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 F64 FRSH ESF LOC CSP FN64 FB8"] Lemma cs_stack_step : forall mq hq LBq ls dW CS0 v f m2 a,
    CSTA mq hq LBq ls dW CS0 DV_FSH v f -> munch [(a, sp1)] mq m2 -> wmono asegs mq m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 -> lo <= a -> a <= sp1 ->
    CSTA m2 hq LBq ls dW CS0 DV_FSH v f /\ (UWCD mq -> UWCD m2).
  Proof.
    intros mq hq LBq ls dW CS0 v f m2 a CST MU WM MI2 ST2 HLA HAS. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (HH2 : HM asegs R HIA hq LBq LF1 m2).
    { eapply (hm_munch asegs R HIA hq LBq LF1 [(a, sp1)] mq m2 HHq MU WM). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      intros x Hx. left. left. rewrite HTq. clear - Hx HLA LOS SP1 TOP. lia. }
    split.
    - assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [] mq m2).
      { eapply (presA_drop_below asegs R HIA hq LBq LF1 _ a sp1 mq mq m2 sp1 HHq); [| clear; lia| clear - HLA LOS; lia].
        eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSq| clear - HLA; lia| clear - SP1 HAS; lia]| apply Forall_nil]. }
      eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := []); try eassumption; [apply Forall_nil|].
      apply Forall_forall. intros ac _. exact I.
    - intros UW. eapply uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition set_limbsA (d0 : mpd) (xs : list word) : mpd := mkMPD (md_addr d0) (md_sg d0) (md_n d0) (md_p d0) xs (md_pad d0) (md_own d0).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59314923118.400000;S2dX2dA1E1K". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO LFB XW W0AS gapn SP1 FRSH ESF SXA IA2 ESA"] Lemma opv_A : forall mq hq LBq ls CS0 v f, CSTA mq hq LBq ls dX CS0 DV_FSH v f -> opv hq mq dA.
  Proof.
    intros mq hq LBq ls CS0 v f CST.
    destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
    - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
      rewrite EQA. eapply S_cs_opv_w; exact CST.
    - eapply S_cs_opv_ext; [exact CST| exact (ESA NE)| exact IA2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02V0@D24976250634.402D52014138856.402D53578774111.260D64280614944.260D67038978349.402K45774582958.260L10183434347.7  L10711524986.213L1166768438.1   L11848892282.10 L11856975223.1  L12251719832.2  L12347009263.1  L13129583555.3  L13132267204.5  L13285652628.20 L1452953054.5   L14924917537.0  L15170693011.13 L15756354262.4  L16348087064.20 L18442818614.12 L18470185603.20 L19161047841.0  L19980016842.7  L21201505239.3  L21935447823.11 L22283799325.1  L22700250492.3  L22917020203.1  L2397676628.0   L23986819982.2  L25069779737.14 L25427714598.1  L25498419105.2  L25865452341.8  L26349011210.3  L26530157006.253L26565939539.6  L26985840473.9  L27940637589.11 L2803942888.1   L29074096193.384L29074168500.387L29428324939.11 L29956516996.0  L31388772227.20 L31407731254.330L31668341332.1  L3194437963.8   L32454903270.1  L3482559548.11  L3482839721.20  L34900154170.213L34979112605.7  L35663928186.7  L38155515253.20 L38235734261.1  L38948636245.0  L39172636981.0  L40149986470.2  L44011071610.2  L44157098448.5  L45155411430.1  L45777581288.4  L46480359477.12 L47992363050.2  L49037504437.6  L49330082295.2  L50996975716.1  L51632320110.3  L51794595714.2  L52045659405.3  L52101693566.14 L5259999888.212 L53530622874.253L53577728712.1  L54965870984.2  L54972843200.4  L5509432403.11  L55738333094.1  L56427974826.1  L576250137.214  L59308546384.3  L59308546384.4  L59308546384.5  L59308632045.3  L59308632561.3  L59308975980.10 L59314923118.1  L59577627664.253L59577822949.250L59970840047.3  L60098763854.3  L61486461140.11 L61670655514.8  L61868843.1     L62018535662.1  L6203415987.3   L62037211595.7  L6203936179.1   L62624524490.41 L63580607104.2  L63744388140.2  L64254333864.2  L65614147016.1  L66151427842.16 L67215427846.346L67744726869.20 L68660770180.1  L7485178018.6   L795199521.13   L8931608776.1   L9080220944.4   L9356559676.11  L9838743115.2   P49335587632.403P54978542206.261Q10596644647.217Q11801279589.260Q11801279589.402Q1343603249.348 Q1356123914.215 Q1356123914.264 Q1356123914.397 Q1432901526.217 Q14603997304.258Q15321523536.255Q15686527286.217Q16623256797.257Q17757173815.258Q20013594135.215Q20544175131.216Q22285648010.397Q22287729077.400Q22288293173.399Q24974040330.402Q28419147350.257Q3853030411.217 Q39029445783.215Q39029445783.264Q39029445783.397Q39033706924.348Q39212284437.258Q39212284437.400Q4184760842.216 Q42081808994.400Q4924309012.400 Q49698585326.259Q52016320488.402Q52744951088.260Q54255983964.399Q56761401107.400Q58397637280.258Q60511567613.258Q60511567613.400Q62965564504.401Q63231501142.397Q64054320522.215Q65424847505.260Q67365112715.258Q67366931124.255Q67367442255.257Q9072355532.257 Q9538787269.255 Q9538787269.397 00001802@03E04J06P07\07e08K08P09509909A09E09P09Q0:N0:_0:`0;N0;\0;m0;n0<<0<=0<U0<`0=K0=N0=V0=[0=\0=d0>D0>I0>P0>\0>h0?[0@10@?0@f0@j0Ag0Bd0CK0CL0Cm0D`0Dd0E00E40E`0F]0GG0Gb0H70Ho0I30I40I50I>0I?0IQ0IU0IV0J40J=0JR0JS0JX0Jb0Jh0K40Ke0Lh0M[0M`0Ma0N00NY0N]0Na0OG0OR0OS0OT0O`0Ok0P@0PC0Q:0R10R>0RH0RM0RN0RR0RU0RZ0S50S:0S;0SD0SM0SS0SX0T40U50Um0V00VF0W70W<0WK0X60X@0XA0XB0X^0YW0ZP0[?0[c0\R0]E0]l0^V0_<0_X0`?0`l0aS0ao0bY0cC0cm0df0eL0f00fW0gI0h?0i10iW0jA0j]0kN0l80lh0ma0nZ0oD10210X11<11d12[13E13i14b15H15n16T17;17_18GS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2dA2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2dA2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1X1A2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv3dW43W0k3XR52HB5Ha_st5Hl_stS2LF3LFB2dX2dA2FB4gapn3dLX1k2HK4XB164LENX3NRX3PXF2KN3xs24LEN22HB5Ha_st5Hl_stS3dX33N31S2LF2ra2sp3LFB2dX2FB3sp14gapn3dLX4XB16S3dLXS1R5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12XSS2dAS2lo3sp1S2FBS2dX3dW42K1FS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3dLX3ALO3NX14PX163PX03PXCS2dX2dA2dB3dW42LTSS1R3HIA1h1d3FRb2D04BUDF2FF6FIN_FR2hq1f2HF4HFRqS1R2lo3LOS3ALOS3sp13dLX3NRX3NX1FS3sp13dLX1k2HKSS1R3HIA1h2sp3TOP3sp13SP1S2dA3dW42GES1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dLX3ALO3PXCS1XS1X2xx1KS3dLXSS2dX3NW1S1R2lo3LOS2FB3sp13dLX3ALO2F13PXFS3dLXS1d3CAPS2dX3dX33AP3S2dX3dW43WAPS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S1d3FRb2FF6FIN_FR1f2HFS3dX31a2Ha3A30S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2FBS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW43XR5S2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW43XR5S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPSS1R2sp2lo3SLO3sp13SP13dLX3NRA3PX0S2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S2FBS2dX3dX33LVWS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACPS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3dLX3ALO3NX14PX163PX03PXCS2LF2ra2sp3LFB2dX2FB3sp14gapn3dLX4XB163NRXS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dLX3ALO4LENX3NX13PX03PXCS2loSSS3dLX3NRXSS2sp2dX3sp13SP12KKS2FBFS4PHIb2PF7FIN_PHI1v2HV3dX33CPBS2dA4NRAdS1R2sp2lo3SLO3sp13SP1FS3dLXS1R3HIA2h4S1k2HKS2sp3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12hq2XS1a2HaS2LF2ra2sp1X3LFB2dX2XE2FB3sp14gapn3dLX3SPR2F04SP1R3X0q4XB163XL03PX0S2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S3sp1FS2dX2dA2dB4NRAdS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2FBS2FBS2LF2ra2sp3LFB2dX2FB3sp14gapn3dLX4XB16S3dW42Z02N1FFS3dLX3NX12KNS2dX3X0q2KRS2dA3dX33dW41T3AX32PMS1KS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23ARvS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23ARvS2dX3X0q4XB16S1R2lo3LOSS3sp1FS2FBS1RS3sp1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1FS3dLX3NRXS3dLX3NRXS1k2P2S3sp1S3sp12r04SP1M1q1r1H2H02q02H4S2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dX23dX33dW41HS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dLX3ALO4LENX3NX13PX03PXCS1XS1R2lo3LOS3ALO3dW43PCkS1R3HIA1h4PHIb3BUD2PF7FIN_PHI2hq3dLX1v2HV3HVq3NRXS3sp1S2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1RFFS2LF3LFB2dX2FB4gapn3dLX4XB16S2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2lo3LFB2dX3sp14gapn3LOC3dLX1k4XB163xs24LEN2S2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF2lo3LFB2dX3sp14gapn3LOC3dLX1k4XB163xs24LEN2S2LF2lo3LFB2dX3sp14gapn3LOC3dLX1k4XB163xs24LEN23dW4S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN23ARvS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB4gapn3dLX4XB16S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB4gapn3dLX1k2F04XB163xs24LEN22HBS2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16S2LF3LFB2dX2FB4gapn3dLX4XB16S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX1k4XB163xs24LEN2S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX1k4XB163xs24LEN23dW4S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX1k4XB163xs24LEN2S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX2FB4gapn3dLX4XB16S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43XR52HBS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43XR5S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43XR52HB5Ha_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY CSR CMPI UWX SXA IA2 ESA FIN_PHI FIN_FR"] Lemma dv_FIN :
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> v + PF <= PHIb -> f + FF <= FRb ->
    Z.abs (mpd_val dLX) < (2 * md_n dA + 2) * A_mpi_div_mpi_M_c24.dvBT dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9fe38) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST EAX EAY EAZ EAD OXH OYH OZH OTH HK UW BPOS HV HF XF.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (arl_need_rt_amem R) as NRA.
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. apply Forall_cons_iff in CHq'. destruct CHq' as [SPC _]. cbn [fst snd] in SPC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWq & _); try eassumption.
    pose proof MWq as [(CXq & X8q & X0q & _) _]. pose proof (rw_cells_bound _ _ _ _ CXq) as XB16. cbn [cells_size csize Nat.add mpi_cells] in XB16. clear CXq.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & XL0 & LENX & NRX & OWX) SGXd]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX). rewrite EAX in CX, OXs. unfold mpi_cells in CX. unfold MPI_MAX_LIMBS in NRX.
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by (rewrite XE; clear - XB16 X0q; lia); [exfalso; rewrite XE in KR; clear - KR X0q; lia|].
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dLX)) by (clear - NRX; lia).
    zstep. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NRX; lia); [exfalso; clear - KN NX1; lia|].
    zstep. zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_core_shift_r_stmtA, A_MPI_CORE_SHIFT_R in CSR.
      eapply CSR with (h := hq) (LB := LBq) (LF := LF1) (X := md_p dLX) (n := md_n dLX) (cnt := k) (lo := lo) (xs := md_limbs dLX);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (eapply client_wrange_block; [apply in_or_app; left; exact INX| clear; lia| clear; lia]).
      all: try (rewrite HTq; clear - SP1 TOP; lia).
      all: unfold MPI_CORE_SHIFT_R_STACK_A; try (clear - NRX NX1 LENX PX16 PX0 PXC ALO LOS SLO SP1 SP1M NEEDR NRA HK; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CSR-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold mpi_core_shift_r_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & UA2 & LEN2 & _ & LV2 & ST2 & HH2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    lazymatch type of UA2 with u32arr _ _ _ ?l => set (xs2 := l) in * end.
    set (dX2 := set_limbsA dLX xs2).
    assert (CX2 : rw_cells asegs m2 (FB + 32) [C8 (Z_to_bv 64 (md_p dLX)); C2 (Z_to_bv 64 (md_sg dLX)); C2 (Z_to_bv 64 (md_n dLX)); C4 (md_pad dLX)]).
    { eapply rw_cells_transport; [exact CX| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add fst snd]. clear - PXF F1 ALO LOS SLO SP1 NEEDR LOC. lia. }
    assert (MLX2 : mpd_at asegs m2 LBq dX2).
    { split; [| exact SGXd]. unfold dX2, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAX.
      split; [exact CX2|]. split; [rewrite <- EAX; exact X8|]. split; [rewrite <- EAX; exact XL0|]. split; [rewrite LEN2; exact LENX|]. split; [unfold MPI_MAX_LIMBS; exact NRX|].
      rewrite OXH. split; [exact NX1|]. split; [exact INX|]. split; [exact PX16| exact UA2]. }
    assert (HPA2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dLX, md_p dLX + 4 * md_n dLX); (lo, sp1)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_cons; [cbn [fst snd]| apply Forall_nil]].
      - eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPX)| clear; lia| clear; lia].
      - eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]. }
    assert (CST2 : CSTA m2 hq LBq (set_nth 0 [dLX; dY; dZ; dT] dX2) dX (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dLX) (WX := [(md_p dLX, md_p dLX + 4 * md_n dLX); (lo, sp1)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OXH| clear; lia]| apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_nil]]. }
    cbn [set_nth] in CST2.
    assert (UW2 : UWCD m2).
    { eapply uwcd_munch; [exact UW| exact MU2|]. apply Forall_cons; [cbn [snd]; clear - PXC ALO LOS SLO SP1 NEEDR; lia| apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil]]. }
    clear MU WM SPC MU2 WM2.

    pose proof (opv_A _ _ _ _ _ _ _ CST2) as (CAv & OAv & ARv & A8v & _ & _ & NRAd & _ & SGA).
    rewrite <- AE in CAv, OAv, ARv, A8v. unfold mpi_cells in CAv.
    assert (ESX : sx16 (Z_to_bv 64 (md_sg dA)) = Z_to_bv 64 (md_sg dA)) by (destruct SGA as [K|K]; rewrite K; apply bv_eq; vm_compute; reflexivity).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWX : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 32) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 32 + 8, FB + 32 + 10)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OAv (A + 8) 2.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : rw_cells asegs m3 (FB + 32) _ |- _ => rename H into CX3 end.
    match goal with H : u32arr asegs m3 (md_p dLX) xs2 |- _ => rename H into UA3 end.
    rewrite ESX in CX3.
    set (dX3 := set_sg dX2 (md_sg dA)).
    assert (MLX3 : mpd_at asegs m3 LBq dX3).
    { split; [| exact SGA]. unfold dX3, dX2, set_sg, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAX.
      split; [exact CX3|]. split; [rewrite <- EAX; exact X8|]. split; [rewrite <- EAX; exact XL0|]. split; [rewrite LEN2; exact LENX|]. split; [unfold MPI_MAX_LIMBS; exact NRX|].
      rewrite OXH. split; [exact NX1|]. split; [exact INX|]. split; [exact PX16| exact UA3]. }
    assert (HPA3 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 32 + 8, FB + 32 + 10)] m2 m3).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ m2 m3 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST3 : CSTA m3 hq LBq (set_nth 0 [dX2; dY; dZ; dT] dX3) dX (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := m2) (d := dX2) (WX := [(FB + 32 + 8, FB + 32 + 10)]); try eassumption; try reflexivity.
      apply Forall_cons; [left; unfold dX2, set_limbsA; cbn [fst snd md_addr]; rewrite EAX; clear; lia| apply Forall_nil]. }
    cbn [set_nth] in CST3.
    assert (UW3 : UWCD m3).
    { eapply uwcd_munch; [exact UW2| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    clear MU WM.

    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (CH3 & _ & _ & _ & _).
    pose proof CH3 as CH3'. unfold A_mpi_div_mpi_C.DCS in CH3'. apply Forall_cons_iff in CH3'. destruct CH3' as [SPC3 _]. cbn [fst snd] in SPC3. unfold A_mpi_div_mpi_C.dv_sp in SPC3.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) with (mq := m3) as (MW3 & _ & _ & XW3 & XLS3 & CRW3 & CRWL3 & HFW3 & ASW3 & WFB3 & OW3); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 0%nat) (d := dX3) as (ML3 & NS3 & _ & LL3 & CR3 & CRL3 & HF3 & SL3 & _ & AS3 & OX3s); try eassumption; [reflexivity|].
    assert (OX3H : md_own dX3 = LHeap) by exact OXH.
    ddestruct (HF3 OX3H) as (P30 & P3C & IN3 & N31 & _ & FRL3).
    pose proof (A_mpi_client2.loc_vs_w asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW W0AS (md_addr dX3) SL3) as LVW.
    assert (W0C : client_range L (mpd_keep LB dX ++ fdata LF) lo (md_addr dX) 16) by (eapply (A_mpi_client2.w0_client asegs R HIA); eassumption).
    pose proof (fresh_apart_client R (mpd_keep LB dX) LF lo (md_addr dX) 16 _ _ FRL3 W0C ltac:(clear; lia) ltac:(clear - N31; lia) ltac:(clear - ALO LOS; lia)) as AP3.
    assert (SEP3 : copy_sep dX dX3 lo sp1).
    { split; [intros _; clear - AP3; lia|]. split.
      { intros OW. ddestruct (HFW3 OW) as (_ & _ & INW & _).
        destruct (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW m3 hq LBq (md_addr dX3) _ _ HH3 INW SL3) as [K|K]; [right; exact K| left; exact K]. }
      split.
      { destruct (limb_own_eq_dec (md_own dX) LHeap) as [OW|OW]; [| right; left; exact OW]. right. right. right.
        ddestruct (HFW3 OW) as (_ & _ & INW & NW1 & _).
        pose proof CST3 as CSTu. unfold A_mpi_client2.cstateA in CSTu. ddestruct CSTu as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WOK & _).
        ddestruct WOK as (_ & _ & _ & WB & _). destruct (WB OW) as [NIN _].
        destruct (hm_apart asegs R HIA hq LBq LF1 m3 HH3) as [_ BA].
        pose proof (blocks_apart_neq _ (md_p dX, 4 * md_n dX) (md_p dX3, 4 * md_n dX3) BA ltac:(apply in_or_app; left; exact INW) ltac:(apply in_or_app; left; exact IN3)
                      ltac:(intros E; apply NIN; rewrite E; apply in_flat_map; exists dX3; split; [left; reflexivity| apply mpd_blk_in; exact OX3H]) ltac:(cbn [snd]; clear - NW1; lia) ltac:(cbn [snd]; clear - N31; lia)) as K.
        cbn [fst snd] in K. exact K. }
      split; [exact AS3|]. split; [exact LL3|]. intros a Ha. pose proof ML3 as [(_ & _ & A30 & _) _]. clear - Ha A30. lia. }
    pose proof COPY as CPY. unfold mpi_copy_stmtA_x_c, mpi_copy_stmtA_gen_c, A_MPI_COPY in CPY.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CPY with (h := hq) (LB := LBq) (LF := LF1) (dX := dX) (dY := dX3) (lo := lo) (d := d);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH3 | exact HK1 | exact MW3 | exact NST | exact ML3 | exact SEP3 | exact XW3 | exact ST3 | exact LOS | exact MI3 | exact TPV | exact OW3 | exact OX3s | exact CR3 | exact CRL3 | exact UWX | reflexivity
              | lazymatch goal with
                | |- mpd_sep dX dX3 => right; clear - LVW; lia
                | |- lo <= sp1 - 112 - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- md_own dX3 = LStatic -> _ => intros EO; exfalso; exact (NS3 EO)
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL, MPI_MAX_LIMBS in *; change (md_n dX3) with (md_n dLX); clear - HVq BUD HV FIN_PHI NRX; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF FIN_FR D0; unfold fr_charge in *; lia
                | |- _ = Z_to_bv 64 (md_addr dX) => rewrite XE; reflexivity
                | |- _ = Z_to_bv 64 (md_addr dX3) => unfold dX3, dX2, set_sg, set_limbsA; cbn [md_addr]; rewrite EAX; reflexivity
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }

    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo3 & h4 & LB4 & dW4 & r
                    & E4 & MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4 & MW4 & OUT4 & FRS4 & RR4).
    injection E4 as Ems Emo. subst ms4 mo4.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite (unsigned_lit sp1) in ST4, HP4 by exact SP1R.
    destruct RR4 as [(RV & EA4 & PD4 & FRP4) TRIM4].
    assert (CST4 : CSTA m4 h4 LB4 [dX3; dY; dZ; dT] dW4 (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + copy_PHI dX3) (f + copy_FR d)).
    { eapply (A_mpi_client2.cs_binop_w asegs R HIA) with (mq := m3) (hq := hq) (SPx := sp1); try eassumption; try (clear - SP1; lia).
      - eapply (A_mpi_div_mpi_S_c24.w_aobj_step R HIA NEEDR h LB LF ra sp m lo LOS SLO LFB dX es XW W0AS FB sp1 gapn SP1 FRSH); [exact CST3| exact HP4| exact HCS4].
      - destruct RV as [(_ & _ & K1 & _)|(_ & K1 & _)]; clear - K1; lia.
      - unfold A_mpi_div_mpi_C.DCS. repeat (apply Forall_cons; [cbn [fst snd]|]); [left; clear; lia| left; clear; lia| left; clear; lia| left; clear; lia| left; clear - SP1; lia| right; clear; lia| right; clear; lia| right; clear; lia| apply Forall_nil].
      - apply Forall_forall. intros d0 _ K. exact K. }
    assert (UW4 : UWCD m4).
    { destruct UWX as [[XS _]|CAP]; [| apply uwc_cap; clear - CAP; lia].
      rewrite <- HSq. eapply S_uwc_presA; [exact HP4| rewrite HSq; exact UW3| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha XS LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF1 MF4))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV.
    assert (CPB : copy_PHI dX3 <= grow_PHI MPI_MAX_LIMBS) by (unfold copy_PHI, grow_PHI, MPI_MAX_LIMBS; change (md_n dX3) with (md_n dLX); clear - NRX; lia).
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    assert (HSZ4 : md_n dW4 <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB)).
    { unfold div_mpi_nz. destruct RV as [(R0 & _ & K1)|(_ & K1 & _)]; [| rewrite K1; apply Z.le_max_l].
      destruct (TRIM4 R0) as [T|[T|T]]; [rewrite T; apply Z.le_max_l| rewrite T; clear - NRAd; lia|].
      assert (AX3 : mpd_abs dX3 < 2 ^ (32 * (md_n dA + 2))).
      { pose proof MLX2 as [(_ & _ & _ & HL2 & _) _]. pose proof MLX as [(_ & _ & _ & HL0 & _) SG0].
        replace (mpd_abs dX3) with (mpd_abs dX2) by reflexivity. rewrite (mpd_abs_lval dX2 HL2). unfold dX2, set_limbsA. cbn [md_limbs md_n]. rewrite LV2.
        rewrite (mpd_val_abs dLX SG0), (mpd_abs_lval dLX HL0) in XF.
        pose proof (lval_range (md_limbs dLX) (md_n dLX) ltac:(clear - NRX; lia)) as LR.
        assert (P2 : 1 <= 2 ^ k) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(clear; lia) ltac:(clear - HK; lia)); lia).
        assert (DV : lval (md_limbs dLX) (md_n dLX) / 2 ^ k <= lval (md_limbs dLX) (md_n dLX)) by (apply Z.div_le_upper_bound; [clear - P2; lia| clear - P2 LR; nia]).
        unfold A_mpi_div_mpi_M_c24.dvBT in XF.
        assert (PW : 2 ^ (32 * (md_n dA + 2)) = 4294967296 * 2 ^ (32 * (md_n dA + 1))) by (replace (32 * (md_n dA + 2)) with (32 + 32 * (md_n dA + 1)) by (clear; lia); rewrite Z.pow_add_r by (clear - NRAd; lia); reflexivity).
        pose proof (Z.pow_pos_nonneg 2 (32 * (md_n dA + 1)) ltac:(clear; lia) ltac:(clear - NRAd; lia)) as PP.
        rewrite PW. clear - DV XF NRAd PP. nia. }
      destruct (Z_lt_le_dec (md_n dW4 - 1) (md_n dA + 2)) as [LT|GE]; [clear - LT; lia| exfalso].
      assert (PM : 2 ^ (32 * (md_n dA + 2)) <= 2 ^ (32 * (md_n dW4 - 1))) by (apply Z.pow_le_mono_r; [clear; lia| clear - GE; lia]).
      clear - PM T AX3. lia. }
    destruct RV as [(-> & _)|(-> & _)].
    2: { (* [comment removed for export] *)
      zstep. zstep.
      eapply C_CLEAN_X with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| intros K; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; clear - K; lia| exact HSZ4| |].
      - clear - HV FIN_PHI CPB. lia.
      - clear - HF FIN_FR. lia. }

    (* [comment removed for export] *)
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST4) as (CH4 & _ & _ & _ & HH4').
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST4) as (HT4' & HS4' & _ & HCS4' & _ & _).
    pose proof CH4 as CH4'. unfold A_mpi_div_mpi_C.DCS in CH4'. apply Forall_cons_iff in CH4'. destruct CH4' as [SPC4 _]. cbn [fst snd] in SPC4. unfold A_mpi_div_mpi_C.dv_sp in SPC4.
    pose proof (hcs_ok asegs R HIA h4) as CSOK4. pose proof (cs_ok_sb _ _ CSOK4) as SB644. pose proof (hcs_stack asegs R HIA h4) as SCS04.
    assert (SCS4 : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS04| clear - LOS; lia| rewrite HS4'; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    zstep. zstep. zstep. zstep.
    clear CST CST2 CST3 FRL3.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWk & NSWk & EAWk & _ & XLSk & _ & _ & HFWk & ASWk & _ & OWk); try eassumption.
    pose proof MWk as [(CWk & W8k & W0k & LENWk & NRWk & OWNk) SGWk]. unfold MPI_MAX_LIMBS in NRWk.
    eapply (aevtA_cut_evtA_KF asegs R HIA h4 mo0).
    { unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT in CMPI.
      eapply CMPI with (CS := hcs asegs R HIA h4) (LB := LB4) (dX := dW4) (z := 0) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (exact (art_alwf asegs R HIA)).
      all: try (exact (hm_abase asegs R HIA h4 LB4 LF1 m4 HH4')).
      all: try (rewrite EAWk; exact OWk).
      all: try (eapply crange_sub; [exact SCS4| clear; lia| clear - SP1; lia]).
      all: try (rewrite EAWk; destruct ASWk as [KK|KK]; [left; exact KK| right; clear - KK SP1; lia]).
      all: try (rewrite EAWk, XE; reflexivity).
      all: try (intros OWH; destruct (HFWk OWH) as (KK & _); exact KK).
      all: try (intros N1; assert (OWH : md_own dW4 = LHeap) by (destruct (md_own dW4) eqn:EO; [exfalso; destruct OWNk as [_ Z0]; clear - Z0 N1; lia| reflexivity| exfalso; exact (NSWk eq_refl)]);
                first [ (ddestruct (HFWk OWH) as (_ & _ & INk & _); eapply hm_aobj_block; [exact HH4'| exact INk]) | (ddestruct (HFWk OWH) as (_ & PCk & _); left; clear - PCk ALO LOS; lia) ]).
      all: try (clear - LOS ALO ACP SLO SP1 SP1M NEEDR; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CMPI-PRE-LEFT:" g end ]. }

    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU5 & WM5 & MI5 & ST5).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m5 end.
    destruct (cs_stack_step m4 h4 LB4 _ _ _ _ _ m5 lo CST4 MU5 WM5 MI5 ST5 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST5 UWK].
    pose proof (UWK UW4) as UW5. clear MU WM MU5 WM5 SPC4 CH4 CST4.
    assert (HV5 : v + copy_PHI dX3 + 4 * AVOL_CALL <= PHIb) by (clear - HV FIN_PHI CPB; lia).
    assert (HF5 : f + copy_FR d + 4 * fr_charge (d + 1) <= FRb) by (clear - HF FIN_FR; lia).
    assert (KEND : forall mz dWz, CSTA mz h4 LB4 [dX3; dY; dZ; dT] dWz (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + copy_PHI dX3) (f + copy_FR d) -> UWCD mz -> md_n dWz = md_n dW4 ->
              forall xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s10' t3' t4' t5' t6',
              aevtA asegs (KF asegs R HIA h4 mo0) POSTD
                (MS (RGM xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s10' (Z_to_bv 64 0) t3' t4' t5' t6') F (Z_to_bv 64 0x9f704) fc None mz (seg_rom asegs))).
    { intros mz dWz CSTz UWz NWz. intros.
      eapply C_CLEAN_X with (r := 0); [exact CSTz| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact UWz| clear; lia| intros _; exact BPOS| rewrite NWz; exact HSZ4| exact HV5| exact HF5]. }
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST5) as (CH5 & _ & _ & _ & HH5).
    pose proof CH5 as CH5'. unfold A_mpi_div_mpi_C.DCS in CH5'. apply Forall_cons_iff in CH5'. destruct CH5' as [SPC5 _]. cbn [fst snd] in SPC5. unfold A_mpi_div_mpi_C.dv_sp in SPC5.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    rewrite Z.sub_0_r.
    destruct (Z.sgn_spec (mpd_val dW4)) as [(GT & ->)|[(EQ & ->)|(LT & ->)]].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. eapply KEND; [exact CST5| exact UW5| reflexivity].
    - (* [comment removed for export] *)

      (* [comment removed for export] *)
      edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MW5 & NSW5 & EAW5 & XWW5 & _ & _ & _ & HFW5 & _ & _ & OW5); try eassumption.
      pose proof MW5 as [(CW5 & W85 & W05 & LENW5 & NRW5 & OWN5) SGW5]. rewrite EAW5 in CW5. rewrite <- XE in CW5, OW5. unfold mpi_cells in CW5.
      destruct XWW5 as [CWW5 _]. rewrite EAW5 in CWW5. rewrite <- XE in CWW5.
      assert (XR5 : 0 <= X /\ X + 16 <= 2^64) by (rewrite XE; clear - XB16 X0q; lia).
      assert (X85 : X mod 8 = 0) by (rewrite XE; exact X8q).
      clear MU WM.
      pose proof (munch_refl [(X + 8, X + 10)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
      zstep. zstep. zstep. zstep. zstep. shadow_chk OW5 (X + 8) 2.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
      match goal with H : HM asegs R HIA h4 LB4 LF1 m6 |- _ => rename H into HH6 end.
      match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
      match goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
      match goal with H : rw_cells asegs m6 X _ |- _ => rename H into CW6 end.

      set (dW6 := set_sg dW4 1).
      assert (MW6 : mpd_at asegs m6 LB4 dW6).
      { split; [| left; reflexivity]. unfold dW6, set_sg. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAW5, <- XE.
        split; [exact CW6|]. split; [exact X85|]. split; [rewrite XE; exact X0q|]. split; [exact LENW5|]. split; [exact NRW5|].
        destruct (md_own dW4) eqn:EO; [exact OWN5| | exfalso; exact (NSW5 eq_refl)].
        ddestruct OWN5 as (N15 & IN5 & P165 & UA5). split; [exact N15|]. split; [exact IN5|]. split; [exact P165|].
        ddestruct (HFW5 eq_refl) as (_ & _ & _ & _ & _ & WAP).
        eapply u32arr_transport; [exact UA5| exact MU| exact WM|]. cbn [disjoint_from]. rewrite LENW5. rewrite XE. split; [clear - WAP; lia| exact I]. }
      assert (HPA6 : presA asegs R LB4 LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA h4) [(md_addr dX, md_addr dX + 16)] m5 m6).
      { eapply presA_weaken with (LB := LB4) (LF := LF1) (SP := sp1) (SSP := arl_stklo R) (TOP := hstkhi asegs R HIA h4) (W := [(X + 8, X + 10)]);
          [| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx K; cbn [outside] in *; rewrite <- XE in K; clear - K; lia].
        eapply (presA_of_munch asegs R LB4 LF1 _ _ _ _ m5 m6 (hcs asegs R HIA h4) CSOK4); [| intros c0' Hc; eapply cshd_hcs; [exact HH6| | exact Hc]; clear; lia| exact MU| exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OW5)| clear; lia| clear; lia]| apply Forall_nil]. }
      assert (CST6 : CSTA m6 h4 LB4 [dX3; dY; dZ; dT] dW6 (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + copy_PHI dX3) (f + copy_FR d)).
      { eapply (A_mpi_client2.cs_upd_w asegs R HIA) with (mq := m5); try eassumption; try reflexivity. }
      assert (UW6 : UWCD m6).
      { destruct UWX as [[XS _]|CAP]; [| apply uwc_cap; clear - CAP; lia].
        eapply uwcd_munch; [exact UW5| exact MU|]. apply Forall_cons; [cbn [snd]; rewrite XE; clear - XS LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
      zstep.
      eapply KEND; [exact CST6| exact UW6| reflexivity].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. eapply KEND; [exact CST5| exact UW5| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY CSR CMPI UWX SXA IA2 ESA FIN_PHI FIN_FR"] Lemma dv_FIN_ok : A_mpi_div_mpi_M_c24.dvFIN_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn PF FF.
  Proof. unfold A_mpi_div_mpi_M_c24.dvFIN_stmt. exact dv_FIN. Qed.

  End Fr.
  End Call.
End WalkF.
