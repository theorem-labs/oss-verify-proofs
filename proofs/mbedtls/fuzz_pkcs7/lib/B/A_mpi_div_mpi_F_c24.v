(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_div_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_core_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_cmp_int A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24 A_mpi_div_mpi_M_c24 A_mpi_shift_r A_mpi_cmp_mpi_raw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_shift_l_c24 A_mpi_add_sub_sz_c24 A_mpi_add_sub_o_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
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
  Hypothesis SLOS : lo <= bv_unsigned sp - 352 - arl_need_smalloc R.
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
  Hypothesis SP1 : bv_unsigned sp - 336 <= sp1 <= bv_unsigned sp - 320.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis GAP : Z.of_nat gapn = bv_unsigned sp + -104 - (sp1 + 216).
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
  Local Notation T2C t2pad := [C8 (Z_to_bv 64 (FB + 176)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 3); C4 t2pad].
  Local Notation CZCp czp czpad := [C8 czp; C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 1); C4 czpad].
  (* [comment removed for export] *)
  Local Notation RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6 :=
    (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) (Z_to_bv 64 (FB + 80))
         (Z_to_bv 64 A) SH4 (Z_to_bv 64 B) s11v t3 t4 t5 t6).
  (* [comment removed for export] *)
  Local Notation DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq :=
    (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120
                (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 X) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 0) (Z_to_bv 64 FB))
         (T2C t2pad) [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq).

  Hypothesis COPY : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.   (* [comment removed for export] *)
  Hypothesis SHR : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.
  Hypothesis CMPR : mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis IA2 : md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) -> img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Variables (slo : Z).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO2 : slo <= lo.
  Hypothesis SSH0 : sshad asegs AL m slo (bv_unsigned sp).
  (* [comment removed for export] *)
  Variables (PF FF : Z).
  Hypothesis FIN_PHI : grow_PHI MPI_MAX_LIMBS + 4 * AVOL_CALL <= PF.
  Hypothesis FIN_FR : copy_FR d + 4 * fr_charge (d + 1) <= FF.

  #[using="Type"] Lemma uwc_raise_m : forall mx LO' TOP' vv F0' F1' dd, uwc asegs mx LO' TOP' vv F0' dd -> F1' + 16 <= vv -> uwc asegs mx LO' TOP' vv F1' dd.
  Proof.
    intros mx LO' TOP' vv F0' F1' dd HU HF. inversion HU; subst; [apply uwc_stop; assumption| eapply uwc_link; eassumption| apply uwc_cap; assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L12884375298.10L29515765010.11L5413320392.1  L62037211595.7 L63072848869.3 00000W01301801S01_S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R3HIA1h3sp12wa2wb2Hw2a02HaS3sp1S1R5NEEDR2sp2lo3LOS3SLO3SPRS2sp3sp13SP1". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO SP1"] Lemma uwcd_munch : forall W mq m2, UWCD mq -> munch W mq m2 -> Forall (fun w => snd w <= sp1 + 216) W -> UWCD m2.
  Proof.
    intros W mq m2 UW MU HW. rt_facts.
    eapply uwc_floor with (F := sp1 + 216); [| clear; lia].
    eapply uwc_munch; [eapply uwc_raise_m; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
    intros a0 Ha. clear - HW Ha. induction HW as [|[wa wb] W' Hw _ IH]; [exact I|]. cbn [outside fst snd] in *. split; [lia| exact IH].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18080337898.5 L35663928186.7 L457170510.6   L5413320392.1  L57413683421.13L59652475261.3 L60098763854.3 L62018535662.1 L6203936179.1  00000@00U00f00k01U01_01i01l021S1R2lo3LOS1a3HLAS1R3HIA1h2sp2lo3TOP1HS2sp2lo3sp13SP11aS3sp1S1R3HIA1h2sp2lo3LOS3TOP3sp13SP11a3HLA1x2HxS2lo1a3HLAS1R2lo3LOSS1RS3sp1". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18080337898.5 L35663928186.7 L457170510.6   L5413320392.1  L57413683421.13L59652475261.3 L60098763854.3 L62018535662.1 L6203936179.1  00000@00U00f00k01U01_01i01l021S1R2lo3LOS1a3HLAS1R3HIA1h2sp2lo3TOP1HS2sp2lo3sp13SP11aS3sp1S1R3HIA1h2sp2lo3LOS3TOP3sp13SP11a3HLA1x2HxS2lo1a3HLAS1R2lo3LOSS1RS3sp1". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 F64 FRSH ESF LOC CSP FN64 FB8"] Lemma f_cs_stack_step : forall mq hq LBq ls dW CS0 SHC v f m2 a,
    CSTA mq hq LBq ls dW CS0 SHC v f -> munch [(a, sp1)] mq m2 -> wmono asegs mq m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 -> lo <= a -> a <= sp1 ->
    CSTA m2 hq LBq ls dW CS0 SHC v f /\ (UWCD mq -> UWCD m2).
  Proof.
    intros mq hq LBq ls dW CS0 SHC v f m2 a CST MU WM MI2 ST2 HLA HAS. rt_facts.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "09E0@D24976250634.481D28250049055.393D35617972959.398D35617972959.399D43080244883.393D50215630175.266D52014138856.481D52337554464.266D55579844745.398D67038978349.481D9411077970.399 K3576858960.486 K43479278672.484K45774582958.266K49335587632.482K50573164112.483K65183577936.485L10183434347.7  L10596430123.1  L10780327787.2  L10994491731.3  L1104935590.1   L1119910786.2   L1166768438.1   L11792259177.1  L11856975223.1  L12098237581.380L12251719832.2  L12266043405.1  L12267397436.2  L12285457344.13 L12469921329.0  L12942039165.4  L13109208497.1  L13129583555.3  L13132267204.5  L13232367216.3  L13942988826.10 L13945231423.6  L13945524892.8  L13956014909.3  L14284640027.2  L14447004729.1  L14447004729.2  L1452953054.5   L14782354334.7  L14782585149.6  L14793915263.2  L14797038143.2  L15170693011.13 L15373145186.9  L15374837476.7  L15375133767.6  L15376930629.2  L15634843742.1  L15756354262.4  L15822417165.1  L15824827452.2  L1685717371.0   L1720391334.1   L17322624197.2  L1783081967.1   L18442818614.12 L18470185603.20 L18972077998.3  L19980016842.7  L21036585719.13 L21201505239.3  L21228526875.13 L21577549698.0  L21866712442.1  L21868500043.2  L22002391606.336L22283799325.1  L22317299610.258L22378827755.6  L22700250492.3  L22917020203.1  L22939159100.2  L2397676628.0   L23986819982.2  L24023900370.0  L24437484229.2  L24982576641.464L25219257385.453L25427714598.1  L25438042383.11 L2545017055.379 L25498419105.2  L2584991287.9   L25865452341.8  L26349011210.3  L26565939539.6  L26838715138.13 L26985840473.9  L27287902542.380L27830289819.1  L27940405558.7  L27940637589.6  L27942514839.3  L27993841605.2  L29074163277.464L29074168500.467L29428324939.5  L29443236169.3  L29784415085.481L29788741724.7  L29956516996.0  L30334941133.1  L30336823036.2  L30399176481.0  L3045595043.13  L30805168729.13 L31034375991.6  L31106126158.6  L31106358253.8  L31121041996.3  L3194437963.8   L32454903270.1  L32482764419.20 L33001125733.49 L33007376959.49 L33234217204.3  L33578466172.385L33633551754.17 L34748944355.2  L34759441986.7  L34759668961.5  L34761608388.9  L3480690494.2   L3482559548.6   L3482791583.7   L3482839721.20  L34979112605.7  L35663928186.7  L3588131735.2   L36415413615.1  L36523706914.2  L36523706914.3  L37185112175.384L37250098319.11 L37251814921.8  L37252045994.7  L37253916584.4  L38235734261.1  L38551529394.0  L3886437182.4   L38948636245.0  L39172636981.0  L39195090679.13 L39288703771.13 L40066129279.1  L40066129279.2  L40517951613.4  L40709922538.453L41064432956.2  L42411609006.0  L42826186982.1  L43058161753.13 L43477968535.2  L43585312641.1  L44011071610.2  L44157098448.5  L44654336316.2  L44656115725.1  L44994687875.4  L45130272096.28 L45223273812.1  L45777581288.4  L46305539319.13 L46480359477.12 L46776410825.2  L47992363050.2  L4800151836.8   L48374623544.5  L48925634523.6  L48925634523.8  L48925634523.9  L48926158682.13 L49037504437.6  L49330082295.2  L50575522967.2  L50837052601.0  L50996975716.1  L51352513313.0  L51632320110.3  L51794595714.2  L52045659405.3  L52101693566.14 L5259801613.463 L5259999888.219 L53529584078.258L54054323036.3  L5412792008.3   L5413320392.1   L54523052982.7  L54965870984.2  L54972843200.4  L56119133011.11 L56344447542.8  L56427974826.1  L56451432934.1  L57387013133.6  L576250137.379  L58083356955.13 L58815124353.1  L58835407131.1  L59308546384.3  L59308630368.3  L59308632561.3  L59308975980.10 L59311074534.8  L59314923118.1  L59577627664.258L59577822949.255L59970840047.3  L60098763854.3  L61670655514.8  L61798214783.1  L61798214783.2  L61868843.1     L62018535662.1  L6203415987.3   L62037211595.7  L6203936179.1   L62095858632.3  L62127882130.1  L62282932196.1  L62623490959.384L62799502113.0  L629676416.10   L63544410086.1  L63580607104.2  L63800406256.385L64254333864.2  L64331618245.2  L6512450649.13  L65183118794.3  L65613626824.3  L66107333501.4  L66151427842.16 L66234598.1     L67215427846.349L68561933542.1  L68660770180.1  L68699744090.57 L68699744090.58 L7485178018.6   L7519336234.49  L7519336234.50  L7531541105.49  L7735748552.2   L7738195705.2   L776496616.3    L795199521.13   L829317888.2    L8343148922.10  L881835912.0    L8931088584.3   L905100669.4    L905620861.2    L9080220944.4   L9113469884.13  L9171490621.4   L9175014120.1   L9356559676.11  L9631767342.6   L9838743115.2   L9924960261.2   P10773621127.484P1107370100.484 P12278670331.398P12278670331.399P14461423358.393P14783166904.393P15835051771.398P15835051771.399P17318485811.484P21870859916.398P21870859916.399P22945712379.398P22945712379.399P24433340723.484P27989722163.484P30347570235.398P30347570235.399P3576858960.486 P36523116728.393P40077402040.393P43479278672.484P44651977723.398P44651977723.399P49335587632.482P50573164112.483P54978542206.267P61800574648.393P64335891507.484P65183577936.485P7750690063.393 P7750690063.398 P7750690063.399 P9920822259.484 Q10579110768.388Q10579110769.387Q10579110771.389Q10579110782.386Q10579110783.385Q10596710310.389Q1103009890.397 Q1103009890.398 Q11124718681.395Q11799173861.389Q11799173861.467Q11801279589.266Q11801279589.393Q11801279589.398Q11801279589.399Q11801279589.481Q13544917990.390Q13544917990.468Q14101852574.381Q14349578653.378Q14603997304.264Q15321523536.261Q17048688612.379Q17827947541.386Q18087146764.462Q18775750062.396Q19821305046.397Q19821305046.398Q20023545321.397Q20191731767.389Q21454448774.391Q21456539716.386Q21456539721.389Q21456539722.388Q21456539723.387Q21538057956.392Q22285584006.481Q22287729077.484Q22288293173.483Q22821429170.398Q22868514764.263Q23225647464.390Q23225647464.468Q23605328050.398Q24974040330.486Q25263405308.487Q26196310761.397Q26314584654.390Q26314584654.391Q26314584654.468Q26316671538.375Q27174574993.266Q27297536113.487Q27359195790.389Q27469433926.395Q28096292234.224Q28212980322.397Q28212980322.398Q28419147350.263Q28659803101.263Q28945680805.395Q2940082018.394 Q30062200162.394Q30179009431.223Q30179009431.270Q3036956912.388 Q3036956913.387 Q3036956915.389 Q3036956926.386 Q3036956927.385 Q30450927206.385Q30450927207.386Q30450927208.387Q30450927209.388Q30450927210.389Q30680983297.388Q30802955094.390Q31438667564.390Q31438667564.468Q31577921210.391Q32127118376.391Q32329107814.385Q32329107815.386Q32329107816.387Q32329107817.388Q32329107818.389Q32454656875.389Q32804381142.386Q32804381143.385Q32804381144.388Q32804381145.387Q32804381147.389Q33742177293.394Q34089326809.378Q34357517856.384Q34669208217.380Q34702050737.390Q34702050737.468Q34964695574.388Q35515373300.480Q36340694389.389Q36340694390.388Q36340694391.387Q36721801750.387Q37313495734.395Q37315397645.480Q37315464705.481Q37744718870.385Q37744718871.386Q37744718872.387Q37744718873.388Q37744718874.389Q38251425369.395Q38542462901.487Q38927412047.391Q38962842163.386Q38964949745.390Q38964949745.468Q39212284437.264Q39212284437.484Q39234993220.389Q39234993222.387Q39234993223.388Q39234993224.385Q39234993225.386Q39527480644.389Q39527480646.387Q39527480647.388Q39527480648.385Q39527480649.386Q39688975392.379Q39962575253.389Q39962575254.388Q39962575255.387Q39962575256.386Q39962575257.385Q41524277967.395Q41526247032.481Q41526704244.480Q42081808994.484Q42489001010.385Q42489001011.386Q42489001020.387Q42489001021.388Q42489001022.389Q42491088113.391Q43082486931.392Q43399686461.391Q43945613965.480Q44298944140.375Q44301027056.390Q44301027056.391Q44301027056.468Q44330035869.380Q44894040693.395Q45187620132.487Q45460977850.391Q46095256701.394Q47321560996.388Q47321560997.387Q47321560999.389Q47321561002.386Q47321561003.385Q47323647848.391Q47799716979.374Q47799716979.462Q47976846438.397Q48234175664.392Q48590533430.395Q4924309012.484 Q49698585326.265Q49698585326.391Q49698585326.396Q49698585326.397Q49954538313.389Q49954538314.388Q49954538315.387Q49956649862.391Q50006609944.385Q50062131060.389Q50977310118.385Q50977310119.386Q50977310120.387Q50977310121.388Q50977310122.389Q51016035644.387Q51163671249.389Q51163671250.388Q51173003698.398Q51956833029.397Q51956833029.398Q52016320488.486Q52017706519.224Q52079534349.389Q52744951088.266Q54043690827.387Q5406763584.389 Q5408854671.391 Q5418299166.391 Q54255983964.483Q54281487746.385Q54281487747.386Q54281487756.387Q54281487757.388Q54281487758.389Q54481541668.384Q54512832306.385Q54687589067.390Q54687589067.468Q55568379588.389Q55568379590.387Q55568379591.388Q55568379592.385Q55568379593.386Q55963253062.395Q56560127590.385Q56560127591.386Q56560127592.387Q56560127593.388Q56560127594.389Q56761401107.484Q5694376087.223 Q57339358596.389Q57339358598.387Q57339358599.388Q57339358600.385Q57339358601.386Q58116659846.391Q58118758985.389Q58118758986.388Q58189595940.386Q58189595941.385Q58189595945.389Q58189595946.388Q58189595947.387Q58191707622.391Q58397637280.264Q58481443915.387Q58972088529.383Q58997395252.487Q59228252318.487Q59581139423.392Q59615732211.462Q60496793856.389Q60511567613.264Q60511567613.484Q61991282045.394Q62093694068.394Q62223702352.388Q62368757662.394Q62965564504.485Q63043732234.223Q63231436122.481Q6361077770.223 Q6361077770.270 Q64140058182.395Q64228675114.390Q64228675114.467Q64944938497.388Q65952862367.398Q66098993732.386Q66281897117.391Q66641604420.389Q66641604422.387Q66641604423.388Q66641604424.385Q66641604425.386Q67127742067.374Q67287962010.381Q67365112715.264Q67366931124.261Q67367442255.263Q67828983654.385Q67828983655.386Q67828983656.387Q67828983657.388Q67828983658.389Q68077445246.462Q68123692367.395Q68205412585.397Q68534218551.264Q6912043759.383 Q8482331796.389 Q8482331798.387 Q8482331799.388 Q8482331800.385 Q8482331801.386 Q866574337.388  Q9407741565.394 Q9538458057.481 Q9538787269.261 Q9558320337.389 Q9558320338.388 Q9558320339.387 Q9558320348.386 00001802:04305l06n08309;0:@0<80>>0@60@70@80A=0A>0A?0A@0AI0AM0AN0AY0A]0A^0Ac0Ag0Ak0Al0B40B80B90Bb0Bc0Bd0Be0C00C10C=0C>0C?0C@0CA0CB0CG0CH0CY0CZ0C[0C\0C]0DK0DL0DM0DN0DO0DP0D^0Db0Dc0Dd0Dh0Di0Dm0Dn0E<0ED0E\0E`0Ek0Eo0F00F40F50Fh0Fk0G^0H30H;0H@0HA0HB0HJ0HK0HL0IE0IF0IK0J60Ji0K00KS0K_0Kk0LA0LF0LT0Mk0Mo0NJ0NK0NL0NM0OJ0PG0PY0PZ0QS0QW0QX0Q\0Q]0Q^0RG0S00SC0SD0SE0SF0SR0SV0T70T80T90TE0U80U90U:0U;0U<0U=0U>0U?0U@0V=0VX0Vm0Vn0W20W<0W=0X00X10X20X30X40X80X90X:0X;0X<0X@0XD0XI0XJ0XK0Yh0Yi0Yj0Yn0ZW0ZX0Z]0Z^0[00[10[50[D0\<0\@0\A0\E0\c0\d0\m0]A0]V0]W0]X0]Y0]Z0]o0^00^10^20^70^80^B0^H0^T0_E0`B0aE0b80b90b>0bC0b^0b_0bn0cW0cm0d10d50d<0do0e30e80e90eD0eN0eY0en0eo0f20fi0g`0gm0h70h80h=0h>0hB0hE0hJ0he0hj0ho0i00i40ig0ih0ii0im0j60ji0jo0k00kY0kZ0k_0k`0lK0lO0mO0mS0mV0mW0mX0mn0mo0n00n10n20n30n?0o00o:0o_0o`0oe0of0og10610_10`10d11O11V11`11a13714j16H17f19D1:b1<@1=^1?Q1@o1BM1Ck1EI1G<1Ho1JM1Kk1Kl1MJ1Nh1Ni1PG1Qe1Qf1Qg1Qh1SF1U91U:1VP1WQ1XO1ZB1ZC1ZD1ZE1ZF1ZG1Zn1Zo1[01[X1\V1]X1^Q1_G1`A1a81b11cN1do1eg1f_1gI1go1hg1im1jX1kH1kI1kJ1lD1lE1mG1nC1o?20;21721m22W23A23k24b25I26m28U29L2:E2;A2<;2=92>72?92?e2@^2@_2@`2AH2Ao2Bi2C`2DF2Dm2Dn2Do2EW2F>2G02G12G22G32G42G52HS2J12KO2Lm2NK2NL2O92O:2O;2O<2O=2P[2R92SW2U52VS2W:2XX2Z62[T2]22^P2^Q2_I2`G2a?2bK2c[2d^2eJ2eK2eL2eM2fS2g;2gg2hS2hT2hU2hV2hW2hX2hY2hZ2h[2i^2jg2l42lZ2mD2mE2mF2mG2mH2mI2mJ2mK2mL2mM2mN2nF2nG2nH2nI2nJ2nK2o32o_30K31<32?33B34E35H36K37T38J39V3:B3:n3;l3<j3=l3>d3?T3@S3@T3A<3BZ3D83EV3G43HR3J63J]3KH3LB3LC3LD3Ln3M^3NN3O?3P03Pl3Qh3Rd3Sf3Tl3UT3W23XP3Yn3[L3\j3]m3]n3]o3^f3^g3^h3_a3`E3`m3af3ag3bc3ce3cf3dP3dQ3dR3dS3dT3dU3e`3fc3fd3fe3ff3fg3fh3fi3fj3gR3i03jN3kl3mJ3nh3oV40=40>40?40@40A40B41D42@43<44S45j47A48X49o4;L4<24<34<k4<l4<m4=c4=d4>K4>o4?W4@?4@g4Am4An4Be4CI4D34DW4EF4En4G[4IV4IW4JN4JO4JP4JQ4JR4JS4JT4JU4K<4L44LZ4M@4Mf4OD4Pb4R@4S^4U<4Ug4VO4WI4X64Xn4Xo4Y04Y14Y24Y34Y44Y\4ZD4Zh4Zi4Zj4Zk4ZlS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A3TOP3LFB2dX2FB3sp14gapn3GAP3dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv2h44HT4'2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A3TOP3LFB2dX2FB3sp14gapn3GAP3dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv2h44HT4'2HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2dA2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2ra2sp1A3LFB2dX2dA2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1X1A2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv3dW43W063WRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv2HB5Ha_st5Hl_stFFS2LF3LFB2dX2dA2FB4gapn3dLX1k2HK4XB164LENX3PXF3xs24LEN22HB5Ha_st5Hl_stFFFS3dX33N31S2FBFS2sp2FB3sp1S2FBFS3dLXS2FBS2dAFS2lo3sp1S2FBFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FFFS2dX3dW42K1FS2sp3sp13SP1FFFFSS3sp1FS2dX2dA2dB3dW42LTFFFFS1R3HIA1h1d3FRb2D04BUDF2FF6FIN_FR2hq1f2HF4HFRqFFFFFS1R2lo3LOS3ALOS2FBFSS2FBFS2FBFS3sp13dLX1k2HKS2lo3sp1S1R3HIA1h2sp3TOP3sp13SP1S2FBS2dA3dW42GES2FBSS2FBFS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S1XS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S1R2lo2FB3sp13LOC3MB5S1X2xx1KS3dLXFSS2dX3NW1SFS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW4FS3dLXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dLX3ALO3PXCS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S1d3CAPS1R5NEEDR2sp2lo3SLO3sp13SP13slo3SL2S2dX3dX33AP3S2dX3dW43WAPS1d3FRb2FF6FIN_FR1f2HFS3sp1S3dX31a2Ha3A30S1R2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEst5CM8st3x132HxS2FBS1R5NEEDR2sp2lo3SLO3sp13SP1FFFS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW43WRvS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW43WRvS1R2lo3LOS3ALO3ACPFS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW4S2FBSS2FBFSS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R3HIA1h2sp3TOP2HTFFFS2dX3dX33LVWS2FBS1R2sp2lo3SLO3sp13SP13dLX3NRA3PX0FFS2FB3dLX3PXFS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2FFFFFFFFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3dLX3ALO3NX14PX163PX03PXCS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HFS2FBS3sp14gapnFS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2FFFFS2loSFSSS2FBS2FBS3sp1FFS1R2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEst5CM8st3x282HxFSS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS3sp1SS2sp2dX3sp13SP12KKFS2FBS2sp2lo3sp13SP1S1R2lo3LOS2FB2r13F643ALO2q04SB321q1r1H2H02r02H42H52q12H9S2FBFS2FBS4PHIb2PF7FIN_PHI1v2HV3dX33CPBSS2dA4NRAdS1R2lo3LOS2FB3ALO2F1S2sp3sp13SP13SPR4SP1RFFFFS1R2sp2lo3SLO3sp13SP1FFFS3dLXSS1R3HIA2h4S1k2HKS2sp3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12hq2XS1a2HaS2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dW43WRvS2LF2ra2sp1X3LFB2dX2XE2FB3sp14gapn3dLX3SPR2F04SP1R3X0q4XB163XL03PX0S2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2FS3sp1S3sp1S1R5NEEDR2sp2lo3SLO3sp13SP1FS2dX2dA2dB4NRAdS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R2lo3LOS3dLX3ALO3PXCS2FBS2FBS2FB2F0S2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S2FBS3sp1FS3dW42Z02N1S1X3X852KAS2dX3X0q2KRS2dA3dX33dW41T3AX32PMFS1KS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23ARvS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23ARvS2dX3X0q4XB16S1R2lo3LOSFS3sp1FS2FBS1RS3sp1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp1FS2FBS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2SFS2FBS3dLX3NRXS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN2S1k2P2FS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS3sp1FS3sp12r04SP1M1q1r1H2H02q02H43dW43P162FB3F64S2FBS2LF2ra2sp1A3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN23dX33dW42LR1HS2FBS1XFFS1R2lo3LOS3ALO3dW43PCkFFFFFS2sp3sp13SP1S1R3HIA1h4PHIb3BUD2PF7FIN_PHI2hq3dLX1v2HV3HVq3NRXS3sp14SP1RS1R5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12XSSS3sp1FFS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2FB2F0S3sp14SP1RFS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dX2XE4W0AS4gapn3dLX1k2HK4XB163xs24LEN23dW42HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stFFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB4gapn3dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS2LF2sp3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF2sp3LFB2dX3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dX2XE2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB162KR3xs24LEN24WFB33dW43WRv2HB5Ha_st5Hl_stFFFFFS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2FFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN23ARvS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4SP1R4XB163xs24LEN22HBFFS2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF1X3LFB2dX2XE4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HBS2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16S2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2FFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16S2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX1k4XB163xs24LEN2FFFFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stFS2LF3LFB2dX2FB4gapn3dLX1k2F04XB163xs24LEN22HBFFFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stFS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4FFFS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4FFFFFFFFS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4FFFFFFFFFFS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFFFFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43WRv2HBS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3GAP3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN23dW4S1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HBS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4SP1R4XB163xs24LEN22HBS2LF1X3LFB2dX2XE4gapn3dLX1k2HK4XB163xs24LEN23dW42HB5Ha_st5Hl_stFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW42HB5Ha_st5Hl_stS2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2dA2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstFS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4FFFFFS1R5NEEDR2LF2sp2lo3SLO3LFB2dX2FB4gapn3dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF2lo3LFB2dX2FB3sp14gapn3LOC3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFFFFFFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43WRvS2LF2sp2lo3LFB2dX3sp14gapn3SP13dLX4XB16FFFFFS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK4XB163xs24LEN22HB5Ha_st5Hl_st5SAEstS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2FS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFS2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW43WRv2HB5Ha_stS2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF1X3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF2lo3LFB2dX3sp14gapn3LOC3dLX4XB16S2LF2lo3LFB2dX3sp14gapn3LOC3dLX1k4XB163xs24LEN2S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S1R2LF2ra2sp1A3LFB2dX2FB3sp14gapn3FB83dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv2HB5Ha_st5Hl_st5SAEstS1R2LF2ra2sp1X1A3LFB2dX2FB3sp14gapn3FB83dLX1k2HK3SPR2F04SP1R3X0q4XB163XL03PX03xs24LEN23ARv3dW43W063WRv2HB5Ha_st5Hl_st5SAEstFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFFFFFFS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN2S1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S2LF1A3LFB2dX4gapn3dLX1k4XB163xs24LEN2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dLX1k2HK3ALO2F14XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX2FB3sp14gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stS2LF3LFB2dX2FB4gapn3dLX1k2F04XB163xs24LEN22HBS1R2LF3LFB2dX2FB4gapn3dLX1k4XB163xs24LEN22HB5Ha_st5Hl_stFFFFFFS2LF3LFB2dX3sp14gapn3dLX1k4XB163xs24LEN2S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN23dW4S2LF3LFB2dX4gapn3dLX1k4XB163xs24LEN2FFFF".
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY SHR CMPR UWX SXA IA2 ESA slo SLO1 SLO2 SSH0 FIN_PHI FIN_FR"] Lemma dv_FIN :
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c64 c72 c80 c88 c96 c104 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120
               t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> v + PF <= PHIb -> f + FF <= FRb ->
    Z.abs (mpd_val dLX) < (2 * md_n dA + 2) * A_mpi_div_mpi_M_c24.dvBT dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6) F (Z_to_bv 64 0xa0274) fc None mq (seg_rom asegs)).
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
    pose proof (arl_need_rt_amem R) as NRA. assert (SLOP : (arl_stklo R <= slo /\ slo <= lo) /\ sshad asegs AL m slo (bv_unsigned sp)) by (split; [split|]; assumption). clear SLO1 SLO2 SSH0.
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. apply Forall_cons_iff in CHq'. destruct CHq' as [SPC _]. cbn [fst snd] in SPC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWq & _); try eassumption.
    pose proof MWq as [(CXq & X8q & X0q & _) _]. pose proof (rw_cells_bound _ _ _ _ CXq) as XB16. cbn [cells_size csize Nat.add mpi_cells] in XB16. clear CXq.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & ASX & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & XL0 & LENX & NRX & OWX) SGXd]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX). rewrite EAX in CX. unfold mpi_cells in CX. unfold MPI_MAX_LIMBS in NRX.
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by (rewrite XE; clear - XB16 X0q; lia); [exfalso; rewrite XE in KR; clear - KR X0q; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { pose proof SHR as SPEC. unfold mpi_shift_r_stmtA, A_MPI_SHIFT_R_E in SPEC.
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := dLX) (count := k) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (eapply client_wrange_block; [apply in_or_app; left; exact INX| clear; lia| clear; lia]).
      all: try (rewrite HTq; clear - SP1 TOP; lia).
      all: try (rewrite EAX; reflexivity).
      all: try (intros _; rewrite EAX; clear - PXF; lia).
      all: try (intros _; clear - PXC ALO ACV ACP LOS; lia).
      all: try (clear - NRX NX1 LENX PX16 PX0 PXC ALO LOS SLO SP1 SP1M NEEDR NRA HK; first [lia| Z.div_mod_to_equations; lia]). }
    cbv beta. intros ms' PO. unfold mpi_shift_r_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2 & MLX2 & LEN2 & LV2 & HH2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    lazymatch type of MLX2 with mpd_at _ _ _ (mkMPD _ _ _ _ ?l _ _) => set (xs2 := l) in * end.
    set (dX2 := set_limbsA dLX xs2).
    change (mpd_at asegs m2 LBq dX2) in MLX2.
    assert (HPA2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(lo, sp1); (md_p dLX, md_p dLX + 4 * md_n dLX)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_cons; [cbn [fst snd]| apply Forall_nil]].
      - eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia].
      - eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPX)| clear; lia| clear; lia]. }
    assert (CST2 : CSTA m2 hq LBq (set_nth 0 [dLX; dY; dZ; dT] dX2) dX (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dLX) (WX := [(lo, sp1); (md_p dLX, md_p dLX + 4 * md_n dLX)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OXH| clear; lia]| apply Forall_nil]]. }
    cbn [set_nth] in CST2.
    assert (UW2 : UWCD m2).
    { eapply uwcd_munch; [exact UW| exact MU2|]. apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_cons; [cbn [snd]; clear - PXC ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]]. }
    pose proof MLX2 as [(CX2 & _ & _ & _ & _ & OW2) _]. unfold dX2, set_limbsA in CX2, OW2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2, OW2.
    rewrite OXH in OW2. ddestruct OW2 as (_ & _ & _ & UA2). rewrite EAX in CX2. unfold mpi_cells in CX2.
    clear MU WM SPC MU2 WM2.

    pose proof (opv_A _ _ _ _ _ _ _ CST2) as (CAv & OAv & ARv & A8v & _ & _ & NRAd & _ & SGA).
    rewrite <- AE in CAv, OAv, ARv, A8v. unfold mpi_cells in CAv.
    assert (ESX : sx16 (Z_to_bv 64 (md_sg dA)) = Z_to_bv 64 (md_sg dA)) by (destruct SGA as [K|K]; rewrite K; apply bv_eq; vm_compute; reflexivity).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWX : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 80) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 80 + 8, FB + 80 + 10)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. zstep. shadow_chk OAv (A + 8) 2.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : rw_cells asegs m3 (FB + 80) _ |- _ => rename H into CX3 end.
    match goal with H : u32arr asegs m3 (md_p dLX) xs2 |- _ => rename H into UA3 end.
    rewrite ESX in CX3.
    set (dX3 := set_sg dX2 (md_sg dA)).
    assert (MLX3 : mpd_at asegs m3 LBq dX3).
    { split; [| exact SGA]. unfold dX3, dX2, set_sg, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAX.
      split; [exact CX3|]. split; [rewrite <- EAX; exact X8|]. split; [rewrite <- EAX; exact XL0|]. split; [rewrite LEN2; exact LENX|]. split; [unfold MPI_MAX_LIMBS; exact NRX|].
      rewrite OXH. split; [exact NX1|]. split; [exact INX|]. split; [exact PX16| exact UA3]. }
    assert (HPA3 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 80 + 8, FB + 80 + 10)] m2 m3).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ m2 m3 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST3 : CSTA m3 hq LBq (set_nth 0 [dX2; dY; dZ; dT] dX3) dX (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := m2) (d := dX2) (WX := [(FB + 80 + 8, FB + 80 + 10)]); try eassumption; try reflexivity.
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
              | dv_c24 R HIA HNDk C24H ]. }

    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo3 & h4 & LB4 & dW4 & r
                    & E4 & MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4 & MW4 & OUT4 & FRS4 & RR4).
    injection E4 as Ems Emo. subst ms4 mo4.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite (unsigned_lit sp1) in ST4, HP4 by exact SP1R.
    destruct RR4 as [(RV & EA4 & PD4 & FRP4) TRIM4].
    assert (CST4 : CSTA m4 h4 LB4 [dX3; dY; dZ; dT] dW4 (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (v + copy_PHI dX3) (f + copy_FR d)).
    { eapply (A_mpi_client2.cs_binop_w asegs R HIA) with (mq := m3) (hq := hq) (SPx := sp1); try eassumption; try (clear - SP1; lia).
      - eapply (A_mpi_div_mpi_S_c24.w_aobj_step R HIA NEEDR h LB LF ra sp m lo LOS SLO LFB dX es XW W0AS FB sp1 gapn SP1 FRSH); [exact CST3| exact HP4| exact HCS4].
      - destruct RV as [(_ & _ & K1 & _)|(_ & K1 & _)]; clear - K1; lia.
      - unfold A_mpi_div_mpi_C.DCS. repeat (apply Forall_cons; [cbn [fst snd]; first [left; clear - SP1; lia| right; clear; lia]|]). apply Forall_nil.
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
      { change (mpd_abs dX3) with (limbs_val xs2). rewrite LV2.
        rewrite (mpd_val_abs dLX SGXd) in XF. unfold mpd_abs in XF.
        pose proof (limbs_val_nonneg (md_limbs dLX)) as LR.
        assert (P2 : 1 <= 2 ^ k) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(clear; lia) ltac:(clear - HK; lia)); lia).
        assert (DV : limbs_val (md_limbs dLX) / 2 ^ k <= limbs_val (md_limbs dLX)) by (apply Z.div_le_upper_bound; [clear - P2; lia| clear - P2 LR; nia]).
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
      eapply C_CLEAN_X with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| reflexivity| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| intros K; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; clear - K; lia| exact HSZ4| |].
      - clear - HV FIN_PHI CPB. lia.
      - clear - HF FIN_FR. lia. }
    (* [comment removed for export] *)
    zstep.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4q & MI4' & ST4' & HH4').
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST4) as (HT4' & HS4' & _ & HCS4' & _ & _).
    pose proof CH4 as CH4'. unfold A_mpi_div_mpi_C.DCS in CH4'.
    apply Forall_cons_iff in CH4'. destruct CH4' as [SPC4 CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [T2C4 CH4'].
    apply Forall_cons_iff in CH4'. destruct CH4' as [ZC4 CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [CZ4 CH4'].
    apply Forall_cons_iff in CH4'. destruct CH4' as [GAP4 CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [SAVE4 CH4'].
    apply Forall_cons_iff in CH4'. destruct CH4' as [FHD4 CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [Z32C CH4'].
    apply Forall_cons_iff in CH4'. destruct CH4' as [Z48C CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [Z64C CH4'].
    apply Forall_cons_iff in CH4'. destruct CH4' as [TPC4 CH4']. apply Forall_cons_iff in CH4'. destruct CH4' as [JQ4 _].
    cbn [fst snd] in SPC4, T2C4, ZC4, CZ4, GAP4, SAVE4, FHD4, Z32C, Z48C, Z64C, TPC4, JQ4. unfold A_mpi_div_mpi_C.dv_sp in SPC4.
    clear MU WM. unfold A_mpi_div_mpi_P.DV_FSH in SH4q. cbn [app] in SH4q.
    pose proof (hcs_ok asegs R HIA h4) as CSOK4. pose proof (cs_ok_sb _ _ CSOK4) as SB644. pose proof (hcs_stack asegs R HIA h4) as SCS04.
    assert (SCS4 : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS04| clear - LOS; lia| rewrite HS4'; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFB4 : crange (hcs asegs R HIA h4) FB 256) by (eapply crange_mono; [exact HCS4'| exact CFB]).
    assert (INF : In (FB, 256) LF1) by (left; reflexivity).
    assert (MB5 : Z.shiftr FB 3 + al_sb AL + 4 + 1 <= lo).
    { pose proof (hcs_shadow_band asegs R HIA h4 (FB + 32) (CFB4 (FB + 32) ltac:(clear; lia))) as [_ SB32]. clear - SB32 ALO LOS F64.
      unfold shadow_of in SB32. rewrite !Z.shiftr_div_pow2 in * by lia. change (2 ^ 3) with 8 in *. Z.div_mod_to_equations. lia. }
    assert (LSA : forall d0, In d0 [dX3; dY; dZ; dT] -> md_addr d0 = FB + 80 \/ md_addr d0 = FB + 112 \/ md_addr d0 = sp1 + 184 \/ md_addr d0 = FB + 144).
    { intros d0 Hd0. destruct Hd0 as [<-|[<-|[<-|[<-|[]]]]]; [left; unfold dX3, dX2, set_sg, set_limbsA; cbn [md_addr]; exact EAX| right; left; exact EAY| right; right; left; exact EAZ| right; right; right; exact EAD]. }
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST4) as COK4.
    assert (GAPk : True /\ rw_cells asegs m4 (sp1 + 216) [CB gapn gb]) by (split; [exact I| exact GAP4]).
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 4 + 1)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : HM asegs R HIA h4 LB4 LF1 m5 |- _ => rename H into HH5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    match goal with H : stk asegs m5 lo sp1 |- _ => rename H into ST5 end.
    match goal with H : rw_cells asegs m5 (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into SH5 end.
    norm_b8 SH5.
    assert (GAP5 : rw_cells asegs m5 (sp1 + 216) [CB gapn gb]).
    { eapply rw_cells_transport; [exact (proj2 GAPk)| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from]. split; [right; clear - MB5 LOC; lia| exact I]. }
    pose proof (A_mpi_div_mpi_S_c24.rw_cells_nil_s m5 (sp1 + 184) ltac:(clear - SP1 SPR SP1R; lia)) as ZC5. clear GAPk.
    lazymatch type of SH5 with rw_cells _ _ _ ?cs => pose (SHC1 := cs) end.
    assert (CST5 : CSTA m5 h4 LB4 [dX3; dY; dZ; dT] dW4 (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) SHC1 (v + copy_PHI dX3) (f + copy_FR d)).
    { eapply (A_mpi_div_mpi_C.cs_shadow_write R HIA) with (mq := m4) (j := 4); try eassumption;
        first [ (clear; lia)
              | (intros d0 Hd0; destruct (LSA d0 Hd0) as [E|[E|[E|E]]]; rewrite E; clear - F0 F1 F2 ALO LOS SLO SP1 NEEDR; lia)
              | (unfold A_mpi_div_mpi_C.DCS; repeat (apply Forall_cons; [cbn [fst snd]; try unfold A_mpi_div_mpi_C.dv_sp; assumption|]); apply Forall_nil)
              | reflexivity ]. }
    assert (UW5 : UWCD m5) by (eapply uwcd_munch; [exact UW4| exact MU| apply Forall_cons; [cbn [snd]; clear - MB5 LOC; lia| apply Forall_nil]]).
    clear MU WM.
    assert (CWZ : client_wrange L (LB4 ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h4) (FB + 32) 4) by (eapply client_wrange_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 32, FB + 36)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5b end.
    match goal with H : HM asegs R HIA h4 LB4 LF1 m5b |- _ => rename H into HH5b end.
    match goal with H : mem_inv asegs m5b |- _ => rename H into MI5b end.
    match goal with H : stk asegs m5b lo sp1 |- _ => rename H into ST5b end.
    match goal with H : rw_cells asegs m5b (FB + 32) _ |- _ => rename H into Z32x end.
    pose proof Z32x as Z32y. apply rw_cells_CB_of in Z32y; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in Z32y.
    lazymatch type of Z32y with rw_cells _ _ _ [CB 8 ?zz] => set (z32a := zz) in Z32y end.
    assert (CST5b : CSTA m5b h4 LB4 [dX3; dY; dZ; dT] dW4 (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZCp czp czpad) gb z32a z48 z64 u0 u1 u2 jq) SHC1 (v + copy_PHI dX3) (f + copy_FR d)).
    { eapply S_cs_store with (mq := m5) (a := FB + 32) (b := FB + 36); try eassumption;
        first [ (clear; lia)
              | (right; split; clear; lia)
              | (intros d0 Hd0; destruct (LSA d0 Hd0) as [E|[E|[E|E]]]; rewrite E; clear - F0 F1 F2 ALO LOS SLO SP1 NEEDR; lia)
              | (unfold A_mpi_div_mpi_C.DCS; repeat (apply Forall_cons; [cbn [fst snd]; try unfold A_mpi_div_mpi_C.dv_sp; assumption|]); apply Forall_nil)
              | (eapply S_dcs_ok; [exact COK4| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]) ]. }
    assert (UW5b : UWCD m5b) by (eapply uwcd_munch; [exact UW5| exact MU| apply Forall_cons; [cbn [snd]; clear - F0 F1 F2 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]]).
    clear MU WM.
    apply (rw_cells_join_C2C2 asegs m5b (sp1 + 200) [C8 czp] (Z_to_bv 64 1) (Z_to_bv 64 1) [C4 czpad]) in CZ4. cbn [app] in CZ4.
    pose proof (munch_refl [(sp1 + 200, sp1 + 212)] m5b) as MU. pose proof (wmono_refl asegs m5b) as WM.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : HM asegs R HIA h4 LB4 LF1 m6 |- _ => rename H into HH6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
    match goal with H : rw_cells asegs m6 (sp1 + 200) _ |- _ => rename H into CZ6 end.
    assert (CST6 : CSTA m6 h4 LB4 [dX3; dY; dZ; dT] dW4 (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad [C8 (Z_to_bv 64 (FB + 32)); C4 (Z_to_bv 64 65537); C4 czpad] gb z32a z48 z64 u0 u1 u2 jq) SHC1 (v + copy_PHI dX3) (f + copy_FR d)).
    { eapply S_cs_store with (mq := m5b) (a := sp1 + 200) (b := sp1 + 212); try eassumption;
        first [ (clear; lia)
              | (left; split; clear - SP1; lia)
              | (intros d0 Hd0; destruct (LSA d0 Hd0) as [E|[E|[E|E]]]; rewrite E; clear - F0 F1 F2 ALO LOS SLO SP1 NEEDR; lia)
              | (unfold A_mpi_div_mpi_C.DCS; repeat (apply Forall_cons; [cbn [fst snd]; try unfold A_mpi_div_mpi_C.dv_sp; assumption|]); apply Forall_nil)
              | (eapply S_dcs_ok; [exact COK4| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]) ]. }
    assert (UW6 : UWCD m6) by (eapply uwcd_munch; [exact UW5b| exact MU| apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil]]).
    clear MU WM.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST6) as (_ & SH6 & _ & _ & _).
    pose proof (A_mpi_client2.cs_pres asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST6) as HP6.
    assert (SSH6 : sshad asegs AL m6 slo (bv_unsigned sp)).
    { pose proof SLOP as [[SL1 _] SS0]. eapply (presA_sshad asegs R); [exact HP6| exact SS0| exact SL1|]. pose proof (hm_top asegs R HIA h LB LF m H0M) as HT. clear - HT TOP. lia. }
    clear FRL3. edestruct (A_mpi_client2.cs_w_facts asegs R HIA) with (mq := m6) as (MW6 & NSW6 & EAW6 & _ & _ & _ & _ & HFW6 & ASW6 & _ & OW6); try eassumption.
    pose proof MW6 as [(CW6 & W86 & W06 & LENW6 & NRW6 & OWN6) SGW6]. unfold MPI_MAX_LIMBS in NRW6.
    pose proof (S_opv_of_mpd h4 LB4 LF1 m6 dW4 HH6 MW6 ltac:(rewrite EAW6; exact OW6) ltac:(intros EO; exfalso; exact (NSW6 EO))) as (CWv & OWv & WRv & W8v & EWB & LENW & NW & FWv & SGW).
    rewrite EAW6, <- XE in CWv, OWv, WRv, W8v. unfold mpi_cells in CWv.
    assert (BP4 : md_n dW4 = 0 \/ 0 < md_p dW4 /\ md_p dW4 mod 4 = 0).
    { destruct (md_own dW4) eqn:EO.
      - left. destruct OWN6 as [_ N0]. exact N0.
      - right. ddestruct OWN6 as (N1 & IN & P16 & UA). split; [exact (proj1 (FWv N1))| clear - P16; Z.div_mod_to_equations; lia].
      - exfalso. exact (NSW6 eq_refl). }
    assert (BPS : 1 <= md_n dW4 -> md_p dW4 + 4 * md_n dW4 <= lo \/ sp1 <= md_p dW4).
    { intros N1. assert (OWH : md_own dW4 = LHeap) by (destruct (md_own dW4) eqn:EO; [exfalso; destruct OWN6 as [_ Z0]; clear - Z0 N1; lia| reflexivity| exfalso; exact (NSW6 eq_refl)]).
      ddestruct (HFW6 OWH) as (_ & PCk & _). left. clear - PCk ALO LOS. lia. }
    assert (BS : X + 16 <= lo \/ sp1 <= X) by (rewrite XE; destruct ASW6 as [KK|KK]; [left; exact KK| right; clear - KK SP1; lia]).
    assert (QB : bytes_at asegs m6 (FB + 32) (u32s [Z_to_bv 64 0])).
    { pose proof Z32x as Z32p. chunk_split Z32p 1%nat Z32p0 Z32p1. clear Z32p1.
      apply u32arr_ro. eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 0))); [eapply rw_cells_reshape; [exact Z32p0| cbn; split; [apply (length_le4 (Z_to_bv 64 0))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (CZY : rw_cells asegs m6 (sp1 + 200) [C8 (Z_to_bv 64 (FB + 32)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 1); C4 czpad]).
    { pose proof (rw_cells_split_C4 asegs m6 _ [C8 (Z_to_bv 64 (FB + 32))] (Z_to_bv 64 65537) _ CZ6) as T22. cbn [app] in T22.
      assert (E2 : le2 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1)) by (rewrite !le2_of_Z; rewrite <- (CellsX.Z_to_le_bytes_mod 2 65537); reflexivity).
      assert (E3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) = Z_to_bv 64 1) by (rewrite unsigned_lit by (clear; lia); reflexivity).
      rewrite E3 in T22.
      eapply rw_cells_reshape; [exact T22| |].
      - cbn -[le2 le4 le8]. repeat split; try (rewrite ?length_le2, ?length_le4, ?length_le8; reflexivity).
      - cbn -[le2 le4 le8]. rewrite E2. reflexivity. }
    assert (OYZ : aobj asegs AL (hcs asegs R HIA h4) m6 (sp1 + 200) 16).
    { apply (A_mpi_div_mpi_S_c24.aobj_of_sshad_s R LF ra sp LFB FB sp1 gapn (hcs asegs R HIA h4) m6 slo (bv_unsigned sp) (sp1 + 200) 1 CSOK4 SSH6);
        [pose proof SLOP as [[_ SL2] _]; clear - SL2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCS4| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    assert (OQZ : aobj asegs AL (hcs asegs R HIA h4) m6 (FB + 32) 4).
    { eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA h4) m6 FB SHC1 (FB + 32) 4%nat 4);
        [exact CSOK4| exact SH6| eapply crange_sub; [exact CFB4| clear; lia| clear; lia]| exact FB8| clear - F0 F1 F2 ALO; lia| clear; lia| clear; lia| reflexivity]. }
    pose proof CMPR as CMPc. unfold mpi_cmp_mpi_raw_stmtA, A_MPI_CMP_MPI_E in CMPc.
    zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA h4 mo0).
    { eapply CMPc with (CS := hcs asegs R HIA h4) (X := X) (P := md_p dW4) (n := md_n dW4) (sg := md_sg dW4) (xs := md_limbs dW4) (pad := md_pad dW4)
                       (Y := sp1 + 200) (Q := FB + 32) (n' := 1) (sg' := 1) (ys := [Z_to_bv 64 0]) (pad' := czpad) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact CWv | exact EWB | exact LENW | exact NW | exact SGW | exact BP4 | exact W8v | exact CZY | exact QB
              | exact MI6 | exact (art_alwf asegs R HIA) | exact CSOK4 | exact (hm_abase asegs R HIA h4 LB4 LF1 m6 HH6)
              | exact OWv | exact OYZ | (intros N1; exact (proj2 (FWv N1))) | (intros _; exact OQZ) | exact ST6
              | exact BS | exact BPS | (clear - SP1R; lia)
              | (rewrite XE; exact X0q) | (rewrite XE; clear - X0q; lia)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1 NEEDR; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS4| clear; lia| clear - SP1; lia])
              | (right; clear; lia)
              | (left; reflexivity)
              | (right; split; [clear - F0 F1 F2 ALO; lia| clear - F64; Z.div_mod_to_equations; lia])
              | (intros _; left; clear - F0 F1 F2 ALO LOS; lia)
              | reflexivity
              | (clear; lia)
              | (f_equal; clear; lia) ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU7 & WM7 & MI7 & ST7).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m7 end.
    destruct (f_cs_stack_step m6 h4 LB4 _ _ _ _ _ _ m7 lo CST6 MU7 WM7 MI7 ST7 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST7 UWK].
    pose proof (UWK UW6) as UW7. clear MU7 WM7 UWK.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST7) as (CH7 & SH7 & _ & _ & HH7).
    pose proof CH7 as CH7'. unfold A_mpi_div_mpi_C.DCS in CH7'.
    apply Forall_cons_iff in CH7'. destruct CH7' as [SPC7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [T2C7 CH7'].
    apply Forall_cons_iff in CH7'. destruct CH7' as [ZC7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [CZ7 CH7'].
    apply Forall_cons_iff in CH7'. destruct CH7' as [GAP7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [SAVE7 CH7'].
    apply Forall_cons_iff in CH7'. destruct CH7' as [FHD7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [Z32C7 CH7'].
    apply Forall_cons_iff in CH7'. destruct CH7' as [Z48C7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [Z64C7 CH7'].
    apply Forall_cons_iff in CH7'. destruct CH7' as [TPC7 CH7']. apply Forall_cons_iff in CH7'. destruct CH7' as [JQ7 _].
    cbn [fst snd] in SPC7, T2C7, ZC7, CZ7, GAP7, SAVE7, FHD7, Z32C7, Z48C7, Z64C7, TPC7, JQ7. unfold A_mpi_div_mpi_C.dv_sp in SPC7.
    unfold SHC1 in SH7. clear CH7.
    assert (GAP7k : True /\ rw_cells asegs m7 (sp1 + 216) [CB gapn gb]) by (split; [exact I| exact GAP7]). clear GAP7.
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL + 4, Z.shiftr FB 3 + al_sb AL + 4 + 1)] m7) as MU. pose proof (wmono_refl asegs m7) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    match goal with H : HM asegs R HIA h4 LB4 LF1 m8 |- _ => rename H into HH8 end.
    match goal with H : mem_inv asegs m8 |- _ => rename H into MI8 end.
    match goal with H : stk asegs m8 lo sp1 |- _ => rename H into ST8 end.
    match goal with H : rw_cells asegs m8 (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into SH8 end.
    norm_b8 SH8.
    assert (GAP8 : rw_cells asegs m8 (sp1 + 216) [CB gapn gb]).
    { eapply rw_cells_transport; [exact (proj2 GAP7k)| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from]. split; [right; clear - MB5 LOC; lia| exact I]. }
    pose proof (A_mpi_div_mpi_S_c24.rw_cells_nil_s m8 (sp1 + 184) ltac:(clear - SP1 SPR SP1R; lia)) as ZC8. clear GAP7k.
    assert (FSH8 : rw_cells asegs m8 (Z.shiftr FB 3 + al_sb AL) A_mpi_div_mpi_P.DV_FSH)
      by (unfold A_mpi_div_mpi_P.DV_FSH; cbn [zcells app]; exact SH8).
    lazymatch type of CST7 with CSTA _ _ _ ?ls ?dw ?cs _ ?vv ?ff => assert (CST8 : CSTA m8 h4 LB4 ls dw cs A_mpi_div_mpi_P.DV_FSH vv ff) end.
    { eapply (A_mpi_div_mpi_C.cs_shadow_write R HIA) with (mq := m7) (j := 4); try eassumption;
        first [ (clear; lia)
              | (intros d0 Hd0; destruct (LSA d0 Hd0) as [E|[E|[E|E]]]; rewrite E; clear - F0 F1 F2 ALO LOS SLO SP1 NEEDR; lia)
              | (unfold A_mpi_div_mpi_C.DCS; repeat (apply Forall_cons; [cbn [fst snd]; try unfold A_mpi_div_mpi_C.dv_sp; assumption|]); apply Forall_nil)
              | reflexivity ]. }
    assert (UW8 : UWCD m8) by (eapply uwcd_munch; [exact UW7| exact MU| apply Forall_cons; [cbn [snd]; clear - MB5 LOC; lia| apply Forall_nil]]).
    clear MU WM CST7. try clear SH7. try clear SH8.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (Z.sgn ?vv)] => destruct (Z.sgn_spec vv) as [(KS & ->)|[(KS & ->)|(KS & ->)]] end.
    - zstep. zstep. zstep.
      eapply C_CLEAN_X with (r := 0); [exact CST8| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| reflexivity| exact UW8| clear; lia| intros _; exact BPOS| exact HSZ4| clear - HV FIN_PHI CPB; lia| clear - HF FIN_FR; lia].
    - edestruct (A_mpi_client2.cs_w_facts asegs R HIA) with (mq := m8) as (MW8 & NSW8 & EAW8 & XWW8 & _ & _ & _ & HFW8 & _ & _ & OW8); try eassumption.
      pose proof MW8 as [(CW8 & W88 & W08 & LENW8 & NRW8 & OWN8) SGW8]. rewrite EAW8 in CW8. rewrite <- XE in CW8, OW8. unfold mpi_cells in CW8.
      destruct XWW8 as [CWW8 _]. rewrite EAW8 in CWW8. rewrite <- XE in CWW8.
      assert (XR8 : 0 <= X /\ X + 16 <= 2^64) by (rewrite XE; clear - XB16 X0q; lia).
      assert (X85 : X mod 8 = 0) by (rewrite XE; exact X8q).
      pose proof (munch_refl [(X + 8, X + 10)] m8) as MU. pose proof (wmono_refl asegs m8) as WM.
      zstep. zstep. zstep. zstep. zstep.
      if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by (clear - XR8; lia);
        [exfalso; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by lia; clear - KA X85; lia|].
      zstep. zstep. zstep. zstep. shadow_chk OW8 (X + 8) 2.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      match goal with H : HM asegs R HIA h4 LB4 LF1 m9 |- _ => rename H into HH9 end.
      match goal with H : mem_inv asegs m9 |- _ => rename H into MI9 end.
      match goal with H : stk asegs m9 lo sp1 |- _ => rename H into ST9 end.
      match goal with H : rw_cells asegs m9 X _ |- _ => rename H into CW9 end.
      set (dW9 := set_sg dW4 1).
      assert (MW9 : mpd_at asegs m9 LB4 dW9).
      { split; [| left; reflexivity]. unfold dW9, set_sg. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAW8, <- XE.
        split; [exact CW9|]. split; [exact X85|]. split; [rewrite XE; exact X0q|]. split; [exact LENW8|]. split; [exact NRW8|].
        destruct (md_own dW4) eqn:EO; [exact OWN8| | exfalso; exact (NSW8 eq_refl)].
        ddestruct OWN8 as (N18 & IN8 & P168 & UA8). split; [exact N18|]. split; [exact IN8|]. split; [exact P168|].
        ddestruct (HFW8 eq_refl) as (_ & _ & _ & _ & _ & WAP).
        eapply u32arr_transport; [exact UA8| exact MU| exact WM|]. cbn [disjoint_from]. rewrite LENW8. rewrite XE. split; [clear - WAP; lia| exact I]. }
      assert (HPA9 : presA asegs R LB4 LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA h4) [(md_addr dX, md_addr dX + 16)] m8 m9).
      { eapply presA_weaken with (LB := LB4) (LF := LF1) (SP := sp1) (SSP := arl_stklo R) (TOP := hstkhi asegs R HIA h4) (W := [(X + 8, X + 10)]);
          [| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx K; cbn [outside] in *; rewrite <- XE in K; clear - K; lia].
        eapply (presA_of_munch asegs R LB4 LF1 _ _ _ _ m8 m9 (hcs asegs R HIA h4) CSOK4); [| intros c0' Hc; eapply cshd_hcs; [exact HH9| | exact Hc]; clear; lia| exact MU| exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OW8)| clear; lia| clear; lia]| apply Forall_nil]. }
      lazymatch type of CST8 with CSTA _ _ _ ?ls _ ?cs ?sh ?vv ?ff => assert (CST9 : CSTA m9 h4 LB4 ls dW9 cs sh vv ff) end.
      { eapply (A_mpi_client2.cs_upd_w asegs R HIA) with (mq := m8); try eassumption; try reflexivity. }
      assert (UW9 : UWCD m9).
      { destruct UWX as [[XS _]|CAP]; [| apply uwc_cap; clear - CAP; lia].
        eapply uwcd_munch; [exact UW8| exact MU|]. apply Forall_cons; [cbn [snd]; rewrite XE; clear - XS LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
      zstep.
      eapply C_CLEAN_X with (r := 0); [exact CST9| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| reflexivity| exact UW9| clear; lia| intros _; exact BPOS| exact HSZ4| clear - HV FIN_PHI CPB; lia| clear - HF FIN_FR; lia].
    - zstep. zstep. zstep.
      eapply C_CLEAN_X with (r := 0); [exact CST8| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| reflexivity| exact UW8| clear; lia| intros _; exact BPOS| exact HSZ4| clear - HV FIN_PHI CPB; lia| clear - HF FIN_FR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY SHR CMPR UWX SXA IA2 ESA slo SLO1 SLO2 SSH0 FIN_PHI FIN_FR"] Lemma dv_FIN_ok : A_mpi_div_mpi_M_c24.dvFIN_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn PF FF.
  Proof. unfold A_mpi_div_mpi_M_c24.dvFIN_stmt. exact dv_FIN. Qed.

  End Fr.
  End Call.
End WalkF.
