(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_div_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_shift_r A_mpi_lset_ng A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24.
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

Section WalkM.
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
  Local Notation CZC czpad := [C8 (Z_to_bv 64 (FB + 64)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 1); C4 czpad].
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

  Hypothesis COPYX : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis IA2 : md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) -> img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis IB2 : md_own dB = LStatic -> (forall i, 0 <= i < 4 * md_n dB -> ro_addr asegs (wa (md_p dB + i)) = true) -> img_norz (md_p dB) (4 * md_n dB) = true.
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Hypothesis ESB : In dB es.
  (* [comment removed for export] *)
  Variables (PHIr FRr : Z).
  Hypothesis PHIR0 : 4 * AVOL_CALL <= PHIr.
  Hypothesis FRR0 : 4 * fr_charge (d + 1) <= FRr.
  Definition dvV6 : Z := grow_PHI (md_n dA + 1) + PHIr.                               (* [comment removed for export] *)
  Definition dvV5 : Z := grow_PHI (md_n dA + 1) + grow_PHI (md_n dB + 1) + dvV6.      (* [comment removed for export] *)
  Definition dvV4 : Z := grow_PHI (md_n dA + 2) + dvV5.                               (* [comment removed for export] *)
  Definition dvV2 : Z := copy_PHI dB + dvV4.                                          (* [comment removed for export] *)
  Definition dvV1 : Z := copy_PHI dA + dvV2.                                          (* [comment removed for export] *)
  Definition dvF6 : Z := shift_l_FR + FRr.
  Definition dvF5 : Z := 2 * shift_l_FR + dvF6.
  Definition dvF4 : Z := grow_FR (d + 1) + dvF5.
  Definition dvF3 : Z := fr_charge (d + 1) + dvF4.                                    (* [comment removed for export] *)
  Definition dvF2 : Z := copy_FR 0 + dvF3.
  Definition dvF1 : Z := copy_FR 0 + dvF2.
  Hypothesis BM_PHI : dvV1 <= PHIb.
  Hypothesis BM_FR : dvF1 <= FRb.
  Hypothesis NA0 : 0 <= md_n dA.
  Hypothesis NB0 : 0 <= md_n dB.

  Ltac unfold_bud := unfold dvV1, dvV2, dvV4, dvV5, dvV6, dvF1, dvF2, dvF3, dvF4, dvF5, dvF6, copy_PHI, grow_PHI, copy_FR, grow_FR, shift_l_FR, calls_FR, fr_charge in *; unfold AVOL_CALL in *.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L15320239295.2L36221617068.5L42090684140.6L59314923118.300000600L00a00iS1r2HRS4PHIb4PHIr5PHIR01v2HVS1d3FRb3FRr4FRR01f2HFS1r2HR1K". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF PHIR0 FRR0"] Lemma dv_ERR : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq v f (r : Z)
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    cells_size czc = 16%nat ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    UWCD mq -> -2^31 < r < 0 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f8b4) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST SZC EAX EAY EAZ EAD UW HR HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    zstep.
    eapply C_CLEAN_X with (r := r); [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact SZC| exact UW| clear - HR; lia| intros K; exfalso; clear - K HR; lia| unfold div_mpi_nz; apply Z.le_max_l| |].
    - clear - HV PHIR0. lia.
    - clear - HF FRR0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L11471117368.119L24928467151.122L33041182163.121L50754888306.121L52972366418.121L59314955108.121L6663987453.121 00000W01@01h02N03803b04HS2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'3HN'S2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'2Z02N1S2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'1T2N1S2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'2LRS2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'3HN'2NES2LF2ra2sp3LFB2FB3sp14gapn2d02dS2d'3POS2LRS2LF2ra2sp3LFB2FB3sp14gapn2dS2d'2HN2N1". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma copy_local_factsA : forall mq LB0 LB1 d0 dS d', mpd_at asegs mq LB1 d' -> (md_sg dS = 1 \/ md_sg dS = -1) -> md_own d' <> LStatic ->
    md_own d0 = LNull -> md_n d0 = 0 ->
    copy_R dS d0 LB0 0 d' -> copy_trim dS d0 d' -> 0 < mpd_abs dS ->
    mpd_abs d' = mpd_abs dS /\ 1 <= md_n d' <= md_n dS /\ md_own d' = LHeap /\ (md_n d' = 1 \/ 2 ^ (32 * (md_n d' - 1)) <= mpd_abs dS)
    /\ mpd_abs dS < 2 ^ (32 * md_n d').
  Proof.
    intros mq LB0 LB1 d0 dS d' MD SGS NS ON N0 [CR _] TR POS.
    destruct CR as [(_ & HV & HN)|(C & _)]; [| discriminate C].
    pose proof MD as [(_ & _ & _ & HL & HN' & HO) SG].
    assert (AB : mpd_abs d' = mpd_abs dS) by (rewrite <- (mpd_val_abs d' SG), <- (mpd_val_abs dS SGS), HV; reflexivity).
    pose proof (mpd_abs_lval d' HL) as AL'. pose proof (lval_range (md_limbs d') (md_n d') ltac:(lia)) as LR.
    assert (N1 : 1 <= md_n d').
    { destruct (Z.eq_dec (md_n d') 0) as [E|NE]; [| lia]. exfalso. rewrite <- AL', AB, E in LR. change (2 ^ (32 * 0)) with 1 in LR. lia. }
    split; [exact AB|]. split; [rewrite N0 in HN; lia|]. split.
    - destruct (md_own d') eqn:O; [destruct HO as [_ Z0]; lia| reflexivity| exfalso; exact (NS eq_refl)].
    - split; [| rewrite <- AB, AL'; lia]. unfold copy_trim in TR. rewrite N0 in TR. destruct TR as [T|[T|T]]; [lia| left; exact T| right; exact T].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L23078657479.114L28202256178.115L30985783986.114L53563543623.11500000U01:01Y028S2LF2ra2sp3LFB2FB3sp14gapn2A02n01x2HxS2LF2ra2sp3LFB2FB3sp14gapn2P02k01x2HxS2LF2ra2sp3LFB2FB3sp14gapn2A01xS2LF2ra2sp3LFB2FB3sp14gapn2P01x". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma wr_ro_apart : forall mx A0 n0 P0 k0, mem_inv asegs mx -> wr_at asegs mx A0 n0 -> 0 <= P0 -> P0 + k0 <= 2^64 ->
    (forall i, 0 <= i < k0 -> ro_addr asegs (wa (P0 + i)) = true) -> 0 < n0 -> 0 < k0 -> A0 + n0 <= P0 \/ P0 + k0 <= A0.
  Proof.
    (intros mx A0 n0 P0 k0 MI dd_H; ddestruct dd_H as (W0 & W1 & WV); intros HP0 HP1 RO Hn Hk).
    apply (apart_by_pred (fun x => ro_addr asegs (wa x) = false) A0 n0 P0 k0); [| | exact Hn| exact Hk].
    - intros x Hx. specialize (WV (x - A0) ltac:(lia)). replace (A0 + (x - A0)) with x in WV by lia.
      destruct (mx (wa x)) eqn:E; [exact (MI _ _ E)| exact (wview_not_ro asegs mx _ WV E)].
    - intros x Hx K. specialize (RO (x - P0) ltac:(lia)). replace (P0 + (x - P0)) with x in RO by lia. congruence.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L19980016842.7 L39280637297.0 L41650118032.6 L464615526.10  L49037504437.6 L52101693566.17L62037211595.7 L6203936179.1  L65159210099.9 L66151427842.16L9356559676.11 L9838743115.2  00000H00I00]01=01R02N02i02n03M03i04T04^S1R3HIA1h2sp3TOP3sp13SP1SS1R2FB2dl3DLF3ALO2F1S1R3HIA1h4PHIb3BUD2hq1v1e2HV3HVqS1R2sp2lo3SLO3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2dl3DLF3ALO2F11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R3HIA1h3FRb4BUDF2hq1f2HF4HFRqS3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF C24H COPYX"] Lemma call_copy_l : forall mq hq LBq ls CS0 v f i dl e (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> length ls = 4%nat -> nth_error ls i = Some dl -> md_addr dl + 16 <= FB + 256 ->
    mpd_at asegs mq LBq e -> aobj asegs AL (hcs asegs R HIA hq) mq (md_addr e) 16 ->
    client_range L (LBq ++ fdata LF1) lo (md_addr e) 16 -> (md_own e = LHeap -> client_range L (LBq ++ fdata LF1) lo (md_p e) (4 * md_n e)) ->
    mpd_sep dl e -> copy_sep dl e lo sp1 -> (md_own e = LStatic -> img_norz (md_p e) (4 * md_n e) = true) ->
    UWCD mq -> v + copy_PHI e <= PHIb -> f + copy_FR 0 <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr dl) -> a1v = Z_to_bv 64 (md_addr e) ->
    (forall m3 h3 LB3 dl' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls dl') dX CS0 DV_FSH (v + copy_PHI e) (f + copy_FR 0) -> copy_Rx e dl LBq r dl' -> mpd_at asegs m3 LB3 dl' -> md_addr dl' = md_addr dl -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_COPY) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST LSL NTH DLF ME OE CRE CREL SEP CSEP IE UW HV HF RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := i) (d := dl) as (ML & NSL & XWL & _ & _ & _ & _ & _ & _ & _ & OL); try eassumption.
    pose proof COPYX as CPY. unfold mpi_copy_stmtA_x_c, mpi_copy_stmtA_gen_c, A_MPI_COPY in CPY. unfold A_MPI_COPY.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CPY with (h := hq) (LB := LBq) (LF := LF1) (dX := dl) (dY := e) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact ML | exact NSL | exact ME | exact SEP | exact CSEP | exact CRE | exact CREL | exact XWL | exact STq | exact LOS | exact MIq | exact TPV | exact OL | exact OE | exact IE | exact RPE | reflexivity
              | lazymatch goal with
                | |- lo <= sp1 - 112 - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD HV; lia
                | |- uw_obj _ _ 16 0 => left; split; [clear - DLF F1 ALO; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dl3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    pose proof RR3 as [(RV & EA3 & PD3 & FRP3) _].
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls dl3) dX CS0 DV_FSH (v + copy_PHI e) (f + copy_FR 0)).
    { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := i) (dX := dl) (mq := mq) (hq := hq); try eassumption. }
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DLF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L25359054107.2L26983617546.4L38948636245.0L52394196865.5L62643686019.3L9216278189.2 00000600A00B00R00\00bS1e2P0S1e2E01a2HaSS2sp3sp13SP11e1KS1e2dl3LE1S1e2N1". (* [comment removed for export] *)
  #[using="NEEDR ra LOS SLO TOP LFB XW gapn SP1 FRSH ESF LOC CSP FN64"] Lemma src_ext : forall mq hq LBq ls dW CS0 v f e i dl, CSTA mq hq LBq ls dW CS0 DV_FSH v f -> In e es -> nth_error ls i = Some dl -> md_own dl = LNull ->
    opnd_sep dX e lo (bv_unsigned sp) ->
    (md_own e = LStatic -> (forall i, 0 <= i < 4 * md_n e -> ro_addr asegs (wa (md_p e + i)) = true) -> img_norz (md_p e) (4 * md_n e) = true) ->
    mpd_at asegs mq LBq e /\ aobj asegs AL (hcs asegs R HIA hq) mq (md_addr e) 16
    /\ client_range L (LBq ++ fdata LF1) lo (md_addr e) 16 /\ (md_own e = LHeap -> client_range L (LBq ++ fdata LF1) lo (md_p e) (4 * md_n e))
    /\ mpd_sep dl e /\ copy_sep dl e lo sp1 /\ (md_own e = LStatic -> img_norz (md_p e) (4 * md_n e) = true).
  Proof.
    intros mq hq LBq ls dW CS0 v f e i dl CST He NTH ONL OE IE.
    edestruct (A_mpi_client2.cs_ext_facts asegs R HIA) with (e := e) as (ME & OEs & CRE & CREL & HFE & ASE & EFB); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := i) (d := dl) as (ML & _ & _ & _ & _ & _ & _ & SLOC & _); try eassumption.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (_ & _ & MIq & _ & HHq).
    edestruct (A_mpi_client2.loc_vs_ext asegs R HIA) with (e := e) (A := md_addr dl) as [LE1 LE2]; try eassumption.
    dpose OE as (_ & _ & _ & OE4 & OE5). pose proof ME as [(CEc & _ & E0 & LENE & NRE & OWE) _].
    split; [exact ME|]. split; [exact OEs|]. split; [exact CRE|]. split; [exact CREL|].
    split; [right; clear - LE1; lia|]. split.
    - split; [| split; [intros K; rewrite ONL in K; discriminate K| split; [right; left; rewrite ONL; discriminate|
        split; [destruct OE4 as [K|K]; [left; exact K| right; clear - K SP1; lia]| split; [intros NN; destruct (OE5 NN) as [K|K]; [left; exact K| right; clear - K SP1; lia]| intros a Ha; clear - Ha E0; lia]]]]].
      intros NN. destruct (md_own e) eqn:EO; [exfalso; exact (NN eq_refl)| destruct (LE2 eq_refl) as [K|K]; [right; exact K| left; exact K]|].
      ddestruct OWE as (N1 & _ & P0 & BY & RO). pose proof ML as [(CLc & _) _]. destruct CLc as [_ WR]. cbn [cells_size csize Nat.add mpi_cells] in WR.
      pose proof (u32ro_bound _ _ _ _ BY) as [_ PB]. rewrite LENE in PB.
      exact (wr_ro_apart mq (md_addr dl) 16 (md_p e) (4 * md_n e) MIq WR ltac:(clear - P0; lia) PB RO ltac:(clear; lia) ltac:(clear - N1; lia)).
    - intros EO. apply (IE EO). rewrite EO in OWE. exact (proj2 (proj2 (proj2 (proj2 OWE)))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26983617546.4L27867584496.3L44150806992.500000=00H00YS2dW3X0q1a2HaS2dX2dl3LVWS2sp2dX3sp13SP11K". (* [comment removed for export] *)
  #[using="NEEDR ra LOS SLO TOP LFB XW W0AS gapn SP1 FRSH LOC CSP FN64"] Lemma src_w : forall mq hq LBq ls dW CS0 v f i dl, CSTA mq hq LBq ls dW CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_own dl = LNull ->
    mpd_at asegs mq LBq dW /\ aobj asegs AL (hcs asegs R HIA hq) mq (md_addr dW) 16
    /\ client_range L (LBq ++ fdata LF1) lo (md_addr dW) 16 /\ (md_own dW = LHeap -> client_range L (LBq ++ fdata LF1) lo (md_p dW) (4 * md_n dW))
    /\ mpd_sep dl dW /\ copy_sep dl dW lo sp1 /\ (md_own dW = LStatic -> img_norz (md_p dW) (4 * md_n dW) = true).
  Proof.
    intros mq hq LBq ls dW CS0 v f i dl CST NTH ONL.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWq & NSW & EAW & _ & XLSq & CRWq & CRWLq & HFW & ASW & WFB & OWq); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := i) (d := dl) as (ML & _ & _ & _ & _ & _ & _ & SLOC & _); try eassumption.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (_ & _ & MIq & _ & HHq).
    pose proof (A_mpi_client2.loc_vs_w asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW W0AS (md_addr dl) SLOC) as LVW.
    pose proof MWq as [(_ & _ & X0q & _) _].
    split; [exact MWq|]. split; [rewrite EAW; exact OWq|]. split; [rewrite EAW; exact CRWq|]. split; [exact CRWLq|].
    split; [right; rewrite EAW; clear - LVW; lia|]. split; [| intros EO; exfalso; exact (NSW EO)].
    split; [| split; [intros K; rewrite ONL in K; discriminate K| split; [right; left; rewrite ONL; discriminate|
      split; [rewrite EAW; destruct ASW as [K|K]; [left; exact K| right; clear - K SP1; lia]| split; [exact XLSq| intros a Ha; clear - Ha X0q; lia]]]]].
    intros NN. destruct (md_own dW) eqn:EO; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSW eq_refl)].
    ddestruct (HFW eq_refl) as (_ & _ & IN & _).
    destruct (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dl) _ _ HHq IN SLOC) as [K|K]; [right; exact K| left; exact K].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition lfacts (dS d' : mpd) : Prop :=
    mpd_abs d' = mpd_abs dS /\ 1 <= md_n d' <= md_n dS /\ md_own d' = LHeap /\ (md_n d' = 1 \/ 2 ^ (32 * (md_n d' - 1)) <= mpd_abs dS)
    /\ mpd_abs dS < 2 ^ (32 * md_n d').

  (* [comment removed for export] *)
  Definition dvM2_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    lfacts dA dLX -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> v + dvV2 <= PHIb -> f + dvF2 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f6a4) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0@D35300034347.212D60189065437.212L10933838098.12 L11144352574.3  L13884980141.12 L1835983057.4   L22369917295.8  L23147748781.12 L23792326817.0  L26985680806.1  L27588716945.2  L28632618922.2  L29956516996.0  L31145622673.2  L31813175040.4  L34080941563.2  L34285487197.7  L35663928186.7  L37960732589.12 L38259954321.2  L45657748817.2  L4599314767.6   L48700858022.1  L53577728712.1  L55815189670.1  L57317554718.5  L57652312495.1  L57698627611.2  L59314923118.4  L59975262609.2  L60098763854.3  L63073555870.4  L66962555329.1  L8603426141.5   L9356559676.11  P27590552406.213P28627113325.213P31146933846.213P38261788758.213P45659584406.213P57713046236.213P59963990870.213Q11968186855.213Q12388912010.209Q16827575549.213Q20537614359.209Q25954107624.213Q28465177121.210Q3375676648.213 Q3421936230.212 Q45057547415.213Q5265442331.211 Q57228775306.212Q58205651829.213Q60189065437.213Q68235297648.21200001<02H02M02Y03B03R04404]04^04c04d04e04f04g05705A05]06206[06\06]07307807=07B07V07Z07[07f07g08108?08D08U09@0:D0;H0<L0=P0>T0?=0@A0AE0A]0A^0B90B:0BS0BT0C@0CA0C[0DD0DE0E?0EaS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS3sp1S2sp3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2dA2dB4BPOS3BLES2dA2dB4PHIb4PHIr5PHIR03NA03NB02B1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1SS3sp1FFSFS2dA2dB4BPOS3BLES3sp14gapnS2dA2dB4PHIb4PHIr3NA03NB02B1S1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FFS1d3FRb2D03FRr4FRR02B1S3sp1S3sp1S3sp1S2dA2dB4PHIb4PHIr2B1S2FBFS2dX2dA1E1KFS1R2lo3LOSS1d3FRb3FRr2B1S3sp1S1d3FRb2D03FRr2B1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R2LF2sp3LFB3sp14gapn3SP12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCFS2LF2sp2lo3LFB3sp14gapn3SP1FS2LF3LFB3sp14gapn4SP1R2HBFS1R2LF2sp2lo3LFB3sp14gapn3SP12HB5Ha_st5Hl_stFS2LF3LFB3sp14gapn2HB5Ha_stS1R2LF2lo3LFB3sp14gapn3LOC2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP12HB5Ha_st5Hl_stS1R2LF3LFB3sp14gapn2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SXA IA2 ESA PHIR0 FRR0 BM_PHI BM_FR NA0 NB0 OA"] Lemma dv_MAIN : dvM2_stmt ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 (Z_to_bv 64 X) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 0) (Z_to_bv 64 FB))
              (T2C t2pad) [] (CZC czpad) gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB -> mpd_abs dB <= mpd_abs dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f690) fc None mq (seg_rom asegs)).
  Proof.
    intros K2. intros until t6. intros CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 UW BPOS BLE. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as OKq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'.
    apply Forall_cons_iff in CHq'. destruct CHq' as [SPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [T2Cq CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [ZCq CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [CZq CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z32C CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z48C CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [Z64C CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [TPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [JQC _].
    cbn [fst snd] in SPC, T2Cq, ZCq, CZq, GAPC, SAVE, FHD, Z32C, Z48C, Z64C, TPC, JQC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    pose proof (munch_refl [(sp1, sp1 + 152)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH 0 0).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity ..]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM SPC T2Cq ZCq CZq GAPC SAVE FHD Z32C Z48C Z64C TPC JQC.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    assert (SRC : mpd_at asegs m2 LBq dA /\ aobj asegs AL (hcs asegs R HIA hq) m2 (md_addr dA) 16
                  /\ client_range L (LBq ++ fdata LF1) lo (md_addr dA) 16 /\ (md_own dA = LHeap -> client_range L (LBq ++ fdata LF1) lo (md_p dA) (4 * md_n dA))
                  /\ mpd_sep dLX dA /\ copy_sep dLX dA lo sp1 /\ (md_own dA = LStatic -> img_norz (md_p dA) (4 * md_n dA) = true)).
    { destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
      - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
        rewrite EQA. eapply src_w with (i := 0%nat); [exact CST2| reflexivity| exact OX0].
      - eapply src_ext with (i := 0%nat); [exact CST2| exact (ESA NE)| reflexivity| exact OX0| exact OA| exact IA2]. }
    ddestruct SRC as (MA2 & OA2 & CRA & CRAL & SEPA & CSEPA & IMA).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m2) (i := 0%nat) (d := dLX) as ([(_ & _ & _ & _ & _ & OWL) _] & _); try eassumption; [reflexivity|]. rewrite OX0 in OWL. destruct OWL as [_ ON0].
    eapply (call_copy_l m2 hq LBq [dLX; dY; dZ; dT] _ 0 0 0%nat dLX dA 0x9f6a0); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite AE; reflexivity).
    - rewrite EAX. clear. lia.
    - pose proof BM_PHI as B1. unfold_bud. clear - B1 NA0 NB0 PHIR0. lia.
    - pose proof BM_FR as B1. unfold_bud. clear - B1 D0 FRR0. lia.
    - clear. lia.
    - intros m3 h3 LB3 dl' r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      pose proof RR3 as [(RV & EA3 & _) TRIM].
      unfold dvM2_stmt in K2.
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      pose proof MA2 as [(_ & _ & _ & _ & _ & _) SGA].
      destruct RV as [(-> & _)|(-> & _)].
      + (* [comment removed for export] *)
        zstep.
        eapply K2; [exact CST3| rewrite EA3; exact EAX| exact EAY| exact EAZ| exact EAD| | exact OY0| exact OZ0| exact OT0| exact UW3| clear - BPOS BLE; lia| |].
        * unfold lfacts. eapply (copy_local_factsA m3 LBq LB3 dLX dA dl'); [exact ML3| exact SGA| | exact OX0| exact ON0| exact (proj1 RR3)| exact (TRIM eq_refl)| clear - BPOS BLE; lia].
          edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 0%nat) (d := dl') as (_ & NS' & _); try eassumption; try reflexivity.
        * pose proof BM_PHI as B1. unfold_bud. clear - B1. lia.
        * pose proof BM_FR as B1. unfold_bud. clear - B1. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| rewrite EA3; exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * pose proof BM_PHI as B1. unfold_bud. clear - B1 NA0 NB0. lia.
        * pose proof BM_FR as B1. unfold_bud. clear - B1 D0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvM3_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    lfacts dA dLX -> lfacts dB dY -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> v + dvV4 <= PHIb -> f + dvF3 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f6b4) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L13655593885.5L14348534914.6L1921887436.7 L21800167073.0L29956516996.0L30780105986.8L31720098237.6L32121109934.3L58500857548.9L9018141615.1 00000@00S00k00l00m01K01a01l02P02TS1d3FRb3FRr1f2HFS1d3FRb2D03FRr1f2HFS1d3FRb2D03FRr4FRR01f2HFSSS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA2dB4PHIb4PHIr1v2HVS2dA2dB3VABS2dA2dB4PHIb4PHIr5PHIR03NA03NB01v2HVS2FB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB BE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX IB2 ESB PHIR0 FRR0 NA0 NB0 OB"] Lemma dv_M2 : dvM3_stmt -> dvM2_stmt.
  Proof.
    intros K3. unfold dvM2_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX OY0 OZ0 OT0 UW VAB HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    destruct (src_ext mq hq LBq _ _ _ _ _ dB 1%nat dY CST ESB eq_refl OY0 OB IB2) as (MB2 & OB2 & CRB & CRBL & SEPB & CSEPB & IMB).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as ([(_ & _ & _ & _ & _ & OWL) _] & _); try eassumption; [reflexivity|]. rewrite OY0 in OWL. destruct OWL as [_ ON0].
    eapply (call_copy_l mq hq LBq [dLX; dY; dZ; dT] _ v f 1%nat dY dB 0x9f6b0); try eassumption; try reflexivity; try (rewrite EAY; reflexivity); try (rewrite BE; reflexivity).
    - rewrite EAY. clear. lia.
    - clear - HV NA0 NB0 PHIR0. unfold_bud. lia.
    - clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dl' r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      pose proof RR3 as [(RV & EA3 & _) TRIM]. unfold dvM3_stmt in K3.
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      pose proof MB2 as [_ SGB].
      destruct RV as [(-> & _)|(-> & _)].
      + zstep.
        eapply K3; [exact CST3| exact EAX| rewrite EA3; exact EAY| exact EAZ| exact EAD| exact LFX| | exact OZ0| exact OT0| exact UW3| exact VAB| |].
        * unfold lfacts. eapply (copy_local_factsA m3 LBq LB3 dY dB dl'); [exact ML3| exact SGB| | exact OY0| exact ON0| exact (proj1 RR3)| exact (TRIM eq_refl)| clear - VAB; lia].
          edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 1%nat) (d := dl') as (_ & NS' & _); try eassumption; try reflexivity.
        * clear - HV. unfold_bud. lia.
        * clear - HF. unfold_bud. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| rewrite EA3; exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * clear - HV NA0 NB0. unfold_bud. lia.
        * clear - HF D0. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L16980291777.9L24428689831.4L27309460134.3L35663928186.7L56427931802.3L58329842742.1L60098763854.3L62018535662.100000Q00^00h01=01G01K01U01XS1R5NEEDR2sp2lo3SLO3sp13SP12dl2K1S2sp2lo2dl2K2S2FB2dl2K1S1R3HIA1h2sp2lo3TOP1HS2FB2dl2K2S2dlS1R2lo3LOSS1R". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO TOP LFB HNDk DIMG H0M XW W0AS gapn SP1 F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma sign_store_l : forall mq hq LBq ls dW CS0 v f i dl m2,
    CSTA mq hq LBq ls dW CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_own dl = LHeap ->
    HM asegs R HIA hq LBq LF1 m2 -> munch [(md_addr dl + 8, md_addr dl + 10)] mq m2 -> wmono asegs mq m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 ->
    rw_cells asegs m2 (md_addr dl) (mpi_cells (md_p dl) (Z_to_bv 64 1) (md_n dl) (md_pad dl)) ->
    u32arr asegs m2 (md_p dl) (md_limbs dl) ->
    CSTA m2 hq LBq (set_nth i ls (set_sg dl 1)) dW CS0 DV_FSH v f.
  Proof.
    intros mq hq LBq ls dW CS0 v f i dl m2 CST NTH OH HH2 MU WM MI2 ST2 CL2 UA2. rt_facts.
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := dl) as (ML & NSL & _ & _ & _ & _ & _ & SLOC & _); try eassumption.
    pose proof ML as [(_ & A8 & A0 & LEN & NR & OWN) _]. rewrite OH in OWN. ddestruct OWN as (N1 & IN & P16 & _).
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_addr dl + 8, md_addr dl + 10)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      destruct SLOC as [[K1 K2]|[K1 K2]]; [eapply crange_sub; [exact CFBq| clear - K1; lia| clear - K2; lia]| eapply crange_sub; [exact SCSq| clear - K1 SP1 SLO NEEDR; lia| clear - K2; lia]]. }
    eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dl) (WX := [(md_addr dl + 8, md_addr dl + 10)]); try eassumption; try reflexivity.
    - apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear. lia.
    - split; [| left; reflexivity]. cbn [set_sg md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CL2|]. split; [exact A8|]. split; [exact A0|]. split; [exact LEN|]. split; [exact NR|]. rewrite OH. split; [exact N1|]. split; [exact IN|]. split; [exact P16| exact UA2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L29956516996.0L36221617068.5L42090684140.6L59314923118.100000100G00\00_SS4PHIb4PHIr5PHIR01v2HVS1d3FRb3FRr4FRR01f2HFS1K". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF PHIR0 FRR0"] Lemma dv_ERR16 : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq v f
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    cells_size czc = 16%nat ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    UWCD mq -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f8b8) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST SZC EAX EAY EAZ EAD UW HV HF.
    eapply C_CLEAN_X with (r := -16); [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact SZC| exact UW| clear; lia| intros K; exfalso; clear - K; lia| unfold div_mpi_nz; apply Z.le_max_l| |].
    - clear - HV PHIR0. lia.
    - clear - HF FRR0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvM4_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 SHA10 (Z_to_bv 64 (A + 10)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV4 <= PHIb -> f + dvF4 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f760) fc None mq (seg_rom asegs)).

  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.

  Local Ltac2 Set LiaOrc.tbl := fun () => "03J0@D22707591200.226D35300034347.277D35300034347.278D35300034347.279D35617972959.322D35617972959.323D43032252960.238D50215630175.238D52337554464.238D58291685769.322D60189065437.277D60189065437.278D60189065437.279D62011970312.238D64100766559.226D7045485138.323 K12690573793.226K12690573793.238K45774582958.238L10933838098.12 L11144352574.3  L12267821285.1  L12469921329.0  L12694265486.2  L13655593885.5  L13884980141.12 L14348534914.6  L14447004729.1  L1685717371.0   L18320580243.8  L18363988631.13 L18366171437.14 L19980016842.7  L20028099350.4  L21441596609.1  L22317299610.229L23147748781.12 L23461302570.256L23500973377.0  L23539585209.2  L23919512294.1  L24982576641.253L25950722970.219L26232954963.3  L26985680806.1  L27019463589.2  L27588716945.2  L27954469902.3  L28632618922.2  L28814038272.252L29784415085.259L30157387091.6  L31145622673.2  L31303280872.1  L31811139895.2  L32418217581.2  L33513311607.10 L34080941563.2  L34616251577.6  L35663928186.7  L37960732589.12 L38259954321.2  L38325499858.13 L38327596498.16 L3888524627.11  L38968870582.7  L3925383176.2   L39259851285.12 L39261862319.13 L39261961171.15 L40149296407.303L42003528019.2  L43677756009.253L43677759120.256L44203402846.2  L45657748817.2  L45777250370.2  L46190619535.310L46756382136.309L48700858022.1  L49032088014.219L4935003471.2   L50572132238.2  L52806978339.3  L52860930961.2  L53529584078.229L53577728712.1  L5546550544.311 L55815189670.1  L56119133011.11 L57444257313.2  L57698627611.2  L58788176546.11 L58790367512.11 L59308630368.3  L59308631146.3  L59308632045.3  L59308633593.3  L59314923118.4  L59321342608.4  L59975262609.2  L60098763854.3  L62018535662.1  L62037211595.7  L6203936179.1   L62827215885.1  L63950727862.8  L64274430384.11 L64703390219.10 L64705450417.11 L64810416763.268L66151427842.16 L66382967200.1  L66962555329.1  L67140007708.268L67140007708.311L67482132013.2  L68561933542.1  L6865408111.310 L82580787.4     L8931608776.1   L9175014120.1   L9356559676.11  L9373133312.11  L9414061457.2   L9838743115.2   P27590552406.278P27590552406.279P27967082900.322P27967082900.323P28627113325.278P28627113325.279P31146933846.278P31146933846.279P32425075329.277P32425075329.278P32425075329.279P38261788758.278P38261788758.279P44196848793.278P45659584406.278P45659584406.279P52851231062.277P52851231062.278P52851231062.279P57432086862.277P57432086862.278P57432086862.279P57713046236.278P57713046236.279P59963990870.278P59963990870.279P9427955542.277 P9427955542.278 P9427955542.279 Q11801279589.226Q11801279589.238Q11801279589.322Q11801279589.323Q12388912010.257Q15020413740.319Q15022643857.275Q1586404213.322 Q15911142064.321Q17356582774.261Q18397797912.262Q19056309629.262Q20537614359.257Q22869019191.234Q24840800258.318Q25513505925.321Q25513505925.322Q27174574993.237Q28094326786.274Q28465177121.275Q28465177121.276Q28660317734.234Q28937031854.320Q3421936230.277 Q3421936230.278 Q34678707061.319Q38967165855.318Q39212284437.262Q44927457335.223Q45987633792.274Q47463500689.227Q47465447825.226Q48222134583.224Q49698585326.225Q49698585326.236Q49698585326.320Q49698585326.321Q52015217567.274Q5265442331.276 Q5265442331.277 Q52737337382.223Q52744951088.226Q52744951088.237Q52747231024.227Q57228775306.277Q57228775306.278Q58024304817.319Q58026535180.275Q60085332156.259Q60511567613.262Q63565942191.261Q63566517848.259Q63566565718.262Q64470851025.319Q64471111904.274Q67302478109.274Q68235297648.277Q68235297648.278Q68235297648.279Q68534218551.235Q6996841533.274 Q6997102860.319 Q9538458057.259 00000`02B03d05F07B09>09?09o0:_0<T0>60?X0A:0Al0B\0DQ0E@0Eo0F^0Fc0Fo0G30G40G50GE0Gn0HA0HF0HG0He0Hf0Hg0I?0IQ0IV0J70J`0KM0KN0KU0KY0L?0L`0Ll0M10M80M90M:0M;0Me0NK0N^0N_0Nc0Nj0Nk0Nl0O60OL0Oa0PJ0PK0Q80Q90Qb0R=0RF0RG0RH0S?0T40T;0Te0UO0UP0UQ0UR0VJ0Wf0Wk0XL0XS0XZ0Xd0Xe0YF0YK0ZC0ZH0[10[20[30[40[M0[W0[a0[j0\50\@0\A0\B0\L0\O0\j0\o0]30]Q0]Z0][0]b0^R0^n0_30_80_a0`Y0``0`d0a\0ak0b00b40b_0bi0bj0c40dG0eX0g90h\0io0k@0lS0md0o:10P11d13714H14I15\16m18@19S1:d1<:1=P1>d1?\1@P1Ac1C41DG1EZ1Fk1GU1H?1I;1J41JV1KJ1L21M21N51NN1Nk1OD1Oi1P@1Q41R:1S=1Sc1TK1U11UW1Un1V`1W[1XR1YD1Z51ZN1Ze1[J1\01\V1]31]S1^31^f1_Y1`>1`e1aL1ac1bI1bo1cU1dM1eA1f21fW1g01gG1g`1h91hR1iC1ih1jP1kA1l01l]1m:1mb1nV1nmS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z02HB5Ha_st5Hl_stS1R3HIA1h2LB2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3LBq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z04C24q2An2h43HT43FA02HB5Ha_st5Hl_stS1R3HIA1h2LB2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3LBq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z04C24q2An2h43HT43FA02HB5Ha_st5Hl_stFS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13LBq3dLX2dY2dZ3SPR2F04SP1R3ARv2Z04C24q2An3FA02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3SPR2F04SP1R3ARv2Z02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3SPR2F04SP1R3ARv2Z02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3SPR2F04SP1R3ARv2Z02HB5Ha_st5Hl_stS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13LBq3dLX2dY2dZ3SPR2F04SP1R3ARv2Z04C24q2An3FA02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENY3PYF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENY3PYF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENX3PXF2HB5Ha_st5Hl_stS3sp1S2sp3sp13SP1S2dAFFS1d3FRb3FRr1f2HFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1d3FRb2D03FRr1f2HFS3sp1SS2dA2dB4PHIb4PHIr3NA03NB01v2HVFFS1R3HIA1h2sp3TOP3sp13SP1S2LB4C24H3LBq4C24qS3sp1S2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LF2ra2sp1A3LFB2dA2FB3sp14gapn3NA03dLX2dY2NASS2dA2NAS2FBS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dYS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2dA2NA4NA98S3sp1S2dA2NAFFFS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY3ARvS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dYS1d3FRb2D03FRr1f2HFFS2FBS2dA2E0FFS3sp14gapnS2dA2dB4PHIb4PHIr1v2HVS1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1R3HIA1h1d3FRb2D04BUDF3FRr4FRR02hq1f2HF4HFRqFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3SLO3sp13SP1S2dA4NA98FFS1R3HIA1h2dA2dB4PHIb3BUD4PHIr5PHIR03NA03NB02hq1v2HV3HVqS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24qS2dA2KLS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY3ARvS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY3ARvFFFS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS1R2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ3ACV3SPR2F04SP1R2NX3ARv2Z04C24q2An3FA03FA1S3sp1S2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2dA2NAS2dX2W0S1R3HIA2hqFS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS3sp1S2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FFFS1R2sp2lo3SLO3sp13SP13NRMS1A3A8v2KAS2dA2NA2KGS1A2A02KNS2An3FA02KZS2dX2dA1E1KFFS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S2FBS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA4NA98FS2dA2NAS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3NA03dLX2dY2dZ2NAS3sp12r04SP1M1q1r1H2H02q02H4S3sp1S3sp1S2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY2dZS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS2dA2NAS2FBS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS2sp2lo3sp13SP1S3sp1S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1RFS3sp14SP1RS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ3ALO2NX4C24q2An3FA12HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ3ALO4LENA4C24q2An3FA12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENY3PYC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENY3PYC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13dLX2dY2dZ3ALO4LENY3PYC2HB5Ha_st5Hl_stS1R2LF2sp1A3LFB2dA3sp14gapn3SP13dLX2dY2dZ2HB5Ha_st5Hl_stS2LF2sp3LFB2dA3sp14gapn3SP13dLX2dY2dZ2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13dLX2dY2dZ3ALO2F12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY3EAY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY3EAX2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dYS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24qS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LF1A3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dY3ARvS2LF1A3LFB2dA4gapn3dLX2dYS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24qS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZS2LF3LFB2dA3sp14gapn3dLX2dY2dZ4SP1R2HBS2LF3LFB2dA3sp14gapn3dLX2dY2dZ4SP1R2HBS2LF3LFB2FB4gapn3dLX2dYS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4SP1R4C24q2HBS1R2LF2sp1A2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZ2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZ2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4SP1R4C24q2HBS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24qS2LF1A3LFB2dA4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2F02HBS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_stS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZS2LF3LFB2dA3sp14gapn3dLX2dY2dZ2HB5Ha_stS2LF3LFB2dA3sp14gapn3dLX2dY2dZ2HB5Ha_stS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS1R2LF1A2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZ2HB5Ha_st5Hl_stS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZ2HB5Ha_st5Hl_stS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24qS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZS2LF1A3LFB2dA4gapn3dLX2dYS2LF3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dYS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24qS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZS1R2LF1A3LFB2dA3sp14gapn3dLX2dY2dZ2HB5Ha_st5Hl_stS2LF1A3LFB2dA3sp14gapn3dLX2dY2dZ2HB5Ha_st5Hl_stS2LF3LFB2dA3sp14gapn3dLX2dY2dZ2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2F02HBS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24qS2LF3LFB2dA4gapn3dLX2dY". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H SXA IA2 ESA PHIR0 FRR0 NA0 NB0 CALLOC"] Lemma dv_M3 : dvM4_stmt -> dvM3_stmt.
  Proof.
    intros K4. unfold dvM3_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX LFY OZ0 OT0 UW VAB HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWX : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 80) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWY : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 112) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    dpose LFX as (ABX & NX & OXH & TRX & BDX). dpose LFY as (ABY & NY & OYH & TRY & BDY).
    (* [comment removed for export] *)
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _ & _ & _ & _ & _ & HFY & _); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & _ & LENY & NRY & OWY) _]. rewrite OYH in OWY. ddestruct OWY as (_ & _ & _ & UAY). rewrite EAY in CY. unfold mpi_cells in CY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    pose proof (munch_refl [(md_addr dY + 8, md_addr dY + 10)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; set_sg dY 1; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { change [dLX; set_sg dY 1; dZ; dT] with (set_nth 1 [dLX; dY; dZ; dT] (set_sg dY 1)).
      eapply sign_store_l with (mq := mq); try eassumption; try reflexivity. unfold mpi_cells. rewrite EAY. exact CY. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| rewrite EAY; clear - F1 ALO LOS SLO SP1 NEEDR; lia]).

    clear MU WM.
    (* [comment removed for export] *)
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m2) (i := 0%nat) (d := dLX) as (MLX & _ & _ & _ & _ & _ & HFX & _); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & _ & LENX & NRX & OWX) _]. rewrite OXH in OWX. ddestruct OWX as (_ & _ & _ & UAX). rewrite EAX in CX. unfold mpi_cells in CX.
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    pose proof (munch_refl [(md_addr dLX + 8, md_addr dLX + 10)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    assert (CST3 : CSTA m3 hq LBq [set_sg dLX 1; set_sg dY 1; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { change [set_sg dLX 1; set_sg dY 1; dZ; dT] with (set_nth 0 [dLX; set_sg dY 1; dZ; dT] (set_sg dLX 1)).
      eapply sign_store_l with (mq := m2); try eassumption; try reflexivity. unfold mpi_cells. rewrite EAX. exact CX. }
    assert (UW3 : UWCD m3) by (eapply S_uwcd_store; [exact UW2| exact MU| rewrite EAX; clear - F1 ALO LOS SLO SP1 NEEDR; lia]).
    clear MU WM.
    (* [comment removed for export] *)
    pose proof (opv_A _ _ _ _ _ _ _ CST3) as (CAv & OAv & ARv & A8v & _ & LENA & NA & _).
    rewrite <- AE in CAv, OAv, ARv, A8v. unfold mpi_cells in CAv.
    assert (A0 : 0 < A).
    { destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
      - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
        edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MW & _); try eassumption. pose proof MW as [(_ & _ & W0 & _) _]. rewrite AE, EQA. clear - W0. lia.
      - pose proof (ESA NE) as HeA. edestruct (A_mpi_client2.cs_ext_facts asegs R HIA) with (e := dA) as (ME & _); try eassumption. pose proof ME as [(_ & _ & E0 & _) _]. rewrite AE. clear - E0. lia. }
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (CH3 & _ & _ & _ & _).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as OK3.
    unfold A_mpi_div_mpi_C.DCS in CH3.
    apply Forall_cons_iff in CH3. destruct CH3 as [SPC CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [T2Cq CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [ZCq CH3].
    apply Forall_cons_iff in CH3. destruct CH3 as [CZq CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [GAPC CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [SAVE CH3].
    apply Forall_cons_iff in CH3. destruct CH3 as [FHD CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [Z32C CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [Z48C CH3].
    apply Forall_cons_iff in CH3. destruct CH3 as [Z64C CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [TPC CH3]. apply Forall_cons_iff in CH3. destruct CH3 as [JQC _].
    cbn [fst snd] in SPC, T2Cq, ZCq, CZq, GAPC, SAVE, FHD, Z32C, Z48C, Z64C, TPC, JQC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    pose proof (munch_refl [(sp1, sp1 + 152)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KN; zify_cond KN; [exfalso; clear - KN A0; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by lia; clear - KA A8v; lia|].
    zstep. zstep. zstep.
    shadow_chk OAv (A + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dA)) by (clear - NA; lia). zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by (clear - NA; lia).
    { eapply dv_ERR16; [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| |].
      - clear - HV NA0 NB0. unfold_bud. lia.
      - clear - HF D0. unfold_bud. lia. }

    assert (NA98 : md_n dA <= 9998) by (clear - KL; lia).
    (* [comment removed for export] *)
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & _ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZ0 in OWZ. destruct OWZ as [PZ0 NZ0]. rewrite EAZ, PZ0, NZ0 in CZ. unfold mpi_cells in CZ.
    zstep. zstep.
    zstep. rewrite (zx16_small 0) by (clear; lia). zstep.
    zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by (clear - NA; lia); [exfalso; clear - KG NA; lia|].
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3s end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3s |- _ => rename H into HH3s end.
    match goal with H : mem_inv asegs m3s |- _ => rename H into MI3s end.
    match goal with H : stk asegs m3s lo sp1 |- _ => rename H into ST3s end.
    assert (CST3s : CSTA m3s hq LBq [set_sg dLX 1; set_sg dY 1; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 (Z_to_bv 64 (md_n dA + 2)) SHA10 (Z_to_bv 64 (A + 10)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := m3) (m2 := m3s) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [set_sg md_addr]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OK3| reflexivity ..]. }
    assert (UW3s : UWCD m3s) by (eapply S_uwcd_store; [exact UW3| exact MU| clear; lia]).
    zstep.
    replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    pose proof (A_mpi_client2.cs_cnt24 asegs R HIA HNDk h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as C24q. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in C24q.
    pose proof (arl_need_rt_malloc R) as NRM.
    pose proof (conj CZ I) as CZb. pose proof (conj SPC I) as SPCb.
    clear SPC T2Cq ZCq CZq GAPC SAVE FHD Z32C Z48C Z64C TPC JQC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := hq) (LB := LBq) (LF := LF1) (cnt := md_n dA + 2) (sz := 4) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (rewrite HSq; exact UW3s).
      all: try (rewrite HTq; clear - SP1 TOP; lia).
      all: try (intros _; clear - C24q C24H; unfold C24_DIV_MPI in C24H; lia).
      all: try (rewrite vchg_small by (unfold AMAX_SEC; clear - NA98; lia)).
      all: try (clear - SP1M; Z.div_mod_to_equations; lia).
      all: try (unfold AMAX; clear - NA NA98 SLO SP1 NRM NEEDR; lia).
      all: try (clear - HVq BUD HV NA0 NB0 PHIR0; unfold_bud; lia).
      all: try (clear - HFRq BUDF HF D0 FRR0; unfold_bud; lia).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]. }

    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
    unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (MI4 & ST4 & MF4 & WM4 & HP4 & h4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & CASES).
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
    rewrite vchg_small in HV4 by (unfold AMAX_SEC; clear - NA98; lia).
    destruct CZb as [CZ3 _]. destruct SPCb as [SPC3 _].
    assert (CZ4 : rw_cells asegs m4 (sp1 + 184) [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 (md_sg dZ)); C2 (Z_to_bv 64 0); C4 (md_pad dZ)]).
    { eapply (presA_rw_cells asegs R); [exact HP4| exact CZ3| apply client_range_stack; clear; lia| exact I]. }
    eassert (SPC4 : rw_cells asegs m4 sp1 _) by (eapply (presA_rw_cells asegs R); [exact HP4| exact SPC3| apply client_range_stack; clear; lia| exact I]).
    assert (UW4 : UWCD m4).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP4| rewrite HSq; exact UW3s| clear; lia| intros a Ha; exact I| clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
    apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ mo' (conj HK4 (mo_frame_trans _ _ _ MF1 MF4))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h4) as LAWS. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV.
    pose proof (hcs_ok asegs R HIA h4) as CSOK4. pose proof (hcs_stack asegs R HIA h4) as SCS04.
    assert (SCS4 : crange (hcs asegs R HIA h4) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS04| clear - LOS; lia| rewrite HS4, HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    clear MU WM.
    destruct CASES as [[Er HH4] | (An & Er & A16 & HFRA & HAS & HH4 & HNEW)]; match type of Er with ?vv = _ => subst vv end.
    - (* [comment removed for export] *)
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      zstep.
      assert (MLZ4 : mpd_at asegs m4 LBq dZ).
      { split; [| exact SGZ]. split; [rewrite EAZ, PZ0, NZ0; exact CZ4|]. split; [exact Z8|]. split; [exact Z0|]. split; [exact LENZ|]. split; [exact NRZ|]. rewrite OZ0. split; [exact PZ0| exact NZ0]. }
      assert (CST4 : CSTA m4 h4 LBq (set_nth 2 [set_sg dLX 1; set_sg dY 1; dZ; dT] dZ) dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 (Z_to_bv 64 (md_n dA + 2)) SHA10 (Z_to_bv 64 (A + 10)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (v + 0) (f + fr_charge (d + 1))).
      { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := 2%nat) (dX := dZ) (mq := m3s) (hq := hq); try eassumption; try reflexivity.
        - split; [reflexivity|]. split; [exact NSZ|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b _ _. reflexivity.
        - eapply presA_weaken; [exact HP4| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx _; exact I].
        - intros b Hb. left. exact Hb.
        - intros b Hb. left. exact Hb. }
      cbn [set_nth] in CST4.
      eapply dv_ERR16; [exact CST4| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW4| |].
      + clear - HV NA0 NB0. unfold_bud. lia.
      + clear - HF D0. unfold_bud. lia.
    - (* [comment removed for export] *)

      dpose HFRA as (FA0 & FA1 & FA2 & FA3).
      replace ((md_n dA + 2) * 4) with (4 * (md_n dA + 2)) in * by (clear; lia).
      pose proof (munch_refl [(sp1 + 184, sp1 + 200)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - FA0 FA1 ACV; lia); [exfalso; clear - KZ FA0; lia|].
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : HM asegs R HIA h4 _ LF1 m5 |- _ => rename H into HH5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      match goal with H : stk asegs m5 lo sp1 |- _ => rename H into ST5 end.
      set (dZ5 := mkMPD (sp1 + 184) (md_sg dZ) (md_n dA + 2) An (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2))) (md_pad dZ) LHeap).
      assert (MLZ5 : mpd_at asegs m5 ((An, 4 * (md_n dA + 2)) :: LBq) dZ5).
      { split; [| exact SGZ]. unfold dZ5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells.
        split; [exact CZ4|]. split; [clear - SP1M; Z.div_mod_to_equations; lia|]. split; [clear - SP1R SP1 SLO LOS ALO ACP NEEDR; lia|].
        split; [rewrite repeat_length; clear - NA; lia|]. split; [unfold MPI_MAX_LIMBS; clear - NA NA98; lia|].
        split; [clear - NA; lia|]. split; [left; reflexivity|]. split; [exact A16|].
        eapply (u32arr_of_cells asegs); [exact HNEW| rewrite u32s_repeat0; f_equal; clear - NA; lia]. }
      assert (CST5 : CSTA m5 h4 ((An, 4 * (md_n dA + 2)) :: LBq) (set_nth 2 [set_sg dLX 1; set_sg dY 1; dZ; dT] dZ5) dX
                       (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 (Z_to_bv 64 (md_n dA + 2)) SHA10 (Z_to_bv 64 (A + 10)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (v + 0) (f + fr_charge (d + 1))).
      { eapply (A_mpi_client2.cs_calloc_attach asegs R HIA) with (i := 2%nat) (d := dZ) (mq := m3s) (hq := hq); try eassumption; try reflexivity.
        - eapply presA_trans with (m1 := m4).
          + eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx _; exact I].
          + rewrite EAZ. replace (sp1 + 184 + 16) with (sp1 + 200) by (clear; lia).
            eapply presA_weaken with (LB := (An, 4 * (md_n dA + 2)) :: LBq) (LF := LF1) (SP := sp1) (SSP := arl_stklo R) (TOP := hstkhi asegs R HIA hq);
              [| intros b Hb; right; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx K; exact K].
            eapply (presA_of_munch asegs R _ LF1 _ _ _ _ m4 m5 (hcs asegs R HIA h4) CSOK4); [| intros c0' Hc; rewrite <- HS4 in Hc; eapply cshd_hcs; [exact HH5| | exact Hc]; clear; lia| exact MU| exact WM].
            unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS4| clear - SP1 SLO NEEDR; lia| clear - SP1; lia]| apply Forall_nil].
        - unfold dZ5. cbn [md_addr]. rewrite EAZ. reflexivity. }
      cbn [set_nth] in CST5.
      assert (UW5 : UWCD m5) by (eapply S_uwcd_store; [exact UW4| exact MU| clear; lia]).
      unfold dvM4_stmt in K4.
      eapply K4 with (dZ := dZ5); [exact CST5| exact EAX| exact EAY| reflexivity| exact EAD| exact LFX| exact LFY| reflexivity| reflexivity| reflexivity| reflexivity| exact OT0| exact UW5| exact VAB| exact NA98| |].
      + clear - HV. unfold_bud. lia.
      + clear - HF. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L19980016842.7 L23519742181.11L30177375626.8 L41650118032.6 L41953732581.12L4781719053.2  L52101693566.17L62037211595.7 L6203936179.1  L66151427842.16L9356559676.11 L9838743115.2  00000H00m01L01`02G02M03I03d03i04E05005:S1R3HIA1h2sp3TOP3sp13SP1S1R3HIA1h1d3FRb4BUDF3FRC2hq1f2HF4HFRqS1R2sp2lo3SLO3sp13SP15STACK3STKS1R2FB2dl3DLF3ALO2F1S1R3HIA1h4PHIb3BUD3PHI2hq1v2dl1c2HV3HVqS1d2D0S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2dl3DLF3ALO2F11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF C24H"] Lemma call_xop_l : forall ENTRY STACK C24x (P : Z -> Prop) (PHI : mpd -> Z -> Z) (FRC : Z -> Z) Rr,
    mpi_xop_stmtA_c asegs R HIA ENTRY STACK C24x P PHI FRC Rr -> STACK <= 272 -> C24x <= 2 ->
    (forall LBx dx c r dx', Rr LBx dx c r dx' -> forall b, In b (mpd_blk dx') -> In b (mpd_blk dx) \/ ~ In b LBx) ->
    forall mq hq LBq ls CS0 v f i dl (c : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> length ls = 4%nat -> nth_error ls i = Some dl -> md_addr dl + 16 <= FB + 256 -> P c ->
    UWCD mq -> v + PHI dl c <= PHIb -> f + FRC (d + 1) <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr dl) -> a1v = Z_to_bv 64 c ->
    (forall m3 h3 LB3 dl' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls dl') dX CS0 DV_FSH (v + PHI dl c) (f + FRC (d + 1)) -> Rr LBq dl c r dl' -> mpd_at asegs m3 LB3 dl' -> md_addr dl' = md_addr dl -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None mq (seg_rom asegs)).
  Proof.
    intros ENTRY STACK C24x P PHI FRC Rr SPEC STK HC24x RFR. intros until t6. intros CST LSL NTH DLF PC UW HV HF RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := dl) as (ML & NSL & XWL & LLO & _ & _ & _ & _ & _ & _ & OL); try eassumption.
    unfold mpi_xop_stmtA_c in SPEC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := dl) (v := c) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact ML | exact NSL | exact PC | exact XWL | exact LLO | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | reflexivity
              | (rewrite HSq; exact UW)
              | lazymatch goal with
                | |- lo <= sp1 - _ - _ => clear - SLO SP1 STK; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ _ => split; [exact OL| intros EO; exfalso; exact (NSL EO)]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD HV; lia
                | |- uw_obj _ _ 16 _ => left; split; [clear - DLF F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "XOP-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dl3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls dl3) dX CS0 DV_FSH (v + PHI dl c) (f + FRC (d + 1))).
    { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := i) (dX := dl) (mq := mq) (hq := hq); try eassumption.
      exact (RFR _ _ _ _ _ RR3). }
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DLF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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

  Hypothesis LSETNG : mpi_lset_ng_stmtA asegs R HIA A_MPI_LSET.

  (* [comment removed for export] *)
  Definition dvM4b_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 SHA10 (Z_to_bv 64 (A + 10)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV4 <= PHIb -> f + dvF4 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f770) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L12128799109.1 L12869389312.2 L19980016842.7 L23929348277.6 L52101693566.8 L5413320392.1  L62037211595.7 L63072848869.3 L66151427842.16L66668349941.1 L9356559676.11 00000300=00U00j01D01I01d02002L02O03:S1fS3sp14SP1RS1R3HIA1h2sp3TOP3sp13SP1S1R2sp2lo3SLO3sp13SP1S1R3HIA3sp12hq2dl3DLZ1a2HaS3sp1S1R5NEEDR2sp2lo3LOS3SLO3SPRS2sp3sp13SP1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR".
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 LSETNG"] Lemma w2_call_lset_z : forall mq hq LBq ls CS0 v f i dl (z : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_addr dl = sp1 + 184 -> 1 <= md_n dl -> -2^31 <= z < 2^31 ->
    UWCD mq -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr dl) -> a1v = Z_to_bv 64 z ->
    (forall m3 h3 LB3 dl' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls dl') dX CS0 DV_FSH v f -> P_mpi_lset.lset_R z dl LBq r dl' -> mpd_at asegs m3 LB3 dl' -> md_addr dl' = md_addr dl -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_LSET) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NTH DLZ N1 ZR UW RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := dl) as (ML & NSL & XWL & LLO & _ & _ & _ & _ & _ & _ & OL); try eassumption.
    pose proof LSETNG as SPEC. unfold mpi_lset_ng_stmtA in SPEC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := dl) (v := z) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact ML | exact NSL | exact N1 | exact ZR | exact XWL | exact LLO | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | reflexivity
              | lazymatch goal with
                | |- lo <= sp1 - _ - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ _ => split; [exact OL| intros EO; exfalso; exact (NSL EO)]
                end
              | match goal with |- ?g => idtac "W2-LSET-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dl3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls dl3) dX CS0 DV_FSH (v + 0) (f + 0)).
    { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := i) (dX := dl) (mq := mq) (hq := hq); try eassumption.
      ddestruct RR3 as (_ & _ & KK). exact KK. }
    replace (v + 0) with v in CST3 by (clear; lia). replace (f + 0) with f in CST3 by (clear; lia).
    assert (UW3 : UWCD m3).
    { eapply uwc_floor with (F := sp1 + 216); [| clear; lia].
      rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; eapply uwc_raise_m; [exact UW| clear - SP1; lia]| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DLZ; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L18320580243.8L29956516996.0L30157387091.6L38691415991.0L51352513313.0L58184598986.4L9144300466.2 00000N00O00b00c00d01201:S2dA2dB4PHIb4PHIr3NA03NB01v2HVSS1d3FRb2D03FRr1f2HFSSS2dA3NA02dZ2NZS2dA3NA0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF PHIR0 FRR0 NA0 NB0 LSETNG"] Lemma dv_M4 : dvM4b_stmt -> dvM4_stmt.
  Proof.
    intros K4b. unfold dvM4_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX LFY SGX SGY OZH NZ OT0 UW VAB NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    eapply (w2_call_lset_z mq hq LBq _ _ v f 2%nat dZ 0 0x9f76c); [exact CST| reflexivity| exact EAZ| clear - NZ NA0; lia| clear; lia| exact UW| clear; lia| reflexivity| rewrite EAZ; reflexivity| reflexivity|].
    (* [comment removed for export] *)
    intros m3 h3 LB3 dl' r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
    pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    unfold dvM4b_stmt in K4b.
    ddestruct RR3 as [[(-> & NN' & OW' & _ & _ & _)|(-> & ->)] _].
    - zstep.
      eapply K4b with (dZ := dl'); [exact CST3| exact EAX| exact EAY| rewrite EAL3; exact EAZ| exact EAD| exact LFX| exact LFY| exact SGX| exact SGY| exact OW'| rewrite NN', NZ; clear - NA0; lia| exact OT0| exact UW3| exact VAB| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      zstep.
      eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
      + clear - HV NA0 NB0. unfold_bud. lia.
      + clear - HF D0. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  Hypothesis GROW : mpi_grow_stmtA_c asegs R HIA A_MPI_GROW.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L24928467151.11000000SS2LF2ra2sp3LFB2FB3sp14gapn2d02N02N1". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma out_heapA : forall mq LBq d0, mpd_at asegs mq LBq d0 -> md_own d0 <> LStatic -> 1 <= md_n d0 -> md_own d0 = LHeap.
  Proof.
    intros mq LBq d0 [(_ & _ & _ & _ & _ & HO) _] NS N1. destruct (md_own d0) eqn:O; [| reflexivity| exfalso; exact (NS eq_refl)].
    destruct HO as [_ N0]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvM5_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LHeap -> md_n dT = md_n dA + 2 ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV5 <= PHIb -> f + dvF5 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f794) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L13655593885.5  L14348534914.6  L1921887436.7   L23539585209.2  L25651766269.2  L27019463589.2  L29956516996.0  L30780105986.8  L31720098237.6  L35663928186.7  L43677759120.213L58500857548.9  L60098763854.3  L60496062113.0  L64810467185.2  L65252552111.1  L66390627273.0  L9356559676.11  Q17356582774.214Q18397797912.215Q19056309629.215Q28096359191.212Q39212284437.215Q45989859327.215Q45990201585.214Q52017248394.212Q60085137072.212Q60511567613.215Q63565942191.214Q63566450772.212Q63566565718.215Q67304096620.214Q67304703074.215Q9538787269.212 00000@00P00h00o01601=01>01\02202G02j03N03X03Y03`03d03e04P04b05805J05h06:06U07007K07]07m08?08Q08c09A09_09oS1d3FRb3FRr1f2HFS1d3FRb3FRr1f2HFS1d3FRb2D03FRr4FRR01f2HFS2dA2NAS2dA2NAS2dA2NASS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA2dB4PHIb4PHIr1v2HVS1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3ARvS2dA2dB4PHIb4PHIr5PHIR03NA03NB01v2HVS1R2lo3LOSSS2dA2NAS2FBSS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapn3ARvS2LF1A3LFB2dA4gapnS2LF2sp2lo3LFB2dA3sp14gapn3SP1S2LF1A3LFB2dA4gapnS2LF2lo3LFB2dA3sp14gapn3LOCS2LF2lo3LFB2dA3sp14gapn3LOCS2LF2lo3LFB2dA3sp14gapn3LOCS2LF1A3LFB2dA4gapnS2LF3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF2sp2lo3LFB2dA3sp14gapn3SP1S2LF2sp2lo3LFB2dA3sp14gapn3SP1S2LF3LFB2dA4gapn". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H SXA IA2 ESA PHIR0 FRR0 NA0 NB0 GROW"] Lemma dv_M4b : dvM5_stmt -> dvM4b_stmt.
  Proof.
    intros K5. unfold dvM4b_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX LFY SGX SGY OZH NZ OT0 UW VAB NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. apply Forall_cons_iff in CHq'. destruct CHq' as [SPC _]. cbn [fst snd] in SPC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    pose proof (opv_A _ _ _ _ _ _ _ CST) as (CAv & OAv & ARv & A8v & _ & LENA & NA & _).
    rewrite <- AE in CAv, OAv, ARv, A8v. unfold mpi_cells in CAv.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. shadow_byte OAv (A + 10) 2 as k RD HK. zstep. clear RD. step_to_if.
    lazymatch goal with |- aevtA ?segs _ _ (MS ?R0 ?F0 (if ?cnd then Z_to_bv 64 ?slow else Z_to_bv 64 ?fast) ?fc0 ?rv0 ?m0 ?ro0) =>
      let pk := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
      let pt := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
      merge_cut_apply segs (fun ms' => exists vk vt : word, ms' = MS (tset pt vt (tset pk vk R0)) F0 (Z_to_bv 64 fast) fc0 rv0 m0 ro0) end.
    { let Kz := fresh "Kz" in if_cases Kz; zify_cond Kz.
      - zstep. step_to_if.
        lazymatch goal with |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
          replace cnd with true by (symmetry; eapply (shadow_slow_takenN (A + 10) _ k _ HK Kz); qlia); cbv iota end.
        apply evtA_done; eexists; eexists; reflexivity.
      - apply evtA_done; eexists; eexists; reflexivity. }
    intros ms' (vk & vt & ->); cbv beta iota delta [tset]; try clear HK; try clear k.
    zstep. zstep. rewrite (zx16_small (md_n dA)) by (clear - NA; lia). zstep. zstep. zstep. clear MU WM.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 3%nat) (d := dT) as ([(_ & _ & _ & _ & _ & OWT) _] & _); try eassumption; [reflexivity|]. rewrite OT0 in OWT. destruct OWT as [_ NT0].
    eapply (call_xop_l A_MPI_GROW MPI_GROW_STACK_A _ _ _ _ _ GROW ltac:(clear; lia) ltac:(vm_compute; discriminate)) with (mq := mq) (i := 3%nat) (dl := dT) (c := md_n dA + 2) (retpc := 0x9f790); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
    - intros LBx dx c r dx' [_ K] b Hb. exact (K b Hb).
    - rewrite EAD. clear. lia.
    - clear - NA. lia.
    - clear - HV NA0 NB0 PHIR0. unfold_bud. lia.
    - clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dl' r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 3%nat) (d := dl') as (_ & NS' & _ & _ & _ & _ & _ & SLOC' & _); try eassumption; try reflexivity.
      assert (EAD' : md_addr dl' = FB + 144) by (rewrite EAL3; exact EAD).
      unfold dvM5_stmt in K5.
      ddestruct RR3 as [[(-> & SG' & NN' & _)|(-> & ->)] _].
      + zstep.
        assert (NT' : md_n dl' = md_n dA + 2) by (rewrite NN', NT0; clear - NA; lia).
        eapply K5; [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD'| exact LFX| exact LFY| exact SGX| exact SGY| exact OZH| exact NZ| | exact NT'| exact UW3| exact VAB| exact NA98| |].
        * eapply out_heapA; [exact ML3| exact NS'| rewrite NT'; clear - NA; lia].
        * clear - HV. unfold_bud. lia.
        * clear - HF. unfold_bud. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * clear - HV NA0 NB0. unfold_bud. lia.
        * clear - HF D0. unfold_bud. lia.
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

  Hypothesis BITLEN : mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.

  (* [comment removed for export] *)
  Definition dvM6_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= md_n dY -> md_n dY <= md_n dLX -> md_n dLX <= md_n dA + 1 -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dLX = 1 -> md_sg dY = 1 -> 0 < mpd_val dY <= mpd_val dLX -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvV6 <= PHIb -> f + dvF6 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f7b0) fc None mq (seg_rom asegs)).

  #[using="Type"] Lemma val_lvalA : forall mq LBq d0, mpd_at asegs mq LBq d0 -> md_sg d0 = 1 -> mpd_val d0 = lval (md_limbs d0) (md_n d0).
  Proof.
    intros mq LBq d0 [(_ & _ & _ & HL & _) _] SG. unfold mpd_val. rewrite SG, Z.mul_1_l. fold (mpd_abs d0). apply mpd_abs_lval. exact HL.
  Qed.

  #[using="Type"] Lemma shl_fresh : forall LBx dx c r dx', shift_l_R c dx LBx r dx' -> forall b, In b (mpd_blk dx') -> In b (mpd_blk dx) \/ ~ In b LBx.
  Proof. intros LBx dx c r dx' [_ (_ & _ & K & _)] b Hb. exact (K b Hb). Qed.

  (* [comment removed for export] *)
  Definition nfacts (dLX dY dZ dT : mpd) : Prop :=
    md_own dLX = LHeap /\ md_own dY = LHeap /\ md_own dZ = LHeap /\ md_own dT = LHeap
    /\ 1 <= md_n dY /\ md_n dZ = md_n dA + 2 /\ md_n dT = md_n dA + 2 /\ md_sg dLX = 1 /\ md_sg dY = 1 /\ 0 < mpd_val dY <= mpd_val dLX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@D35300034347.240D60189065437.240L12469921329.0  L13483787457.1  L14016578221.12 L14348534914.6  L15162592258.2  L1685717371.0   L18457770450.4  L1921887436.7   L23594257982.3  L25581210123.2  L26731563765.235L26985680806.1  L27293207874.6  L27588716945.2  L2782056031.15  L28632618922.2  L28784609534.5  L2885095.4      L28860327085.12 L29956516996.0  L30162977185.0  L30780287258.12 L31145622673.2  L31525463372.2  L31718147504.16 L32284259785.0  L34080941563.2  L35526939379.7  L35663928186.7  L37540154232.2  L38259954321.2  L40149985318.4  L41415990515.2  L45657748817.2  L48700858022.1  L50409213458.12 L51794595714.2  L52163114669.12 L54519161338.13 L55815189670.1  L56757544215.4  L57652312495.1  L57698627611.2  L58500772564.13 L59724895848.2  L59726336417.0  L59975262609.2  L60098763854.3  L65614147016.1  L67647012628.6  L9018141615.1   L9356559676.11  P27590552406.241P28627113325.241P31146933846.241P38261788758.241P45659584406.241P57713046236.241P59963990870.241Q11968186855.241Q16827575549.241Q25954107624.241Q28092229165.293Q28096359191.237Q28465177121.238Q3421936230.240 Q52017248394.237Q52021507504.293Q5265442331.239 Q57228775306.240Q60189065437.241Q68235297648.24000001>02L02M02R03;03I03O03P03]04504A04G04f04k05905:05l05m06>06L07507607707b07c07k08c08d08n09F09[09a09b0:20:30:40:90:>0:D0:m0;[0;`0<00<40<50<f0<l0<m0<n0=80==0=R0=V0>A0?G0@M0AS0BY0C_0DH0EN0FT0FU0FV0G30GN0Gg0HS0Hk0IE0I_0JH0KD0KfS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq1k3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3SPR2F04SP1R2HB5Ha_st5Hl_stFS3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3FRb3FRr1f2HFS1k2HKSS2dY1k3NY12GYS1d3FRb2D03FRr4FRR01f2HFS2sp3sp13SP1S1k2HKS2LF2ra2sp3LFB2FB3sp14gapn1k2HKS3sp1S3FRb3FRr1f2HFFS2dA2dB4PHIb4PHIr3NA03dLX2dY1v1k3NXA3NYB2HV2SN3SNYFS2dA3dLX1k3NXA2SNS3FRb3FRr1f2HFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1SSS2dA2dB4PHIb4PHIr3NA03NB03dLX1v1k3NXA2HV2SNFS2dY3NY1S2dA2dB4PHIb4PHIr5PHIR03NA03dLX2dY1v1k3NXA3NYB2HV2SN3SNYSS3sp14gapnS1d3FRb2D03FRr4FRR01f2HFS1R3HIA1h2sp2lo3TOP1HS1k2HKFS3dLX2dY3NY13NYXSFS3sp1S3sp1S1k2HKS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2dA2dB4PHIb4PHIr3dLX2dY1v1k3NXA3NYB2HV2SN3SNYS3sp1S3dLX2dY3NY13NYXS2FBFS2dA2dB4PHIb4PHIr5PHIR03NA03NB03dLX1v1k3NXA2HV2SNS1j2HjSFS1R2lo3LOSS3sp1S3dLX2dY1k3NY13NYX2GXS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stFFS2LF2sp2lo3LFB3sp14gapn3SP11kS2LF2sp2lo3LFB3sp14gapn3SP1S2LF3LFB3sp14gapn4SP1R2HBS2LF2sp2lo3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS2LF2lo3LFB3sp14gapn3LOC1kS2LF3LFB3sp14gapn2HB5Ha_stS2LF2lo3LFB3sp14gapn3LOC1k2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1k2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H PHIR0 FRR0 NA0 NB0 SHL"] Lemma dv_M5b : dvM6_stmt ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    nfacts dLX dY dZ dT -> md_n dY <= md_n dLX -> md_n dLX <= md_n dA -> md_n dY <= md_n dB -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvV5 <= PHIb -> f + dvF5 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 (Z_to_bv 64 (31 - k)) a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9fab8) fc None mq (seg_rom asegs)).
  Proof.
    intros K6. intros until t6. intros CST EAX EAY EAZ EAD NF NYX NXA NYB HK UW BPOS NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    ddestruct NF as (OXH & OYH & OZH & OTH & NY1 & NZ & NT & SGX & SGY & VXY).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as OKq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & _); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof (val_lvalA _ _ _ MLX SGX) as VLX. pose proof (val_lvalA _ _ _ MLY SGY) as VLY.
    assert (BLE : core_bitlen (md_limbs dY) (md_n dY) <= core_bitlen (md_limbs dLX) (md_n dLX)).
    { apply core_bitlen_mono_val; [clear - NY1 NYX; lia| clear - NY1; lia| rewrite <- VLX, <- VLY; exact (proj2 VXY)]. }
    assert (XK : Z.lxor (31 - k) 31 = k).
    { assert (E : exists j, (j < 32)%nat /\ k = Z.of_nat j) by (exists (Z.to_nat k); clear - HK; lia).
      destruct E as (j & Hj & ->). clear - Hj. do 32 (destruct j as [|j]; [reflexivity|]). lia. }
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. repeat (apply Forall_cons_iff in CHq'; destruct CHq' as [?CK CHq']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
    pose proof (munch_refl [(sp1, sp1 + 168)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. rewrite ?XK.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 168); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. clear MU WM.
    unfold mpi_shift_l_stmtA_c in SHL.
    eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m2) (i := 0%nat) (dl := dLX) (c := k) (retpc := 0x9fac8); try eassumption; try reflexivity; try (rewrite EAX; reflexivity).
    - rewrite EAX. clear. lia.
    - cbv beta. clear - HK. lia.
    - pose proof (shift_l_n_le_succ k dLX ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia)) as SN. unfold shift_l_PHI. clear - HV NA0 NB0 PHIR0 SN NXA. unfold_bud. lia.
    - cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dX3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      pose proof (shift_l_n_le_succ k dLX ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia)) as SN.
      assert (EAX3 : md_addr dX3 = FB + 80) by (rewrite EAL3; exact EAX).
      ddestruct RR3 as [[(-> & VX3 & SG3 & NX3)| ->] _].
      + zstep.
        (* [comment removed for export] *)
        destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (CH3 & SH3 & MI3 & ST3 & HH3).
        pose proof CH3 as CH3'. unfold A_mpi_div_mpi_C.DCS in CH3'. repeat (apply Forall_cons_iff in CH3'; destruct CH3' as [?CL CH3']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
        zstep.
        destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (HT3 & HS3 & _ & HCS3 & _ & _).
        pose proof (hcs_ok asegs R HIA h3) as CSOK3. pose proof (cs_ok_sb _ _ CSOK3) as SB643. pose proof (hcs_stack asegs R HIA h3) as SCS03.
        assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| rewrite HS3; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
        zstep. zstep. clear MU WM.
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 1%nat) (d := dY) as (MLY3 & _); try eassumption; [reflexivity|].
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 0%nat) (d := dX3) as (_ & NSX3 & _); try eassumption; [reflexivity|].
        pose proof (shift_l_n_le_succ k dY ltac:(clear - HK; lia) ltac:(clear - NY1; lia)) as SNY.
        eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3) (i := 1%nat) (dl := dY) (c := k) (retpc := 0x9fad8); try eassumption; try reflexivity; try (rewrite EAY; reflexivity).
        * rewrite EAY. clear. lia.
        * cbv beta. clear - HK. lia.
        * unfold shift_l_PHI. clear - HV NA0 NB0 PHIR0 SN SNY NXA NYB. unfold_bud. lia.
        * cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
        * clear. lia.
        * intros m4 h4 LB4 dY4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
          pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV4.
          pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
          assert (EAY4 : md_addr dY4 = FB + 112) by (rewrite EAL4; exact EAY).
          ddestruct RR4 as [[(-> & VY4 & SG4 & NY4)| ->] _].
          -- zstep. zstep.
             edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 1%nat) (d := dY4) as (_ & NSY4 & _); try eassumption; [reflexivity|].
             edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 0%nat) (d := dX3) as (MLX4 & _); try eassumption; [reflexivity|].
             pose proof (shift_l_n_ge k dY ltac:(clear - HK; lia) ltac:(clear - NY1; lia)) as GY. pose proof (shift_l_n_ge k dLX ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia)) as GX.
             pose proof (shift_l_n_mono k dLX dY ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia) BLE) as MONO.
             assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; clear - HK; lia).
             unfold dvM6_stmt in K6.
             eapply K6 with (k := k); [exact CST4| exact EAX3| exact EAY4| exact EAZ| exact EAD| | | exact OZH| exact OTH| | | | exact NZ| exact NT| | | | exact HK| exact UW4| exact BPOS| exact NA98| |].
             ++ eapply out_heapA; [exact MLX4| exact NSX3| rewrite NX3; clear - GX NY1 NYX; lia].
             ++ eapply out_heapA; [exact ML4| exact NSY4| rewrite NY4; clear - GY NY1; lia].
             ++ rewrite NY4. clear - GY NY1. lia.
             ++ rewrite NY4, NX3. exact MONO.
             ++ rewrite NX3. clear - SN NXA. lia.
             ++ rewrite SG3. exact SGX.
             ++ rewrite SG4. exact SGY.
             ++ rewrite VY4, VX3. clear - VXY P2. nia.
             ++ unfold shift_l_PHI. clear - HV SN SNY NXA NYB. unfold_bud. lia.
             ++ clear - HF. unfold_bud. lia.
          -- zstep.
             eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| reflexivity| exact EAX3| exact EAY4| exact EAZ| exact EAD| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             ++ unfold shift_l_PHI. clear - HV NA0 NB0 SN SNY NXA NYB. unfold_bud. lia.
             ++ clear - HF D0. unfold_bud. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX3| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * unfold shift_l_PHI. clear - HV NA0 NB0 SN NXA. unfold_bud. lia.
        * clear - HF D0. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@D35300034347.287D60189065437.287L10933838098.12 L11144352574.3  L12469921329.0  L13869207609.0  L13884980141.12 L15908753905.3  L1685717371.0   L17090287777.0  L20490385257.3  L23147748781.12 L24356459904.261L24950277677.2  L26985680806.1  L27588716945.2  L27940357248.16 L27940405558.7  L2817928458.1   L28632618922.2  L31145622673.2  L31527560548.3  L32121109934.3  L33809151616.3  L33816087292.3  L34080941563.2  L3482839849.16  L35663928186.7  L3602826797.259 L37360441626.3  L37960732589.12 L38235734261.1  L38259954321.2  L38692635477.0  L3918199789.16  L42888674241.1  L43097941400.3  L45657748817.2  L48700858022.1  L49631569796.7  L49992332264.3  L51070401118.0  L53577728712.1  L5379476547.2   L54200787000.3  L54424851272.16 L55815189670.1  L57698627611.2  L59975262609.2  L60098763854.3  L61507631172.4  L62770781818.236L63346541849.236L6493359339.16  L65999237284.8  L67931420133.3  L9080220944.4   L9356559676.11  P27590552406.287P28627113325.287P31146933846.287P38261788758.287P45659584406.287P57713046236.287P59963990870.287Q11968186855.288Q16827575549.288Q25954107624.288Q28096359191.284Q28465177121.285Q28770016439.242Q3421936230.287 Q38718005143.242Q46711588518.242Q52017248394.284Q5265442331.286 Q56659378566.242Q57228775306.287Q60189065437.288Q68235297648.28700001N02l03103=03>03?03h04304404504@04i05M05U05Z05[06=06X06]06^06_06i07407>07I07S08P08e09g0:20:[0:_0:`0:a0;T0;Y0;d0;e0;j0<B0<L0<M0<R0<Y0<c0=V0=[0=\0=]0=g0>50>V0?70@40@R0@]0@l0AW0Bi0D;0EM0F_0H10Hb0J40KF0KG0KH0Km0LP0Lg0M[0N20NI0Nk0OO0Of0PW0Q_0RIS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY3SPR2F03HTq4SP1R3PY02bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R3PY02bl3BLR2HB5Ha_st5Hl_stS3sp1S2sp3sp13SP1FSS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3dLX2dY2LTSSS2dA3dLX2NXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2blS2dY3NRYS3sp1FS1R5NEEDR2sp2lo3SLO3sp13SP12dY3PY0S1R5NEEDR2sp2lo3SLO3sp13SP1S3sp1FFS2dB2dY2NYS2dA2dB3VABS2dB2dY2NYS2dA3dLX2NXS3sp14gapnS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4LENY4PY163PY03PYCS1R3HIA1h2sp2lo3TOP1HS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY3ACV3SPR2F04SP1R3PY03PYC2bl3BLRS2dA3dLX2NXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2loFSS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY3PY03PYCS3sp1S2dY2bl3BLRFS3sp1S2dA2dB3dLX2dY3VAB3BDX1TS2dY2bl2BMSS3sp1S2dY2blS2dB2dY2NYS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY3PY03PYCS3sp1FFS1R2lo3LOSS3FRb3FRr1f2HFS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4LENY4PY163PY03PYCS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA3dLX2NXS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2bl2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12bl3BLR2HB5Ha_st5Hl_stFFS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2blS2LF3LFB3sp14gapn3dLX2dY4SP1R2bl2HBS2LF3LFB2FB4gapn3dLX2dYS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2bl2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2blS2LF3LFB3sp14gapn3dLX2dY2bl2HB5Ha_stS2LF3LFB2FB4gapn3dLX2dYS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2bl2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP13dLX2dY2bl3BLR2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2bl2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H PHIR0 FRR0 NA0 NB0 BITLEN SHL"] Lemma dv_M5 : dvM6_stmt -> dvM5_stmt.
  Proof.
    intros K6. unfold dvM5_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX LFY SGX SGY OZH NZ OTH NT UW VAB NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    dpose LFX as (ABX & NX & OXH & TRX & BDX). dpose LFY as (ABY & NY & OYH & TRY & BDY).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & _); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _ & _ & _ & _ & _ & HFY & _ & _ & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & _ & LENY & NRY & OWY) _]. rewrite OYH in OWY. ddestruct OWY as (_ & INY & PY16 & UAY). rewrite EAY in CY. unfold mpi_cells in CY. unfold MPI_MAX_LIMBS in NRY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _). rewrite EAY in OYs.
    pose proof (u32arr_ro _ _ _ _ UAY) as BYY.
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    (* [comment removed for export] *)
    pose proof MLX as [_ SGXd]. pose proof MLY as [_ SGYd].
    assert (VX : mpd_val dLX = mpd_abs dA) by (unfold mpd_val; rewrite SGX, Z.mul_1_l; exact ABX).
    assert (VY : mpd_val dY = mpd_abs dB) by (unfold mpd_val; rewrite SGY, Z.mul_1_l; exact ABY).
    assert (NYX : md_n dY <= md_n dLX).
    { destruct TRY as [T|T]; [rewrite T; clear - NX; lia|].
      assert (LT : 2 ^ (32 * (md_n dY - 1)) < 2 ^ (32 * md_n dLX)) by (clear - T BDX VAB; lia).
      apply Z.pow_lt_mono_r_iff in LT; [clear - LT; lia| clear; lia| clear - NX; lia]. }
    assert (NF : nfacts dLX dY dZ dT).
    { unfold nfacts. repeat (split; [first [assumption| clear - NY; lia]|]). rewrite VX, VY. exact VAB. }
    pose proof (munch_refl [(sp1 - MPI_CORE_BITLEN_STACK_A, sp1)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (zx16_small (md_n dY)) by (clear - NRY; lia). zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_core_bitlen_stmtA, A_MPI_CORE_BITLEN in BITLEN.
      eapply BITLEN with (CS := hcs asegs R HIA hq) (A := md_p dY) (n := md_n dY) (lo := lo) (xs := md_limbs dY);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (exact (art_alwf asegs R HIA)).
      all: try (exact (hm_abase asegs R HIA hq LBq LF1 mq HHq)).
      all: try (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
      all: unfold MPI_CORE_BITLEN_STACK_A; try (clear - NRY LENY PY16 PY0 PYC ALO LOS SLO SP1 SP1M NEEDR; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold mpi_core_bitlen_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & -> & ST2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    destruct (cs_stack_step mq hq LBq _ _ _ _ _ m2 (sp1 - MPI_CORE_BITLEN_STACK_A) CST MU2 WM2 MI2 ST2 ltac:(unfold MPI_CORE_BITLEN_STACK_A; clear - SLO SP1 NEEDR; lia) ltac:(unfold MPI_CORE_BITLEN_STACK_A; clear; lia)) as [CST2 UWK].
    pose proof (UWK UW) as UW2. clear MU WM.
    pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(clear - NY; lia)) as BLR.
    set (bl := core_bitlen (md_limbs dY) (md_n dY)) in *.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (land_31 bl) by (clear - BLR; lia).
    pose proof (Z.mod_pos_bound bl 32 ltac:(clear; lia)) as BM.
    zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear - BM; lia).
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 (bl mod 32)) with (Z_to_bv 64 (31 - (31 - bl mod 32))) by (f_equal; clear; lia).
      eapply (dv_M5b K6) with (k := 31 - bl mod 32); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact NF| exact NYX| clear - NX; lia| clear - NY; lia| clear - BM; lia| exact UW2| clear - VAB; lia| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      clear MU WM MU2 WM2.
      destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as (CH2 & SH2 & MI2c & ST2c & HH2).
      pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as OK2.
      unfold A_mpi_div_mpi_C.DCS in CH2.
      repeat (let H := fresh "CHK" in apply Forall_cons_iff in CH2; destruct CH2 as [H CH2]; cbn [fst snd] in H).
      unfold A_mpi_div_mpi_C.dv_sp in CHK.
      pose proof (munch_refl [(sp1, sp1 + 152)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      assert (CST3 : CSTA m3 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 (Z_to_bv 64 0) c120 t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
      { eapply S_cs_store with (mq := m2) (a := sp1) (b := sp1 + 152); try eassumption.
        - clear; lia.
        - left. clear - SP1. lia.
        - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
        - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
        - eapply S_dcs_ok; [exact OK2| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      assert (UW3 : UWCD m3) by (eapply S_uwcd_store; [exact UW2| exact MU| clear; lia]).
      ddestruct NF as (_ & _ & _ & _ & NY1 & _ & _ & _ & _ & VXY).
      unfold dvM6_stmt in K6.
      eapply K6 with (k := 0); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| clear - NX; lia| exact NZ| exact NT| exact SGX| exact SGY| exact VXY| clear; lia| exact UW3| clear - VAB; lia| exact NA98| |].
      + clear - HV NA0 NB0. unfold_bud. lia.
      + clear - HF. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq :=
    (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 48)) c72 (Z_to_bv 64 nx) (Z_to_bv 64 ny)
          (Z_to_bv 64 (32 * (nx - ny))) (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (4 * (nx - ny)))
          t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq).

  (* [comment removed for export] *)
  Definition dvBT : Z := 2 ^ (32 * (md_n dA + 1)).

  (* [comment removed for export] *)
  Definition dvL1_stmt (D : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c72 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f (nx ny k vy : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dY = 1 -> mpd_val dY = vy -> 0 < vy -> 0 <= mpd_val dLX < Z.of_nat D * vy -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    mpd_val dLX < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f804) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@D25900232977.300D25900232977.301D35300034347.241D35300034347.242D60189065437.241D60189065437.242D60189065437.300D60189065437.301L10729413793.2  L12469921329.0  L13483787457.1  L14016578221.12 L14348534914.4  L1504043955.5   L1685717371.0   L1921887436.7   L22647212463.3  L23594257982.3  L24950277677.2  L25543724691.4  L26985680806.1  L27588716945.2  L28506473659.236L28632618922.2  L28860327085.12 L29956516996.0  L30437538938.5  L30778190102.10 L31145622673.2  L31525463372.2  L32284259785.0  L33552778908.3  L33552778908.4  L34080941563.2  L34900022969.236L35663928186.7  L36927858849.2  L38126143619.2  L38259954321.2  L39172636981.0  L39284637285.0  L39834034895.2  L40149985318.4  L40150378917.3  L41417987709.6  L42397482388.6  L45657748817.2  L46561319510.3  L48700858022.1  L50409213458.12 L50996975716.1  L52163114669.12 L52860930961.2  L53024297377.0  L55815189670.1  L57698627611.2  L58498675416.11 L59723910010.4  L59975262609.2  L60098763854.3  L62072417481.2  L62365239714.4  L62377977466.237L62770781818.237L63744388140.2  L65614147016.1  L8929292830.295 L8929292959.236 L9018141615.1   L9356559676.11  L9414061457.2   P27590552406.242P27590552406.300P27590552406.301P28627113325.242P28627113325.300P28627113325.301P31146933846.242P31146933846.300P31146933846.301P38261788758.242P38261788758.300P38261788758.301P45659584406.242P45659584406.300P45659584406.301P52851231062.242P57713046236.242P57713046236.300P57713046236.301P59963990870.242P59963990870.300P59963990870.301P9427955542.242 Q11968186855.242Q1355927177.297 Q1356123914.238 Q15022512148.297Q16827575549.242Q19403150857.297Q20013266709.238Q25925321111.238Q25954107624.242Q28465177121.239Q28465177121.297Q28465177121.298Q32584980358.238Q3421936230.241 Q3421936230.299 Q3421936230.300 Q37991553687.296Q38718005143.238Q39029249300.297Q39029445783.238Q41259708437.238Q45989991432.238Q45989991561.297Q5265442331.240 Q5265442331.298 Q5265442331.299 Q53878910356.297Q56659378566.238Q57228775306.241Q57228775306.299Q57228775306.300Q58026404745.297Q60189065437.242Q64053992584.238Q66561630474.296Q67304840980.297Q67304841109.238Q68235297648.241Q68235297648.242Q68235297648.300Q68235297648.301Q7366734728.238 00001F02\03k05>06M07`0960:L0:T0:U0:Z0;C0;Q0;e0;f0<>0<J0<V0<^0<n0=30=40=Y0=Z0>C0>D0>V0?;0?<0?D0?E0?Q0?]0?g0@I0@^0@f0@m0@n0@o0A00A80AH0AT0AU0Aa0Ab0An0B30B80B=0Bf0Bg0Bh0Bm0Bn0CY0Ca0Cb0Cl0D30DA0D[0E50E>0EC0FG0GH0GL0H70H80IC0JQ0K_0Lj0N80OF0PQ0Q_0Rm0T80UF0VT0W_0Xm0Z;0[F0\40\h0]\0^g0`50aC0bN0cU0d70dO0e40e50eW0f20fB0fC0f\0g?0gb0h20hc0iZ0jQ0k60kF0kk0lF0la0m90m[0n50nY0o=0ob10210`11T12H12j13g14?14a15F15a16D16k17X18E18]S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP3dLX2dY3SPR2F04SP1R2cc2h33HT32HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP3dLX2dY3SPR2F04SP1R2cc2h33HT32HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq2dY3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX3SPR2F03HTq4SP1R2HB5Ha_st5Hl_st2dYS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX3SPR2F04SP1R2HB5Ha_st5Hl_st2dYS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R2cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R2cc2HB5Ha_st5Hl_stS3dLX2dYFS3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3FRb3FRr1f2HFS3dLX2dY3NY13NYX3NRXSS1d3FRb2D03FRr4FRR01f2HFS3dLX2dY3VXYS2sp3sp13SP1S2dY3NRYS3dLX2dY3NYX3BLRS3sp1FS2LF2ra2sp3LFB2FB3sp14gapn2dY3NY13NRYFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1SS3dLX2dY3NY12cc2GYS2dA4PHIb4PHIr3dLX2dY1v3NXA2HV2cc3SNBFS2dY3NY1SS3dLX2dY3NYXS3dLX2dY3NYXS3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn3dLX3NRXS1R3HIA1h2sp2lo3TOP1HS3dLX2dYS2dY2LRFSSS3dLX2dYS3dLX2dY3NY13NYXS3dLX2dY3VXYSS2dA3dLX3NXAFS3dLX2dY3BLRS3sp1S3sp1S3dLXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FSS3sp1FS2dA4PHIb4PHIr5PHIR03dLX2dY1v3NXA2HV2cc3SNBS2dY3NY1FS1R2lo3LOSS2dY2LRS2dA3dLX2LR2PMS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapnS3dLX3NRXS3sp1S2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY3NYX3NXA4NA983SPR2F04SP1R2cc3BLRS2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY3NY13NYX3NXA4NA983SPR2F04SP1RS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS2LF2sp3LFB3sp14gapn3SP12dY2HB5Ha_st5Hl_st3dLXS2LF2sp3LFB2FB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp3LFB2FB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_st3dLXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dY3ALO2F12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF2lo3LFB3sp14gapn3LOCS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccFS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF2sp2lo3LFB3sp14gapn3SP1S2LF3LFB2FB4gapnFS2LF3LFB3sp14gapn4SP1R2HBS2LF3LFB3sp14gapn3dLX2dY4SP1R2cc2HBS2LF3LFB3sp14gapn3dLX2dY4SP1R2cc2HBS2LF3LFB2FB4gapnS2LF2sp2lo3LFB3sp14gapn3SP12dY2HB5Ha_st5Hl_st3dLXS2LF2sp2lo3LFB2FB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2FB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF3LFB2FB4gapnS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF2sp2lo3LFB3sp14gapn3SP1S2LF2sp2lo3LFB3sp14gapn3SP1S2LF2lo3LFB3sp14gapn3LOCS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF3LFB3sp14gapn2HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF3LFB2FB4gapnS2LF2lo3LFB3sp14gapn3LOC2dY2HB5Ha_st5Hl_st3dLXS2LF2lo3LFB2FB3sp14gapn3LOC3dLX2dY2cc2HB5Ha_st5Hl_stS2LF2lo3LFB2FB3sp14gapn3LOC3dLX2dY2cc2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP12dY2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF2sp2lo3LFB3sp14gapn3SP1S2LF3LFB3sp14gapn2dY2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2HB5Ha_st5Hl_st2dYS2LF3LFB2FB3sp14gapn3dLX2dY2cc2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn3dLX2dY2cc2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H PHIR0 FRR0 SHL"] Lemma dv_M6 : (forall D, dvL1_stmt D) -> dvM6_stmt.
  Proof.
    intros KL1. unfold dvM6_stmt. intros until t6. intros CST EAX EAY EAZ EAD OXH OYH OZH OTH NY1 NYX NXA NZ NT SGX SGY VXY HK UW BPOS NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as OKq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. repeat (apply Forall_cons_iff in CHq'; destruct CHq' as [?CK CHq']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & _ & _ & _ & _ & _ & _ & _ & _ & _ & OXs); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & _ & _ & NRX & _) _]. pose proof MLY as [(CY & _ & _ & _ & NRY & _) _]. rewrite EAX in CX, OXs. rewrite EAY in CY, OYs. unfold mpi_cells in CX, CY. unfold MPI_MAX_LIMBS in NRX, NRY.
    pose proof (munch_refl [(sp1, sp1 + 168)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. rewrite ?(zx16_small (md_n dLX)) by (clear - NRX; lia). zstep. rewrite ?(zx16_small (md_n dLX)) by (clear - NRX; lia). rewrite ?(zx16_small (md_n dY)) by (clear - NRY; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 in * by (clear; lia). change (2 ^ 5) with 32 in *.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 (Z_to_bv 64 (md_n dLX)) (Z_to_bv 64 (md_n dY)) (Z_to_bv 64 ((md_n dLX - md_n dY) * 32)) c104 (Z_to_bv 64 k) (Z_to_bv 64 (md_n dLX - md_n dY)) t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 168); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM.

    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. clear MU WM.
    set (cc := (md_n dLX - md_n dY) * 32).
    pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(clear - NY1; lia)) as BLR.
    assert (SNB : shift_l_n cc dY <= md_n dLX).
    { unfold shift_l_n. destruct (Z.ltb_spec (md_n dY * 32) (core_bitlen (md_limbs dY) (md_n dY) + cc)); [| exact NYX].
      apply limbs_of_bits_le; [subst cc; clear - BLR NYX; lia| subst cc; clear - BLR; lia]. }
    unfold mpi_shift_l_stmtA_c in SHL.
    eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m2) (i := 1%nat) (dl := dY) (c := cc) (retpc := 0x9f7d8); try eassumption; try reflexivity; try (rewrite EAY; reflexivity).
    - rewrite EAY. clear. lia.
    - cbv beta. subst cc. change (2 ^ 32) with 4294967296. clear - NYX NRX NY1. lia.
    - unfold shift_l_PHI. clear - HV SNB NXA PHIR0. unfold_bud. lia.
    - cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dY3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      assert (EAY3 : md_addr dY3 = FB + 112) by (rewrite EAL3; exact EAY).
      destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (CH3 & _ & MI3 & ST3 & HH3).
      destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (HT3 & HS3 & _ & HCS3 & _ & _).
      pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as OK3.
      pose proof (hcs_ok asegs R HIA h3) as CSOK3. pose proof (cs_ok_sb _ _ CSOK3) as SB643. pose proof (hcs_stack asegs R HIA h3) as SCS03.
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| rewrite HS3; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      ddestruct RR3 as [[(-> & VY3 & SG3 & NY3)| ->] _].
      + pose proof CH3 as CH3'. unfold A_mpi_div_mpi_C.DCS in CH3'. repeat (apply Forall_cons_iff in CH3'; destruct CH3' as [?CL CH3']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
        pose proof (munch_refl [(sp1, sp1 + 168)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 in * by (clear; lia). change (2 ^ 2) with 4 in *.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        match goal with H : HM asegs R HIA h3 LB3 LF1 m4 |- _ => rename H into HH4 end.
        match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
        match goal with H : stk asegs m4 lo sp1 |- _ => rename H into ST4 end.
        assert (CST4 : CSTA m4 h3 LB3 [dLX; dY3; dZ; dT] dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 (md_n dLX) (md_n dY) k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (v + shift_l_PHI dY cc) (f + shift_l_FR)).
        { eapply S_cs_store with (mq := m3) (a := sp1) (b := sp1 + 168); try eassumption.
          - clear; lia.
          - left. clear - SP1. lia.
          - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY3, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
          - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. subst cc.
            replace (Z_to_bv 64 (32 * (md_n dLX - md_n dY))) with (Z_to_bv 64 ((md_n dLX - md_n dY) * 32)) by (f_equal; clear; lia).
            replace (Z_to_bv 64 (4 * (md_n dLX - md_n dY))) with (Z_to_bv 64 ((md_n dLX - md_n dY) * 4)) by (f_equal; clear; lia).
            replace (Z_to_bv 64 (md_n dY - 1)) with (Z_to_bv 64 (md_n dY + -1)) by (f_equal; clear; lia).
            repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
          - eapply S_dcs_ok; [exact OK3| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
        assert (UW4 : UWCD m4) by (eapply S_uwcd_store; [exact UW3| exact MU| clear; lia]).
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 1%nat) (d := dY3) as (_ & NSY3 & _); try eassumption; [reflexivity|].
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (shift_l_n_ge cc dY ltac:(subst cc; clear - NYX; lia) ltac:(clear - NY1; lia)) as GY.
        assert (P2 : 0 < 2 ^ cc) by (apply Z.pow_pos_nonneg; [clear; lia| subst cc; clear - NYX; lia]).
        assert (VY3P : 0 < mpd_val dY3) by (rewrite VY3; clear - VXY P2; nia).
        assert (XBD : mpd_val dLX < dvBT).
        { rewrite (val_lvalA _ _ _ MLX4 SGX). pose proof (lval_range (md_limbs dLX) (md_n dLX) ltac:(clear - NY1 NYX; lia)) as LR. unfold dvBT.
          assert (PM : 2 ^ (32 * md_n dLX) <= 2 ^ (32 * (md_n dA + 1))) by (apply Z.pow_le_mono_r; clear - NXA NY1 NYX; lia). clear - LR PM. lia. }
        assert (YBD : mpd_abs dY3 < 2 ^ (32 * md_n dLX)).
        { rewrite <- (mpd_val_abs dY3 ltac:(left; rewrite SG3; exact SGY)). rewrite VY3. rewrite (val_lvalA _ _ _ MLY SGY).
          pose proof (lval_range (md_limbs dY) (md_n dY) ltac:(clear - NY1; lia)) as LR.
          rewrite Z.abs_eq by (apply Z.mul_nonneg_nonneg; [clear - LR; lia| apply Z.pow_nonneg; clear; lia]).
          subst cc. replace (32 * md_n dLX) with (32 * md_n dY + (md_n dLX - md_n dY) * 32) by (clear; lia). rewrite Z.pow_add_r by (clear - NY1 NYX; lia).
          apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; [clear; lia| clear - NYX; lia]| clear - LR; lia]. }
        eapply (KL1 (S (Z.to_nat (mpd_val dLX)))) with (vy := mpd_val dY3) (k := k); [exact CST4| exact EAX| exact EAY3| exact EAZ| exact EAD| exact OXH| | exact OZH| exact OTH| exact NY1| exact NYX| exact NXA| clear; lia| rewrite NY3; exact GY| exact NZ| exact NT| rewrite SG3; exact SGY| reflexivity| exact VY3P| | exact HK| exact UW4| exact BPOS| exact NA98| | | exact XBD| exact YBD].
        * eapply out_heapA; [exact ML3| exact NSY3| rewrite NY3; clear - GY NY1; lia].
        * assert (E : Z.of_nat (S (Z.to_nat (mpd_val dLX))) = mpd_val dLX + 1) by (clear - VXY; lia).
          split; [clear - VXY; lia|]. rewrite E. clear - VXY VY3P. nia.
        * unfold shift_l_PHI. clear - HV SNB NXA. unfold_bud. lia.
        * clear - HF. unfold_bud. lia.
      + pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| exact EAY3| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * unfold shift_l_PHI. clear - HV SNB NXA. unfold_bud. lia.
        * clear - HF. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis CMP : mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L13969782048.8 L27940637589.11L29428324939.11L3482559548.11 L34979112605.7 L35663928186.7 L38235734261.1 L53035543379.8 L60098763854.3 L9080220944.4  L9356559676.11 00000E00l01S02?02Z02o03303H03R03a04LS1R2lo3LOS2dj3ALO3PJCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACPS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HS2loS1R2lo3LOS2di3ALO3PICS1R2lo3LOSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 CMP"] Lemma call_cmp_ll : forall mq hq LBq ls CS0 v f i j di dj (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some di -> nth_error ls j = Some dj ->
    md_own di = LHeap -> md_own dj = LHeap -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (md_addr dj) ->
    (forall m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m2 hq LBq ls dX CS0 DV_FSH v f -> (UWCD mq -> UWCD m2) ->
       aevtA asegs (KF asegs R HIA hq mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 (Z.sgn (mpd_val di - mpd_val dj))) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_CMP_MPI_E) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI NJ OI OJ RPC RPE -> -> K. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := di) as (MI & _ & _ & _ & _ & _ & HFI & _ & _ & ASI & OI'); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := j) (d := dj) as (MJ & _ & _ & _ & _ & _ & HFJ & _ & _ & ASJ & OJ'); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & _). ddestruct (HFJ OJ) as (PJ0 & PJC & INJ & _).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E in CMP. unfold A_MPI_CMP_MPI_E.
      eapply CMP with (CS := hcs asegs R HIA hq) (LB := LBq) (dX := di) (dY := dj) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (intros _; assumption).
      all: try (exact (art_alwf asegs R HIA)).
      all: try (exact (hm_abase asegs R HIA hq LBq LF1 mq HHq)).
      all: try (intros _; eapply hm_aobj_block; [exact HHq| eassumption]).
      all: try (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
      all: try (destruct ASI as [KK|KK]; [left; exact KK| right; exact KK]).
      all: try (destruct ASJ as [KK|KK]; [left; exact KK| right; exact KK]).
      all: try (intros _; left; clear - PIC PJC ALO LOS; lia).
      all: try (clear - LOS ALO ACP SLO SP1 SP1M NEEDR; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    destruct (cs_stack_step mq hq LBq _ _ _ _ _ _ lo CST MU2 WM2 MI2 ST2 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST2 UWK].
    eapply K; [exact CST2| exact UWK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L28553935321.2L58185413033.200000800@S2di3N1IS2dj3N1J". (* [comment removed for export] *)
  #[using="NEEDR ra LOS SLO TOP LFB XW gapn SP1 FRSH LOC CSP FN64"] Lemma locals_apart : forall mq hq LBq ls dW CS0 v f i j di dj, CSTA mq hq LBq ls dW CS0 DV_FSH v f ->
    nth_error ls i = Some di -> nth_error ls j = Some dj -> i <> j ->
    (md_addr di + 16 <= md_addr dj \/ md_addr dj + 16 <= md_addr di)
    /\ (md_own di = LHeap -> md_own dj = LHeap -> md_p di + 4 * md_n di <= md_p dj \/ md_p dj + 4 * md_n dj <= md_p di).
  Proof.
    intros mq hq LBq ls dW CS0 v f i j di dj CST NI NJ NE.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := di) as (_ & _ & _ & _ & _ & _ & HFI & _); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := j) (d := dj) as (_ & _ & _ & _ & _ & _ & HFJ & _); try eassumption.
    unfold A_mpi_client2.cstateA in CST. ddestruct CST as (HH & _ & _ & _ & _ & SA & LA & _).
    split; [exact (SA i j di dj NI NJ NE)|]. intros OI OJ.
    ddestruct (HFI OI) as (_ & _ & INI & N1I & _). ddestruct (HFJ OJ) as (_ & _ & INJ & N1J & _).
    destruct (hm_apart asegs R HIA hq LBq LF1 mq HH) as [_ BA].
    pose proof (LA i j di dj NI NJ NE OI OJ) as PNE.
    pose proof (blocks_apart_neq _ (md_p di, 4 * md_n di) (md_p dj, 4 * md_n dj) BA ltac:(apply in_or_app; left; exact INI) ltac:(apply in_or_app; left; exact INJ)
                  ltac:(intros E; injection E as E1 _; exact (PNE E1)) ltac:(cbn; clear - N1I; lia) ltac:(cbn; clear - N1J; lia)) as K.
    cbn [fst snd] in K. exact K.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis ASNG : add_sub_mpi_ng_stmtA_o (-1) asegs R HIA A_ADD_SUB_MPI.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L12128799109.1 L19980016842.7 L25148064707.3 L35590224338.3 L39261961171.9 L39272446419.9 L4223562214.6  L4781719053.2  L50313707442.2 L52101693566.17L59308631662.4 L60162046265.6 L6188244917.6  L62037211595.7 L6203936179.1  L66151427842.16L66668349941.1 L9356559676.11 L9838743115.2  00000300K00V00a01?01^02202802@03<03J03^04304N04S04o05205]05gS1fS1R3HIA1h2sp3TOP3sp13SP1S2di2dj3VJIS2di2dj3VIJS1R3HIA1h4PHIb3BUD2hq1v2HV3HVqS1R3HIA1h3FRb4BUDF2hq1f2HF4HFRqS1R2FB2dj3DJF3ALO2F1S1d2D0S2di3VIIS1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS2di2dj3ABL2KKS1R2FB2di3DIF3ALO2F1S1R2sp2lo3SLO3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF ASNG"] Lemma call_sub_ng_ll : forall mq hq LBq ls CS0 v f i j di dj (retpc : Z)
      t0 t1 t2 a0v a1v a2v a3v a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some di -> nth_error ls j = Some dj -> i <> j ->
    md_addr di + 16 <= FB + 256 -> md_addr dj + 16 <= FB + 256 ->
    md_own di = LHeap -> md_own dj = LHeap -> md_sg di = 1 -> md_sg dj = 1 -> mpd_abs dj <= mpd_abs di ->
    UWCD mq -> v <= PHIb -> f <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (md_addr di) -> a2v = Z_to_bv 64 (md_addr dj) -> a3v = Z_to_bv 64 (-1) ->
    (forall m3 h3 LB3 di' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls di') dX CS0 DV_FSH v f -> add_sub_mpi_R (-1) LBq di di dj r di' -> mpd_at asegs m3 LB3 di' -> md_addr di' = md_addr di -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2v a3v a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_ADD_SUB_MPI) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI NJ NE DIF DJF OI OJ SGI SGJ ABL UW HV HF RPC RPE -> -> -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := i) (d := di) as (MI & NSI & XWI & LLI & CRI & CRLI & HFI & SLI & _ & ASI & OIs); try eassumption.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := j) (d := dj) as (MJ & NSJ & _ & LLJ & CRJ & CRLJ & HFJ & SLJ & _ & ASJ & OJs); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _). ddestruct (HFJ OJ) as (PJ0 & PJC & INJ & N1J & _).
    destruct (locals_apart _ _ _ _ _ _ _ _ i j di dj CST NI NJ NE) as [SAP LAP].
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INI SLI) as VII.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INJ SLI) as VIJ.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dj) _ _ HHq INI SLJ) as VJI.
    pose proof MI as [(_ & _ & AI0 & _) _]. pose proof MJ as [(_ & _ & AJ0 & _) _].
    pose proof ASNG as SPA'. unfold add_sub_mpi_ng_stmtA_o in SPA'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPA' with (h := hq) (LB := LBq) (LF := LF1) (dX := di) (dA := di) (dB := dj) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact MI | exact NSI | exact XWI | exact LLI | exact CRI | exact CRLI | exact CRJ | exact CRLJ | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | reflexivity
              | (left; exact MJ) | (rewrite HSq; exact UW)
              | lazymatch goal with
                | |- mpd_sep di di => left; reflexivity
                | |- mpd_sep di dj => right; exact SAP
                | |- _ * md_sg dj = - md_sg di => rewrite SGI, SGJ; reflexivity
                | |- mpd_abs dj <= mpd_abs di -> _ => intros _; clear; lia
                | |- mpd_abs di < mpd_abs dj -> _ => intros KK; exfalso; clear - KK ABL; lia
                | |- opnd_sep di di _ _ => split; [intros _; clear - VII; lia| split; [intros _; clear - VII; lia| split; [left; reflexivity| split; [exact ASI| exact LLI]]]]
                | |- opnd_sep di dj _ _ => split; [intros _; clear - VIJ; lia| split; [intros _; clear - VJI; lia| split; [right; right; right; exact (LAP OI OJ)| split; [exact ASJ| exact LLJ]]]]
                | |- lo <= sp1 - _ - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ di => split; [exact OIs| intros EO; exfalso; exact (NSI EO)]
                | |- mpd_aobjA _ _ _ _ dj => split; [exact OJs| intros EO; exfalso; exact (NSJ EO)]
                | |- md_own di = LStatic -> _ => intros EO; exfalso; exact (NSI EO)
                | |- md_own dj = LStatic -> _ => intros EO; exfalso; exact (NSJ EO)
                | |- _ <> _ -> _ => intros KK; exfalso; apply KK; reflexivity
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold add_sub_PHI0; clear - HVq BUD HV; lia
                | |- uw_obj _ (md_addr di) 16 _ => left; split; [clear - DIF F1 ALO; lia| clear - D0; lia]
                | |- uw_obj _ (md_addr dj) 16 _ => left; split; [clear - DJF F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold add_sub_FR0; clear - HFRq BUDF HF; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "SUB-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & di3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls di3) dX CS0 DV_FSH (v + 0) (f + 0)).
    { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := i) (dX := di) (mq := mq) (hq := hq); try eassumption.
      destruct RR3 as [_ (_ & _ & KK & _)]. exact KK. }
    replace (v + 0) with v in CST3 by (clear; lia). replace (f + 0) with f in CST3 by (clear; lia).
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DIF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition set_limbsA (d0 : mpd) (xs : list word) : mpd := mkMPD (md_addr d0) (md_sg d0) (md_n d0) (md_p d0) xs (md_pad d0) (md_own d0).

  (* [comment removed for export] *)
  Definition dvM8_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c72 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f (nx ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9fae0) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@C7096915042.252 D33876909647.251D63873442836.251K66327680928.252L13843160408.5  L14940460802.5  L17162795167.5  L19133426325.6  L24599071338.248L27153772539.5  L29832375856.1  L32170472955.239L35663928186.7  L39723389345.0  L40374229935.6  L46190619535.240L47887867615.6  L49168952290.8  L49848821868.15 L53517041937.239L5376886168.7   L57625758213.5  L57652312495.1  L59308550125.6  L59310648043.7  L59310730320.5  L59310730321.8  L59667784614.1  L60098763854.3  L61798049332.5  L62018535662.1  L63883836664.5  L66199197884.5  L66330468140.4  L8532400182.5   L8927066272.240 L8927066273.239 L8929159528.243 L9018141615.1   L9356559676.11  P61800574648.253P66327680928.252Q10812129647.247Q11801279589.251Q12386747392.243Q13311529494.247Q13313446495.247Q13315708651.247Q18654822746.247Q19991027068.253Q20535455645.243Q24839097629.243Q26295627581.247Q31205954960.253Q3375676648.253 Q33874924623.252Q33877164610.247Q33889765055.247Q38968870528.243Q40217825408.253Q45057547415.253Q45987633792.243Q48467890406.253Q49698585326.251Q50458135125.247Q51135677050.250Q51336009840.244Q5389729424.247 Q5392185892.247 Q5396397785.247 Q60685804113.247Q60695847448.247Q60695898138.244Q60698371756.247Q63871233556.252Q67302478109.243Q8945721240.244 00000101L02]02^03403H03Z04105705D05H06[07007107G08:08M08l09d0:P0:h0;80;<0;P0;k0<=0<X0<\0<f0<g0<j0=<0=N0=O0=a0?C0@i0BK0BO0C:0DM0DN0EF0Eo0F`0Fa0Fb0Fc0GQ0GR0HF0I:0I`0Ia0Ib0J]0KU0LM0M>0M?0M@0N10N20Nf0OL0P:0Q20Q30Q40Q50Q_0RI0S30S]0TN0UB0UhFS2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3SPR2F03idx2wv4SP1R2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy3NY12VX3SPR2F03idx2wv4SP1R2Z03PZ03KW1FS4PHIb4PHIr5PHIR01v2HVS3dLX2nx3NXL3dX43NK4S2dZ2nx2ny3idx3IDXS2dZ2nx2ny4LENZ3idx3IDXS2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy2VX3SPR2F04SP1R2Z03PZ03idxS1D3dLX2vy2VXS2dZS1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2vy2NZ2VX3ACV3SPR2F04SP1R2Z03PZ03PZCS1R3HIA1h2sp2lo3TOP1HSS2dA2nx2ny3NY13NYX3NXAS2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy2VX3idxS1D3dLX2dY2vy2VY2VXS3dLX2nx2ny3NY13NYX3NXL3dX43NK4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dZ2nx2ny3ALO3idx3PZC3IDXS2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2vy2VXS1d3FRb2D03FRr4FRR01f2HFS3dLX2vy3VY03XBDS2FBS1D3dLX2vy3VY02VX2NNS2dZ2nx2ny4LENZ3idx3IDX3NTHS2dZ2nx2ny3NYX3KW1S2dZ2nx2ny3NYX1H2H03KW23PZ0S2dZS1R2lo3LOSFS1RS2dZ2nx2ny3idx3IDXS2dZ2nx2ny3idx3IDXFS2dZ2nx2ny3idx3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3ACV3SPR2F04SP1R2Z03PZ03PZC3KW1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NYX3NXA2NZ2VX3ACV3SPR2F04SP1R2Z03PZ03PZC3KW1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3ACV3SPR2F04SP1R2Z03PZ03PZC3KW1S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11D3dLX2dZ2nx2ny2vy2VX3ALO3idx2wv3PZC3IDXFS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx2wvS2LF2lo3LFB3sp14gapn3LOC1D3dLX2dZ2nx2ny2vy2VX3idxFFFS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3PZ03idx3KW1FS2LF2sp2lo3LFB3sp14gapn3SP11D3dLX2dZ2nx2ny2vy2VX3idxS2LF2sp2lo3LFB3sp14gapn3SP11D3dLX2dZ2nx2ny2vy2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idxFFS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idx2wvS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF2lo3LFB3sp14gapn3LOC1D3dLX2dZ2nx2ny2vy2VX3idxFFS2LF2lo3LFB3sp14gapn3LOC1D3dLX2dZ2nx2ny2vy2VX3idxFS1R2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3ACV3idx3PZC3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx3PZ03KW1S2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxFFFS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx3KW1S2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx3KW1S2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx3KW1S2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx3KW1S2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx2wv3KW1S2LF2sp2lo3LFB3sp14gapn3SP11D3dLX2dZ2nx2ny2vy2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF PHIR0 FRR0 NA0 ASNG"] Lemma dv_L1body : forall D, dvL1_stmt D ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c72 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq v f (nx ny k vy : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dY = 1 -> mpd_val dY = vy -> 0 < vy -> vy <= mpd_val dLX < Z.of_nat (S D) * vy -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    mpd_val dLX < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f814) fc None mq (seg_rom asegs)).
  Proof.
    intros D IH. intros until t6. intros CST EAX EAY EAZ EAD OXH OYH OZH OTH NY1 NYX NXA NXL NYL NZ NT SGY VY VY0 VX HK UW BPOS NA98 HV HF XBD YBD.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (CWZ : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dZ) (4 * md_n dZ))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
    set (idx := nx - ny).
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYX NXA; lia).
    destruct (nth_error (md_limbs dZ) (Z.to_nat idx)) as [wz|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ IDX; lia].
    pose proof (munch_refl [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. apply Forall_cons_iff in CHq'. destruct CHq' as [SPC _]. cbn [fst snd] in SPC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    zstep. zstep. zstep. zstep. clear SPC.
    zstep. if_cases KW1; zify_cond KW1; [exfalso; clear - KW1 NYX; lia|].
    zstep. zstep. zstep. zstep. if_cases KW2; zify_cond KW2;
      [exfalso; clear - KW2 PZ0 NYX; repeat match type of KW2 with context [?a <? ?b] => revert KW2; case (Z.ltb_spec a b); intros ? KW2 end;
       cbn [Z.b2z] in KW2; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in KW2; lia|].
    zstep. zstep. shadow_chk OPZ (4 * (nx - ny) + md_p dZ) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wz _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep.
    pose proof (u32arr_store_ok asegs mq (md_p dZ) (md_limbs dZ) idx _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dZ) (md_limbs dZ) idx vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : rw_cells asegs m3 (sp1 + 184) _ |- _ => rename H into CZ3 end.
    set (dZ3 := set_limbsA dZ (upd (md_limbs dZ) (Z.to_nat idx) wv)).
    assert (MLZ3 : mpd_at asegs m3 LBq dZ3).
    { split; [| exact SGZ]. unfold dZ3, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAZ.
      split; [exact CZ3|]. split; [rewrite <- EAZ; exact Z8|]. split; [rewrite <- EAZ; exact Z0|]. split; [rewrite upd_length; exact LENZ|]. split; [exact NRZ|].
      rewrite OZH. split; [exact NZ1|]. split; [exact INZ|]. split; [exact PZ16| exact UAZ']. }
    assert (HPA3 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] mq m3).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m3 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPZ)| clear - IDX; lia| clear - IDX; lia]. }
    assert (CST3 : CSTA m3 hq LBq (set_nth 2 [dLX; dY; dZ; dT] dZ3) dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dZ) (WX := [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OZH| clear - IDX; lia]| apply Forall_nil]. }
    cbn [set_nth] in CST3.
    assert (UW3 : UWCD m3).
    { eapply uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - IDX PZC ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    clear MU WM.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. clear MU WM.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 0%nat) (d := dLX) as (MLX3 & _); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 1%nat) (d := dY) as (MLY3 & _); try eassumption; [reflexivity|].
    pose proof MLX3 as [_ SGXd].
    assert (SGX : md_sg dLX = 1).
    { destruct SGXd as [K|K]; [exact K| exfalso]. unfold mpd_val in VX. rewrite K in VX. pose proof (limbs_val_nonneg (md_limbs dLX)) as NN. fold (mpd_abs dLX) in VX. unfold mpd_abs in VX. clear - VX VY0 NN. lia. }
    assert (ABL : mpd_abs dY <= mpd_abs dLX).
    { unfold mpd_val in VX, VY. rewrite SGX in VX. rewrite SGY in VY. unfold mpd_abs. clear - VX VY. lia. }
    eapply (call_sub_ng_ll m3 hq LBq _ _ v f 0%nat 1%nat dLX dY 0x9f868); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAY; reflexivity).

    - discriminate.
    - rewrite EAX. clear. lia.
    - rewrite EAY. clear. lia.
    - clear - HV PHIR0. unfold AVOL_CALL in PHIR0. lia.
    - clear - HF FRR0 D0. unfold fr_charge in FRR0. lia.
    - clear. lia.
    - intros m4 h4 LB4 dX4 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
      pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV4.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      assert (EAX4 : md_addr dX4 = FB + 80) by (rewrite EAL4; exact EAX).
      ddestruct RR4 as [[(-> & VX4)| ->] (_ & _ & _ & NK4)].
      + (* [comment removed for export] *)
        zstep. zstep.
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 0%nat) (d := dX4) as (_ & NSX4 & _); try eassumption; [reflexivity|].
        unfold dvL1_stmt in IH.
        eapply IH with (nx := nx) (ny := ny) (k := k) (vy := vy); [exact CST4| exact EAX4| exact EAY| exact EAZ| exact EAD| | exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| exact NXA| clear - NXL NK4; lia| exact NYL| exact NZ| exact NT| exact SGY| exact VY| exact VY0| | exact HK| exact UW4| exact BPOS| exact NA98| exact HV| exact HF| rewrite VX4, VY; clear - XBD VY0; lia| exact YBD].
        * eapply out_heapA; [exact ML4| exact NSX4| clear - NXL NK4 NY1 NYX; lia].
        * rewrite VX4, VY. rewrite Nat2Z.inj_succ in VX. clear - VX VY0. lia.
      + (* [comment removed for export] *)
        unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep. zstep. zstep.
        eapply dv_ERR16; [exact CST4| reflexivity| exact EAX4| exact EAY| exact EAZ| exact EAD| exact UW4| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L27322058401.0L36799126446.5L36799158313.5L40148281766.4L59308944635.400000100A00Q00^00iSS1D3dLX2vy2VX2GTS1D3dLX2vy2VX2EQS1D3dLX2vy2VXS3dLX2vy2VX". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF PHIR0 FRR0 NA0 CMP ASNG"] Lemma dv_LOOP1 : dvM8_stmt -> forall D, dvL1_stmt D.
  Proof.
    intros K8. induction D as [|D IH]; unfold dvL1_stmt; intros until t6;
      intros CST EAX EAY EAZ EAD OXH OYH OZH OTH NY1 NYX NXA NXL NYL NZ NT SGY VY VY0 VX HK UW BPOS NA98 HV HF XBD YBD; [exfalso; clear - VX VY0; lia|].
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    eapply (call_cmp_ll mq hq LBq [dLX; dY; dZ; dT] _ v f 0%nat 1%nat dLX dY 0x9f810); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAY; reflexivity); [clear; lia|].
    intros m2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST2 UWK. pose proof (UWK UW) as UW2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct (Z.sgn_spec (mpd_val dLX - mpd_val dY)) as [(GT & ->)|[(EQ & ->)|(LT & ->)]].
    3: { (* [comment removed for export] *)
      zstep. unfold dvM8_stmt in K8.
      eapply K8 with (nx := nx) (ny := ny) (k := k); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| exact NXA| exact NXL| exact NYL| exact NZ| exact NT| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF| rewrite Z.abs_eq by (clear - VX; lia); exact XBD| exact YBD]. }
    - zstep. eapply (dv_L1body D IH) with (nx := nx) (ny := ny) (k := k) (vy := vy); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| exact NXA| exact NXL| exact NYL| exact NZ| exact NT| exact SGY| exact VY| exact VY0| | exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF| exact XBD| exact YBD].
      rewrite VY in GT. clear - GT VX. lia.
    - zstep. eapply (dv_L1body D IH) with (nx := nx) (ny := ny) (k := k) (vy := vy); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| exact NXA| exact NXL| exact NYL| exact NZ| exact NT| exact SGY| exact VY| exact VY0| | exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF| exact XBD| exact YBD].
      rewrite VY in EQ. clear - EQ VX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis SHR : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.

  (* [comment removed for export] *)
  Definition dvFIN_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c64 c72 c80 c88 c96 c104 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSM c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (FB + 32)) c64 c72 c80 c88 c96 c104 (Z_to_bv 64 k) c120
               t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < (2 * md_n dA + 2) * dvBT ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6) F (Z_to_bv 64 0xa0274) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition dvLOOP_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c48 c80 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (nx ny k : Z)
           xra t0 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSM c0 c8 c16 (Z_to_bv 64 65537) (Z_to_bv 64 4294967295) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) c48
               (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 48)) (Z_to_bv 64 (2 ^ 61)) c80 (Z_to_bv 64 ((ny - 2) * 4))
               (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 k) c120
               t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny < nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < dvBT -> mpd_abs dY < 2 ^ (32 * ny) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 (Z_to_bv 64 nx) t2 (Z_to_bv 64 (nx - 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fb44) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01S0@D35300034347.285D35300034347.286D60189065437.285D60189065437.286L12251719832.2  L13483787457.1  L14016578221.12 L14933635412.4  L16500284193.0  L17786231048.2  L19980016842.7  L21117053682.11 L23594257982.3  L26985680806.1  L27588716945.2  L28632618922.2  L28860327085.12 L31145622673.2  L32482764547.25 L32703425643.1  L34080941563.2  L34306769533.3  L34811591499.25 L3482839849.25  L35663928186.7  L37021784866.276L38235734261.1  L38259954321.2  L3883892771.1   L39172636981.0  L4218649811.277 L42967148590.276L45174325948.1  L45657748817.2  L47990265982.2  L48700858022.1  L49516137587.3  L50409213458.12 L50574758523.3  L50574758523.4  L51841720889.1  L52163114669.12 L5413320392.1   L55815189670.1  L57698627611.2  L59311074662.12 L59975262609.2  L60098763854.3  L62018535662.1  L64235851075.12 L65271643703.0  L65614147016.1  L68148167523.277L9080220944.4   L9356559676.11  P27590552406.285P27590552406.286P28627113325.285P28627113325.286P31146933846.285P31146933846.286P38261788758.285P38261788758.286P45659584406.285P45659584406.286P57713046236.285P57713046236.286P59963990870.285P59963990870.286Q12388912010.280Q13394437384.282Q1355927048.282 Q15022709143.280Q15236383893.282Q15902156936.282Q20013136780.281Q20013594135.238Q20537614359.280Q20614745749.282Q21912967688.282Q28465177121.282Q28465177121.283Q3421936230.284 Q3421936230.285 Q39029249429.282Q41259381015.280Q5265442331.283 Q5265442331.284 Q57228775306.284Q57228775306.285Q58026207754.280Q64053858321.281Q64054320522.238Q67148022549.282Q68235297648.285Q68235297648.286Q7366406794.280 Q7526424981.282 Q9874441992.282 00001Y03B04k06T06\06a07J07R07S07Z08208\08h08m08n08o09X09Y0:90:=0:G0:R0;_0<\0=10>V0>Z0>[0>_0>`0>a0@=0@A0@B0@J0@O0@Y0@^0@i0A40A80Aa0Af0Ak0Al0Am0An0B80B;0BP0BQ0BV0Cn0D=0Dh0FB0G\0I60JP0Kj0MD0N^0P80QR0Rl0Si0Tf0V@0WZ0XH0Y60Yd0ZU0[F0\40\e0]J0^;0^l0_Z0`I0a80b80c80ci0dZ0eJ0f:0g70h40hb0iP0j20jc0kY0lO0m=0mn0n\S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY2nx2ny3SPR2F03HTq4SP1R2Y03PY03x144LEN22HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY2nx2ny3SPR2F03HTq4SP1R2Y03PY03x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3SPR2F04SP1R2Y03PY03x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3SPR2F04SP1R2Y03PY03x144LEN22HB5Ha_st5Hl_stS2lo3sp1S3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2ny3NY1SS2nx2nyS1R3HIA1h2sp3TOP3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO3PYCS2sp3sp13SP1S3sp1FFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1R2sp2lo3SLO3sp13SP12dY3NRA3PY0S2dYS3sp14gapnS2FB2dY3PYFS1R5NEEDR2sp2lo3LOS3SLO2dA3sp13SP12dY2nx2ny3NY13NYX3NXA4NA983ALO4NY1'3PY03PYCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4NY1'4PY163PY03PYCS1R3HIA1h2sp2lo3TOP1HS1R2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY2nx2ny3NY13NYX3NXA3NYL4NA983ACV3SPR2F04SP1R2Y03PY03PYC3x144LEN2S2loFS2dYSFS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3NY13NYX3NYL3ACV3SPR2F04SP1R2Y03PY03PYC3x144LEN22KTS2dYFS2dA3NA0S3sp1S2nx2ny2KTS3sp1S2nx2ny3NYXS2nx2ny3NYXS2dYS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S3sp1FFFS1R2lo3LOSS1RS1R2lo3LOS2dY3ALO3PYCSS3sp1S1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3NY13NYL3ACV3SPR2F04SP1R2Y03PY03PYC3x144LEN22KTS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13x144LEN22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nxS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF3LFB3sp14gapn3dLX2dY2nx2ny4SP1R3x144LEN22HBS2LF3LFB3sp14gapn3dLX2dY2nx2ny4SP1R3x144LEN22HBS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF3LFB3sp14gapn3dLX2dY2nx2ny3x144LEN22HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2nx2ny3x144LEN22HB5Ha_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nxS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF3LFB3sp14gapn3dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2nx2ny3x144LEN22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3x144LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3x144LEN2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 SP1M GAP F64 FRSH CFB ESF LOC CSP FN64 FB8 NA0 SHR"] Lemma dv_M8 : dvFIN_stmt -> dvLOOP_stmt -> dvM8_stmt.
  Proof.
    intros KFIN KLOOP. unfold dvM8_stmt. intros until t6. intros CST EAX EAY EAZ EAD OXH OYH OZH OTH NY1 NYX NXA NXL NYL NZ NT HK UW BPOS NA98 HV HF XBD YBD.
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
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & NSY & _ & LLY & _ & _ & HFY & _ & Y8 & ASY & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & Y0 & LENY & NRY & OWY) SGYd]. rewrite OYH in OWY. ddestruct OWY as (NY1' & INY & PY16 & UAY). unfold MPI_MAX_LIMBS in NRY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_shift_r_stmtA, A_MPI_SHIFT_R_E in SHR.
      eapply SHR with (h := hq) (LB := LBq) (LF := LF1) (dX := dY) (count := 32 * (nx - ny)) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (rewrite EAY; reflexivity).
      all: try (eapply client_wrange_block; [apply in_or_app; left; exact INY| clear; lia| clear; lia]).
      all: try (rewrite HTq; clear - SP1 TOP; lia).
      all: try (intros _; rewrite EAY; clear - PYF; lia).
      all: try (intros _; clear - PYC ALO LOS SLO SP1 NEEDR LOC; lia).
      all: try (rewrite EAY; clear - F1 ALO LOS SLO SP1 NEEDR LOC; lia).
      all: try (clear - NRY NY1' LENY PY16 PY0 PYC ALO LOS SLO SP1 SP1M NEEDR NRA NY1 NYX NXA NA98; first [lia| Z.div_mod_to_equations; lia]). }

    cbv beta. intros ms' PO. unfold mpi_shift_r_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2 & MLY2 & LEN2 & LV2 & HH2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    lazymatch type of MLY2 with mpd_at _ _ _ ?dd => set (dY2 := dd) in * end.
    assert (HPA2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(lo, sp1); (md_p dY, md_p dY + 4 * md_n dY)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_cons; [cbn [fst snd]| apply Forall_nil]].
      - eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia].
      - eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPY)| clear; lia| clear; lia]. }
    assert (CST2 : CSTA m2 hq LBq (set_nth 1 [dLX; dY; dZ; dT] dY2) dX (DCSL c0 c8 c16 c24 c32 c40 c48 c72 nx ny k t2pad czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dY) (WX := [(lo, sp1); (md_p dY, md_p dY + 4 * md_n dY)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OYH| clear; lia]| apply Forall_nil]]. }
    cbn [set_nth] in CST2.
    assert (UW2 : UWCD m2).
    { eapply uwcd_munch; [exact UW| exact MU2|]. apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_cons; [cbn [snd]; clear - PYC ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]]. }
    assert (YB2 : mpd_abs dY2 < 2 ^ (32 * ny)).
    { unfold mpd_abs at 1. unfold dY2. cbn [md_limbs]. rewrite LV2. fold (mpd_abs dY).
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; [clear; lia| clear - NYX; lia]|]. rewrite <- Z.pow_add_r by (clear - NY1 NYX; lia).
      replace (32 * (nx - ny) + 32 * ny) with (32 * nx) by (clear; lia). exact YBD. }
    assert (BTP : 0 < dvBT) by (unfold dvBT; apply Z.pow_pos_nonneg; [clear; lia| clear - NA0; lia]).
    clear SPC MU2 WM2.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as (CH2 & _ & _ & _ & _).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as OK2.
    pose proof CH2 as CH2'. unfold A_mpi_div_mpi_C.DCS in CH2'. repeat (apply Forall_cons_iff in CH2'; destruct CH2' as [?CK CH2']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
    pose proof (munch_refl [(sp1, sp1 + 168)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - NY1 NYX NXA NA98; lia).

    - (* [comment removed for export] *)
      unfold dvFIN_stmt in KFIN.
      eapply KFIN with (k := k); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact HK| exact UW2| exact BPOS| exact HV| exact HF| clear - XBD BTP NA0; nia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite ?Z.shiftl_mul_pow2 in * by (clear; lia). change (2 ^ 2) with 4 in *.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
      assert (CST3 : CSTA m3 hq LBq [dLX; dY2; dZ; dT] dX
                (DCSM c0 c8 c16 (Z_to_bv 64 65537) (Z_to_bv 64 4294967295) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) c48
                      (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 48)) (Z_to_bv 64 (2 ^ 61)) (Z_to_bv 64 nx) (Z_to_bv 64 ((ny - 2) * 4))
                      (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (4 * (nx - ny)))
                      t2pad (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
      { eapply S_cs_store with (mq := m2) (a := sp1) (b := sp1 + 168); try eassumption.
        - clear; lia.
        - left. clear - SP1. lia.
        - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; unfold dY2; cbn [md_addr]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
        - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp.
          replace (Z_to_bv 64 ((ny - 2) * 4)) with (Z_to_bv 64 ((ny + -2) mod 18446744073709551616 * 4))
            by (apply Z_to_bv_eqm; change (2 ^ 64) with 18446744073709551616; rewrite Z.mul_mod_idemp_l by (clear; lia); f_equal; clear; lia).
          repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
        - eapply S_dcs_ok; [exact OK2| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      assert (UW3 : UWCD m3) by (eapply S_uwcd_store; [exact UW2| exact MU| clear; lia]).
      replace (Z_to_bv 64 (nx + -1)) with (Z_to_bv 64 (nx - 1)) by (f_equal; clear; lia).
      unfold dvLOOP_stmt in KLOOP.
      eapply KLOOP with (nx := nx) (ny := ny) (k := k); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| clear - KT; lia| exact NXA| exact NXL| exact NYL| exact NZ| exact NT| exact HK| exact UW3| exact BPOS| exact NA98| exact HV| exact HF| exact XBD| exact YB2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE BE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SXA IA2 IB2 ESA ESB PHIR0 FRR0 BM_PHI BM_FR NA0 NB0 OA OB CALLOC LSETNG GROW BITLEN SHL CMP ASNG SHR"] Lemma dv_M : dvFIN_stmt -> dvLOOP_stmt ->
    A_mpi_div_mpi_S_c24.dv_MAIN_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn.
  Proof.
    intros KFIN KLOOP. unfold A_mpi_div_mpi_S_c24.dv_MAIN_stmt. intros until t6. intros CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 UW BPOS BLE.
    eapply (dv_MAIN (dv_M2 (dv_M3 (dv_M4 (dv_M4b (dv_M5 (dv_M6 (dv_LOOP1 (dv_M8 KFIN KLOOP)))))))));
      [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| exact OX0| exact OY0| exact OZ0| exact OT0| exact UW| exact BPOS| exact BLE].
  Qed.

  End Fr.
  End Call.
End WalkM.
