(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_div_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_core_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24.
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
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF PHIR0 FRR0"] Lemma dv_ERR : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f (r : Z)
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    UWCD mq -> -2^31 < r < 0 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f700) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST EAX EAY EAZ EAD UW HR HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    zstep.
    eapply C_CLEAN_X with (r := r); [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact UW| clear - HR; lia| intros K; exfalso; clear - K HR; lia| unfold div_mpi_nz; apply Z.le_max_l| |].
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
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    lfacts dA dLX -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> v + dvV2 <= PHIb -> f + dvF2 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 B) s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f41c) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@D35300034347.198D35300034347.199D60189065437.198D60189065437.199L11144352574.3  L1835983057.4   L22369917295.8  L23298740641.0  L26988105723.2  L28632618922.2  L29956516996.0  L31813175040.4  L34285487197.7  L35663928186.7  L36757749421.12 L38060875949.12 L42888674241.1  L4599314767.6   L48700858022.1  L49304025233.2  L49442955282.12 L52258283942.1  L53577728712.1  L57317554718.5  L57698627611.2  L58209102511.1  L59314923118.4  L60098763854.3  L63073555870.4  L66426995373.12 L67372926033.2  L8603426141.5   L9356559676.11  P28627113325.199P49296947798.199P57713046236.199P67365848726.199Q11968186855.199Q13394240522.195Q16827575549.199Q20614549399.195Q25954107624.199Q28465177121.196Q3375676648.199 Q3421936230.198 Q41261547165.195Q45057547415.199Q5265442331.197 Q57228775306.198Q58205651829.199Q60189065437.199Q68235297648.198Q68235297648.199Q7368572160.195 00001>02L03Z04h05405D05f05g06106206306C06_07407]08F08K08a08f08g08l09109609J09K09O09Z09d0:20:[0:\0:m0;X0<^0=d0>O0?U0@[0A30A40AO0AP0Ai0Aj0BX0C30C40CN0D90D:0E60EZ0F<0FTS1R3HIA1h2LF2ra2sp1B3TOP3LFB2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1B3TOP3LFB2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS2sp3sp13SP1S2dA2dB4BPOS3BLES2dA2dB4PHIb4PHIr5PHIR03NA03NB02B1SS3sp14gapnFSS2dA2dB4BPOS3BLES2dA2dB4PHIb4PHIr3NA03NB02B1S1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S1d3FRb2D03FRr4FRR02B1S3sp1FS3sp1S3sp1S3sp1S2dA2dB4PHIb4PHIr2B1FS2FBS2dX2dA1E1KS1R2lo3LOSS1d3FRb3FRr2B1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1d3FRb2D03FRr2B1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R2LF2sp1B3LFB3sp14gapn3SP12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCFS2LF2sp2lo3LFB3sp14gapn3SP1FS2LF3LFB3sp14gapn4SP1R2HBFS1R2LF2sp1B2lo3LFB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1FS2LF3LFB3sp14gapn2HB5Ha_stS1R2LF1B2lo3LFB3sp14gapn3LOC2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp1B2lo3LOS3SLO3LFB3sp14gapn3SP12HB5Ha_st5Hl_stS1R2LF1B3LFB3sp14gapn2HB5Ha_st5Hl_stS2LF1B3LFB3sp14gapn2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SXA IA2 ESA PHIR0 FRR0 BM_PHI BM_FR NA0 NB0 OA"] Lemma dv_MAIN : dvM2_stmt ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2pad gb u0 u1 u2 jq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 FB) c128 c136 (Z_to_bv 64 FB))
              (T2C t2pad) [] gb [C4 u0; C4 u1; C4 u2] jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB -> mpd_abs dB <= mpd_abs dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 B) (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
          F (Z_to_bv 64 0x9f404) fc None mq (seg_rom asegs)).
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
    apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [TPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [JQC _].
    cbn [fst snd] in SPC, T2Cq, ZCq, GAPC, SAVE, FHD, TPC, JQC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    pose proof (munch_refl [(sp1, sp1 + 152)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH 0 0).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM SPC T2Cq ZCq GAPC SAVE FHD TPC JQC.
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
    eapply (call_copy_l m2 hq LBq [dLX; dY; dZ; dT] _ 0 0 0%nat dLX dA 0x9f418); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite AE; reflexivity).
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
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| rewrite EA3; exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * pose proof BM_PHI as B1. unfold_bud. clear - B1 NA0 NB0. lia.
        * pose proof BM_FR as B1. unfold_bud. clear - B1 D0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvM3_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    lfacts dA dLX -> lfacts dB dY -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> v + dvV4 <= PHIb -> f + dvF3 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 B) s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f42c) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L12691537071.1L13655593885.5L14348534914.6L1921887436.7 L29956516996.0L30780105986.8L31720098237.6L32121109934.3L56543256993.0L58500857548.900000400D00W00o01001N01d01o02002TS2FBS1d3FRb3FRr1f2HFS1d3FRb2D03FRr1f2HFS1d3FRb2D03FRr4FRR01f2HFSS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA2dB4PHIb4PHIr1v2HVS2dA2dB3VABSS2dA2dB4PHIb4PHIr5PHIR03NA03NB01v2HV". (* [comment removed for export] *)
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
    eapply (call_copy_l mq hq LBq [dLX; dY; dZ; dT] _ v f 1%nat dY dB 0x9f428); try eassumption; try reflexivity; try (rewrite EAY; reflexivity); try (rewrite BE; reflexivity).
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
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| rewrite EA3; exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
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
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF PHIR0 FRR0"] Lemma dv_ERR16 : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    UWCD mq -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f704) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST EAX EAY EAZ EAD UW HV HF.
    eapply C_CLEAN_X with (r := -16); [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| exact UW| clear; lia| intros K; exfalso; clear - K; lia| unfold div_mpi_nz; apply Z.le_max_l| |].
    - clear - HV PHIR0. lia.
    - clear - HF FRR0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvM4_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV4 <= PHIb -> f + dvF4 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 (md_n dA + 2)) (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f4a8) fc None mq (seg_rom asegs)).

  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@D11138851872.217D17183699282.306D3349449248.229 D35617972959.305D35617972959.306D48084872841.305D53578774111.229D62011970312.229D64280614944.229D67430489183.217K12690573793.217K12690573793.229K45774582958.229L12267821285.1  L12469921329.0  L12694265486.2  L13655593885.5  L14348534914.6  L15216807696.294L15822417165.1  L1685717371.0   L17507800040.1  L18320580243.8  L18363988631.13 L18366171437.14 L19980016842.7  L20028099350.4  L23461302570.231L23500973377.0  L23539585209.2  L26232954963.3  L26530157006.220L27019463589.2  L27364556572.243L27364556572.294L27954469902.3  L2803942888.1   L30157387091.6  L32354394574.210L32454903270.1  L33513311607.10 L34616251577.6  L35663928186.7  L372066202.210  L38325499858.13 L38327596498.16 L3925383176.2   L39259851285.12 L39261862319.13 L39261961171.15 L4089016915.11  L41155479456.1  L42003528019.2  L43677759120.231L45777250370.2  L46434418113.1  L46756382136.292L46839732335.293L4935003471.2   L51005809078.7  L52806978339.3  L53530622874.220L5509432403.11  L55990716303.293L56523586534.1  L58788176546.11 L58790367512.11 L59308631146.3  L59308633593.3  L59321342608.4  L5975110039.287 L60098763854.3  L62018535662.1  L62037211595.7  L6203936179.1   L63950727862.8  L64274430384.11 L64703390219.10 L64705450417.11 L64810416763.243L65614147016.1  L66038874368.11 L66151427842.16 L67482132013.2  L7181165107.4   L9356559676.11  L9838743115.2   P27967082900.305P27967082900.306Q11708072759.214Q11801279589.217Q11801279589.229Q11801279589.305Q11801279589.306Q16623769894.225Q17000624785.218Q17002805393.217Q17356582774.236Q17757173815.226Q18397797912.237Q19056309629.237Q24471895157.302Q25513505925.304Q25513505925.305Q26130604464.304Q39085863854.303Q39212284437.237Q40701317926.214Q48916668113.302Q48916928383.249Q49473382146.301Q49698585326.216Q49698585326.227Q49698585326.303Q49698585326.304Q51003319455.301Q52744951088.217Q52744951088.228Q52747231024.218Q60085137072.234Q60133849205.305Q60511567613.237Q61046252962.249Q61046516748.302Q63565942191.236Q63566450772.234Q63566565718.237Q65424847505.228Q9072899383.225 Q9538787269.234 Q9961343543.215 00000`02U02V04R06N08C09309e0:U0;E0<40<c0=R0=V0=W0=X0=h0>;0?30?70?80?<0?Z0?[0?\0@40@F0A30A40A;0AG0Ah0Ao0BX0CP0CQ0CU0Ch0DI0DM0DN0Dd0E90EZ0FG0FH0FQ0FR0FS0GJ0H30H80H?0Hi0Hj0Ho0JK0KC0KJ0Ke0Ko0LP0M90N10N50N60NO0NY0Nd0Ne0OZ0Od0Og0PB0PG0Pe0Pn0Po0Q60Qf0Qk0R50RQ0RX0Rg0SR0S\0U?0Vb0W90Wc0XM0YI0ZB0ZY0[?0[e0\>0\[0]80]Q0^C0_I0`L0aO0bA0bZ0c10cb0dG0e;0e[0f;0fn0ga0hR0i80i^0jD0j]0k]0l40l\0mP0mi0nB0n[0oA0oX0oo10LS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13LBq3dLX2dY2dZ3SPR2F04SP1R3ARv2Z04C24q2An3FA02HB5Ha_st5Hl_stFS1R3HIA1h2LB2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3LBq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z04C24q2An2h43HT43FA02HB5Ha_st5Hl_stS1R3HIA1h2LB2LF2ra2sp1A3TOP3LFB2dA2FB3sp14gapn3GAP2hq3LBq3dLX2dY2dZ3SPR2F03HTq4SP1R3ARv2Z04C24q2An2h43HT43FA02HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2ra2sp1A2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13LBq3dLX2dY2dZ3SPR2F04SP1R3ARv2Z04C24q2An3FA02HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENY3PYF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENY3PYF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY4LENX3PXF2HB5Ha_st5Hl_stS2dAFFS1d3FRb3FRr1f2HFS1d3FRb2D03FRr1f2HFS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS2FBSS2FBS2dA2dB4PHIb4PHIr3NA03NB01v2HVFFS1R3HIA1h2sp3TOP3sp13SP1S2LB4C24H3LBq4C24qS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3NA03dLX2dY2NASS2dA2NAS2dA2NA4NA98S2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2dA2NAS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY2dZS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnFS2FBS1d3FRb2D03FRr1f2HFS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2FBFS2dA2dB4PHIb4PHIr1v2HVS1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS1R3HIA1h1d3FRb2D04BUDF3FRr4FRR02hq1f2HF4HFRqFS2dA4NA98FFS1R3HIA1h2dA2dB4PHIb3BUD4PHIr5PHIR03NA03NB02hq1v2HV3HVqS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S2dA2KLS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3dLX2dY3ARvFS3sp1S1R2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ3ACV3SPR2F04SP1R2NX3ARv2Z04C24q2An3FA03FA1S2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS2dA2NAS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA2hqS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24q2AnS2FBFS1R2sp2lo3SLO3sp13SP13NRMS2dA2NA2KGS2An3FA02KZFS2LB2LF2ra2sp1A3LFB2dA2FB3sp14gapn3LBq3dLX2dY2dZ4C24qS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA4NA98FS2dA2NAS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3NA03dLX2dY2dZ2NAS3sp1S3sp14SP1RS3sp12r04SP1M1q1r1H2H02q02H4S2dA2NAS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1RS1R5NEEDR2LB2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ3ALO4LENA4C24q2An3FA12HB5Ha_st5Hl_stS1R5NEEDR2LB2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ3ALO4LENA4C24q2An3FA12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY3EAY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY3EAX2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF1A3LFB2dA4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY2F02HBS2LF1A3LFB2dA4gapn3dLX2dY3ARvS2LF1A3LFB2dA4gapn3dLX2dYS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4SP1R4C24q2HBS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24q2An2HB5Ha_st5Hl_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4SP1R4C24q2HBS2LF1A3LFB2dA4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24qS2LF2lo3LFB2dA3sp14gapn3LOC3dLX2dY2dZS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24qS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_stS2LB2LF3LFB2dA3sp14gapn3LBq3dLX2dY2dZ4C24q2HB5Ha_stS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24qS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF1A3LFB2dA4gapn3dLX2dYS2LB2LF2lo3LFB2dA3sp14gapn3LOC3LBq3dLX2dY2dZ4C24q2HB5Ha_st5Hl_stS2LF3LFB2dA4gapn3dLX2dYS2LF2sp2lo3LFB2dA3sp14gapn3SP13dLX2dY2dZS2LB2LF2sp2lo3LFB2dA3sp14gapn3SP13LBq3dLX2dY2dZ4C24qS2LF1A3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dYS2LF1A3LFB2dA4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2dA4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY2F02HB". (* [comment removed for export] *)
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
    assert (CWX : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 32) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWY : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 64) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
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
    assert (CST2 : CSTA m2 hq LBq [dLX; set_sg dY 1; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
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
    assert (CST3 : CSTA m3 hq LBq [set_sg dLX 1; set_sg dY 1; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { change [set_sg dLX 1; set_sg dY 1; dZ; dT] with (set_nth 0 [dLX; set_sg dY 1; dZ; dT] (set_sg dLX 1)).
      eapply sign_store_l with (mq := m2); try eassumption; try reflexivity. unfold mpi_cells. rewrite EAX. exact CX. }
    assert (UW3 : UWCD m3) by (eapply S_uwcd_store; [exact UW2| exact MU| rewrite EAX; clear - F1 ALO LOS SLO SP1 NEEDR; lia]).
    clear MU WM.
    (* [comment removed for export] *)
    pose proof (opv_A _ _ _ _ _ _ _ CST3) as (CAv & OAv & ARv & A8v & _ & LENA & NA & _).
    rewrite <- AE in CAv, OAv, ARv, A8v. unfold mpi_cells in CAv.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    shadow_chk OAv (A + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dA)) by (clear - NA; lia). zstep. zstep. zstep.
    zstep. if_cases KL; zify_cond KL; rewrite ?unsigned_lit in KL by (clear - NA; lia).
    { eapply dv_ERR16; [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| |].
      - clear - HV NA0 NB0. unfold_bud. lia.
      - clear - HF D0. unfold_bud. lia. }

    assert (NA98 : md_n dA <= 9998) by (clear - KL; lia).
    (* [comment removed for export] *)
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & _ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZ0 in OWZ. destruct OWZ as [PZ0 NZ0]. rewrite EAZ, PZ0, NZ0 in CZ. unfold mpi_cells in CZ.
    zstep. rewrite (zx16_small 0) by (clear; lia). zstep.
    zstep. if_cases KG; zify_cond KG; rewrite ?unsigned_lit in KG by (clear - NA; lia); [exfalso; clear - KG NA; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity).
    pose proof (A_mpi_client2.cs_cnt24 asegs R HIA HNDk h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as C24q. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in C24q.
    pose proof (arl_need_rt_malloc R) as NRM.
    pose proof (conj CZ I) as CZb.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply (heapA_calloc_t asegs R HIA) with (h := hq) (LB := LBq) (LF := LF1) (cnt := md_n dA + 2) (sz := 4) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (rewrite HSq; exact UW3).
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
    destruct CZb as [CZ3 _].
    assert (CZ4 : rw_cells asegs m4 (sp1 + 168) [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 (md_sg dZ)); C2 (Z_to_bv 64 0); C4 (md_pad dZ)]).
    { eapply (presA_rw_cells asegs R); [exact HP4| exact CZ3| apply client_range_stack; clear; lia| exact I]. }
    assert (UW4 : UWCD m4).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP4| rewrite HSq; exact UW3| clear; lia| intros a Ha; exact I| clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
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
      assert (CST4 : CSTA m4 h4 LBq (set_nth 2 [set_sg dLX 1; set_sg dY 1; dZ; dT] dZ) dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + 0) (f + fr_charge (d + 1))).
      { eapply (A_mpi_client2.cs_binop_l asegs R HIA) with (i := 2%nat) (dX := dZ) (mq := m3) (hq := hq); try eassumption; try reflexivity.
        - split; [reflexivity|]. split; [exact NSZ|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b _ _. reflexivity.
        - eapply presA_weaken; [exact HP4| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx _; exact I].
        - intros b Hb. left. exact Hb.
        - intros b Hb. left. exact Hb. }
      cbn [set_nth] in CST4.
      eapply dv_ERR16; [exact CST4| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW4| |].
      + clear - HV NA0 NB0. unfold_bud. lia.
      + clear - HF D0. unfold_bud. lia.
    - (* [comment removed for export] *)

      dpose HFRA as (FA0 & FA1 & FA2 & FA3).
      replace ((md_n dA + 2) * 4) with (4 * (md_n dA + 2)) in * by (clear; lia).
      pose proof (munch_refl [(sp1 + 168, sp1 + 184)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by (clear - FA0 FA1 ACV; lia); [exfalso; clear - KZ FA0; lia|].
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : HM asegs R HIA h4 _ LF1 m5 |- _ => rename H into HH5 end.
      match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
      match goal with H : stk asegs m5 lo sp1 |- _ => rename H into ST5 end.
      set (dZ5 := mkMPD (sp1 + 168) (md_sg dZ) (md_n dA + 2) An (repeat (Z_to_bv 64 0) (Z.to_nat (md_n dA + 2))) (md_pad dZ) LHeap).
      assert (MLZ5 : mpd_at asegs m5 ((An, 4 * (md_n dA + 2)) :: LBq) dZ5).
      { split; [| exact SGZ]. unfold dZ5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells.
        split; [exact CZ4|]. split; [clear - SP1M; Z.div_mod_to_equations; lia|]. split; [clear - SP1R SP1 SLO LOS ALO ACP NEEDR; lia|].
        split; [rewrite repeat_length; clear - NA; lia|]. split; [unfold MPI_MAX_LIMBS; clear - NA NA98; lia|].
        split; [clear - NA; lia|]. split; [left; reflexivity|]. split; [exact A16|].
        eapply (u32arr_of_cells asegs); [exact HNEW| rewrite u32s_repeat0; f_equal; clear - NA; lia]. }
      assert (CST5 : CSTA m5 h4 ((An, 4 * (md_n dA + 2)) :: LBq) (set_nth 2 [set_sg dLX 1; set_sg dY 1; dZ; dT] dZ5) dX
                       (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + 0) (f + fr_charge (d + 1))).
      { eapply (A_mpi_client2.cs_calloc_attach asegs R HIA) with (i := 2%nat) (d := dZ) (mq := m3) (hq := hq); try eassumption; try reflexivity.
        - eapply presA_trans with (m1 := m4).
          + eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros xx _; exact I].
          + rewrite EAZ. replace (sp1 + 168 + 16) with (sp1 + 184) by (clear; lia).
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L26496199141.3 L29515765010.11L62037211595.7 L8931608776.1  L9366540546.10 00000<00X01301801_S2sp3sp13SP1S1R3HIA1h3sp12wa2wb2Hw2a02HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACP". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO SP1"] Lemma uwcd_munch : forall W mq m2, UWCD mq -> munch W mq m2 -> Forall (fun w => snd w <= sp1 + 184) W -> UWCD m2.
  Proof.
    intros W mq m2 UW MU HW. rt_facts.
    eapply uwc_floor with (F := sp1 + 184); [| clear; lia].
    eapply uwc_munch; [eapply uwc_raise_m; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
    intros a0 Ha. clear - HW Ha. induction HW as [|[wa wb] W' Hw _ IH]; [exact I|]. cbn [outside fst snd] in *. split; [lia| exact IH].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_CP.

  (* [comment removed for export] *)
  Definition dvM4b_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV4 <= PHIb -> f + dvF4 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 s10v (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f4dc) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01a0@C17025492443.236C34148349383.237C34148349383.238D17183699282.247D23292090960.238D23907573425.239D33876909647.239D33988137722.247D3716744088.238 D43836906270.238D4450269177.239 D59671782440.238D60109446735.238K21212095580.236L10897409697.0  L12251719832.2  L16764136465.2  L17095181706.2  L19532412838.6  L19684006143.1  L19684006143.2  L19980016842.7  L21218866939.2  L24273062129.1  L26851215369.231L27364556572.214L27375151549.2  L28172831004.12 L28613873490.2  L31454615961.2  L32168522716.228L32172565554.231L32172768967.213L32287489260.1  L35044277615.2  L35663928186.7  L38235734261.1  L39172636981.0  L40064338006.2  L40420896875.1  L42517693215.11 L43825175696.1  L44107246460.239L54248392413.2  L55990716303.214L56386624752.239L56883856123.2  L57017996577.12 L58790367501.12 L59667784614.1  L60098763854.3  L60660110969.1  L62018535662.1  L63641776730.1  L66332508238.2  L66332810040.3  L68377014843.3  L812924237.9    L8931608776.1   L9080220944.4   L9356559676.11  L9626242935.231 O17025492443.236O19981014709.236O24374484701.238O34148349383.237O34148349383.238P19688836881.247P21212095580.236P35030842081.238P40077402040.239P66327680928.247P68373149109.236Q11801279589.247Q13420329874.235Q25075822059.239Q25513505925.246Q26295627581.236Q31205737968.239Q31942369726.236Q3375393928.239 Q33874924623.238Q34964382778.239Q38248387216.238Q38248387216.239Q39085863854.244Q43836906270.238Q43836906270.239Q4452482553.238 Q44992724106.243Q45057789175.239Q46491598615.243Q48914764906.218Q49472925079.218Q49698585326.237Q49698585326.245Q50458135125.236Q51003780618.218Q54850542606.239Q59118516891.233Q59307101533.236Q59667195953.236Q59668083912.235Q59671782440.233Q59671782440.238Q59671782440.239Q60133849205.246Q61044090551.218Q68383599693.236Q8956025278.233 Q9090756535.238 Q9090756535.239 Q9356559649.219 00000100200301L01M01N02W04005:05W06C06`07F07G07H07P07X07`08508908:08R08S08T09109N09W09_09g09h0:l0<00<n0=30=40=I0=M0=N0=O0=S0>=0>A0>a0>i0?F0?f0?j0?k0@D0@H0@R0@V0@Y0@]0@^0@_0@`0@a0@f0A50A`0B=0B>0B?0B@0BM0BZ0Cl0Cm0Dc0F20GJ0Go0HY0I30JB0K20KB0KC0KW0KX0LA0Lk0M>0MQ0N00N@0NP0No0OM0ON0Oo0PJ0Ph0QA0Qa0R10RL0Rf0S@0SZ0Sj0T:0TJ0TZ0Tj0UW0V50VL0V\0W:0WX0X1FFFS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12dZ3SPR2F04SP1R2Z03PZ02zl2HB5Ha_st5Hl_stFFS2LF2ra2sp3LFB2dA2FB3sp14gapn3NA02dZ2NZ3SPR2F04SP1R2Z03PZ02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq2dZ3SPR2F03HTq4SP1R2Z03PZ02zl2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp2lo3TOP3LFB2FB3sp14gapn3GAP2hq2dZ3SPR2F03HTq4SP1R2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn2dZS2LF2ra2sp3LFB2FB3sp14gapn2dZ2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn2dZS1R2LF2ra2sp2lo3LOS3LFB2FB3sp14gapn2dZFSS2lo3sp1S2dZ3NZ1S2dZ3NZ1S1R2lo3LOS2dZ3ALO3PZCS2dZFS1R3HIA1h2sp3TOP3sp13SP1FFS2LF2ra2sp3LFB2FB3sp14gapn2dZS2LF2ra2sp3LFB2FB3sp14gapn2dZS2dZ4LENZS2dZ3NRZS2dZ3NRZFS1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA02dZ2NZ3ACV3SPR2F04SP1R2Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn3NA02dZ2NZ3ACV3SPR2F04SP1R2Z03PZ03PZCS1R2LF2ra2sp3LFB2FB3sp14gapn2dZ3ACV3SPR2F04SP1R2Z03NRZ3PZ03PZCS3sp1FS1R3HIA1h2sp2lo3TOP1HS2loSFS2dZS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dZ3ALO3PZCS2dZS2LF2ra2sp3LFB2FB3sp14gapn2dZ2zlS2lo3sp1S2LF2ra2sp3LFB2FB3sp14gapn2dZS2LF2ra2sp3LFB2FB3sp14gapn2dZ2zlS2dZSS1R2sp2lo3SLO3sp13SP13NRAS2dZS1R2lo3LOSS2dZS1RS2dZFFFFS3sp1S2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2ra2sp3LFB2FB3sp14gapn2dZFFFS2dZ4LENZ3NZ1S2dZ4LENZ3NZ1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13NA02dZ2NZ3ALO3PZC2zl2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP12dZ3ALO3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13NA02dZ2NZ3ALO3PZC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13NA02dZ2NZ3ALO3PZC2zl2HB5Ha_st5Hl_st5LENZ6S1R2LF2lo3LOS3LFB3sp14gapn2dZ3ALO3PZCS2LF3LFB3sp14gapn2dZ3EAZ2zl2HB5Ha_st5Hl_stS2LF3LFB2dA4gapn3NA02dZ2NZS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP13NA02dZ2NZ3ALO3PZC2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP12dZ2zl2HB5Ha_st5Hl_stS2LF3LFB4gapn2dZFS2LF3LFB4gapn2dZ3PZ0FS2LF3LFB2dA4gapn3NA02dZ2NZ2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB3sp14gapn3SP12dZS2LF2lo3LFB4gapn2dZS2LF2lo3LFB4gapn2dZS2LF3LFB3sp14gapn2dZ4SP1R2zl2HBS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZ2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC2dZ2zlFS2LF2sp2lo3LFB3sp14gapn3SP12dZ2zlS2LF2lo3LFB3sp14gapn3LOC2dZS2LF2sp2lo3LFB3sp14gapn3SP12dZS2LF3LFB4gapn2dZ2HB5Ha_stS2LF3LFB3sp14gapn2dZ2zl2HB5Ha_stS2LF3LFB4gapn2dZS2LF2lo3LFB3sp14gapn3LOC2dZS2LF3LFB2dA4gapn3NA02dZ2NZS2LF3LFB2dA4gapn3NA02dZ2NZS2LF3LFB2dA4gapn3NA02dZ2NZS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZS2LF3LFB4gapn2dZS2LF2lo3LFB3sp14gapn3LOC2dZ2zl2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP12dZS2LF3LFB4gapn2dZ3PZ02HBS2LF3LFB4gapn2dZS2LF2sp2lo3LFB3sp14gapn3SP12dZS2LF2sp2lo3LFB3sp14gapn3SP12dZS2LF3LFB3sp14gapn2dZ4SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8 NA0 AMS"] Lemma dv_M4 : dvM4b_stmt -> dvM4_stmt.
  Proof.
    intros K4b. unfold dvM4_stmt. intros until t6. intros CST EAX EAY EAZ EAD LFX LFY SGX SGY OZH NZ OT0 UW VAB NA98 HV HF. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (cs_ok_sb _ _ CSOKq) as SB64q. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (arl_need_rt_amem R) as NRA.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (INZF : In (md_p dZ, 4 * md_n dZ) (LBq ++ fdata LF1)) by (apply in_or_app; left; exact INZ).
    pose proof (blk_top47_sub asegs R HIA hq LBq LF1 mq _ _ (md_p dZ) (md_n dZ * 4) HHq INZ ltac:(clear; lia)) as Z47.
    pose proof UAZ as HPL. apply u32arr_cells in HPL. apply (u8arr_of_rw_cells asegs) in HPL.
    pose proof (munch_refl [(md_p dZ, md_p dZ + md_n dZ * 4); (lo, sp1)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dZ)) by (clear - NRZ; unfold MPI_MAX_LIMBS in NRZ; lia).
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_CP) as SPM. unfold A_ASAN_MEMSET_CP in SPM.
    acallxA_sp sp1
      (eapply SPM with (h := hq) (LB := LBq) (LF := LF1) (DST := md_p dZ) (v := 0) (n := md_n dZ * 4) (lo := lo) (ds := u32s (md_limbs dZ));
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | rewrite u32s_length; clear - LENZ; lia
             | eapply aobj_sub; [exact OPZ| clear; lia| clear; lia]
             | eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]
             | left; clear - PZC ALO LOS; lia
             | exact Z47
             | eapply client_wrange_block; [exact INZF| clear; lia| clear; lia]
             | (rewrite HTq; clear - SP1 TOP; lia)
             | clear - NRZ LOS SLO NEEDR NRA SP1 SPR; unfold MPI_MAX_LIMBS in NRZ; lia
             | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ] ]).
    clear SPM.
    all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSET-SIDE:" g end.

    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 (md_p dZ) _ |- _ => rename H into HPZ end.
    match goal with H : ?x = Z_to_bv 64 (md_p dZ) |- _ => subst x end.
    apply (rw_cells_of_u8arr asegs) in HPZ. rewrite repeat_length in HPZ.
    apply (rw_cells_zeros asegs m5 (md_p dZ) (Z.to_nat (md_n dZ * 4)) [C4 (Z_to_bv 64 0); CB (Z.to_nat (md_n dZ * 4 - 4)) (repeat (Z_to_bv 8 0) (Z.to_nat (md_n dZ * 4 - 4)))]) in HPZ;
      [| cbn; repeat split; reflexivity | cbn [cells_size csize]; clear - NZ1; lia].
    apply (rw_cells_app asegs m5 (md_p dZ) [C4 (Z_to_bv 64 0)]) in HPZ. destruct HPZ as [HP0 HPR]. cbn [cells_size csize Nat.add] in HPR.
    replace (md_p dZ + Z.of_nat 4) with (md_p dZ + 4) in HPR by (clear; lia).
    match goal with H : aobj asegs AL (hcs asegs R HIA hq) m5 (md_p dZ) _ |- _ => rename H into OPZ5 end.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPZ5 (md_p dZ) 4.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m6 |- _ => rename H into HH6 end.
    match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
    match goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
    match goal with H : rw_cells asegs m6 (md_p dZ) [C4 ?w] |- _ => rename H into HP6 end.
    match goal with H : rw_cells asegs m6 (md_p dZ + 4) _ |- _ => rename H into HPR6 end.
    match goal with H : rw_cells asegs m6 (sp1 + 168) _ |- _ => rename H into CZ6 end.

    set (zl := [Z_to_bv 64 0] ++ repeat (Z_to_bv 64 0) (Z.to_nat (md_n dZ - 1))).
    set (dZ6 := mkMPD (md_addr dZ) (md_sg dZ) (md_n dZ) (md_p dZ) zl (md_pad dZ) LHeap).
    assert (UAZ6 : u32arr asegs m6 (md_p dZ) zl).
    { unfold zl. apply u32arr_app. split.
      - eapply (u32arr_of_cells asegs); [eapply rw_cells_reshape; [exact HP6| cbn -[le4]; split; [apply length_le4| exact I] | cbn -[le4]; rewrite app_nil_r; reflexivity]|].
        cbn. rewrite ?app_nil_r. reflexivity.
      - cbn [length Z.of_nat Pos.of_succ_nat]. replace (Z.to_nat (md_n dZ * 4 - 4)) with (4 * Z.to_nat (md_n dZ - 1))%nat in HPR6 by (clear - NZ1; lia).
        eapply (u32arr_of_cells asegs); [exact HPR6| symmetry; apply u32s_repeat0]. }
    assert (MLZ6 : mpd_at asegs m6 LBq dZ6).
    { split; [| exact SGZ]. unfold dZ6. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAZ.
      split; [exact CZ6|]. split; [rewrite <- EAZ; exact Z8|]. split; [rewrite <- EAZ; exact Z0|].
      split; [unfold zl; rewrite length_app, repeat_length; cbn [length]; clear - NZ1; lia|]. split; [exact NRZ|].
      split; [exact NZ1|]. split; [exact INZ|]. split; [exact PZ16| exact UAZ6]. }
    assert (HPA6 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dZ, md_p dZ + md_n dZ * 4); (lo, sp1)] mq m6).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m6 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH6| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_cons; [cbn [fst snd]| apply Forall_nil]].
      - eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPZ5)| clear; lia| clear; lia].
      - eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]. }
    assert (CST6 : CSTA m6 hq LBq (set_nth 2 [dLX; dY; dZ; dT] dZ6) dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dZ) (WX := [(md_p dZ, md_p dZ + md_n dZ * 4); (lo, sp1)]); try eassumption; try reflexivity.
      - apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OZH| clear; lia]| apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_nil]].
      - unfold dZ6. cbn [md_own]. symmetry. exact OZH. }
    cbn [set_nth] in CST6.
    assert (UW6 : UWCD m6).
    { eapply uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - PZC ALO LOS SLO SP1 NEEDR; lia| apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil]]. }
    clear MU WM.
    (* [comment removed for export] *)
    assert (LENZ6 : Z.of_nat (length zl) = md_n dZ) by (unfold zl; rewrite length_app, repeat_length; cbn [length]; clear - NZ1; lia).
    pose proof (munch_refl [(md_addr dZ + 8, md_addr dZ + 10)] m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m7 |- _ => rename H into HH7 end.
    match goal with H : mem_inv asegs m7 |- _ => rename H into MI7 end.
    match goal with H : stk asegs m7 lo sp1 |- _ => rename H into ST7 end.
    match goal with H : rw_cells asegs m7 (sp1 + 168) _ |- _ => rename H into CZ7 end.
    match goal with H : u32arr asegs m7 (md_p dZ) zl |- _ => rename H into UAZ7 end.
    assert (CST7 : CSTA m7 hq LBq (set_nth 2 [dLX; dY; dZ6; dT] (set_sg dZ6 1)) dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply sign_store_l with (mq := m6); try eassumption; try reflexivity. unfold dZ6, mpi_cells. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite EAZ. exact CZ7. }
    cbn [set_nth] in CST7.
    assert (UW7 : UWCD m7) by (eapply S_uwcd_store; [exact UW6| exact MU| unfold dZ6; cbn [md_addr]; rewrite EAZ; clear; lia]).
    unfold dvM4b_stmt in K4b.
    eapply K4b with (dZ := set_sg dZ6 1); [exact CST7| exact EAX| exact EAY| exact EAZ| exact EAD| exact LFX| exact LFY| exact SGX| exact SGY| reflexivity| exact NZ| exact OT0| exact UW7| exact VAB| exact NA98| exact HV| exact HF].
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
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    lfacts dA dLX -> lfacts dB dY -> md_sg dLX = 1 -> md_sg dY = 1 -> md_own dZ = LHeap -> md_n dZ = md_n dA + 2 -> md_own dT = LHeap -> md_n dT = md_n dA + 2 ->
    UWCD mq -> 0 < mpd_abs dB <= mpd_abs dA -> md_n dA <= 9998 -> v + dvV5 <= PHIb -> f + dvF5 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + 10)) SHA10 s10v (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f4f8) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11327188655.1  L13655593885.5  L14348534914.6  L1921887436.7   L23539585209.2  L25651766269.2  L27019463589.2  L29230279457.0  L29956516996.0  L30780105986.8  L31720098237.6  L35663928186.7  L43677759120.206L58500857548.9  L60098763854.3  L64810467185.2  L66390627273.0  L9356559676.11  Q17356582774.207Q18397797912.208Q19056309629.208Q28095821548.207Q39212284437.208Q52016735601.207Q60085137072.205Q60511567613.208Q63565942191.207Q63566450772.205Q63566565718.208Q9538787269.205 00000400D00T00l01301:01A01B01C01a02702L02o03S03]03d03e04P04b05805J05h06:06U06g07707I07[07m08=S2FBS1d3FRb3FRr1f2HFS1d3FRb3FRr1f2HFS1d3FRb2D03FRr4FRR01f2HFS2dA2NAS2dA2NAS2dA2NASSS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA2dB4PHIb4PHIr1v2HVS1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp1A3LFB2dA2FB3sp14gapn3ARvS2dA2dB4PHIb4PHIr5PHIR03NA03NB01v2HVS1R2lo3LOSS2dA2NASS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapn3ARvS2LF1A3LFB2dA4gapnS2LF2sp2lo3LFB2dA3sp14gapn3SP1S2LF1A3LFB2dA4gapnS2LF2lo3LFB2dA3sp14gapn3LOCS2LF1A3LFB2dA4gapnS2LF3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF1A3LFB2dA4gapnS2LF3LFB2dA4gapn". (* [comment removed for export] *)
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
    shadow_chk OAv (A + 10) 2.
    zstep. rewrite (zx16_small (md_n dA)) by (clear - NA; lia). zstep. zstep. zstep. clear MU WM.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 3%nat) (d := dT) as ([(_ & _ & _ & _ & _ & OWT) _] & _); try eassumption; [reflexivity|]. rewrite OT0 in OWT. destruct OWT as [_ NT0].
    eapply (call_xop_l A_MPI_GROW MPI_GROW_STACK_A _ _ _ _ _ GROW ltac:(clear; lia) ltac:(vm_compute; discriminate)) with (mq := mq) (i := 3%nat) (dl := dT) (c := md_n dA + 2) (retpc := 0x9f4f4); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
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
      assert (EAD' : md_addr dl' = FB + 96) by (rewrite EAL3; exact EAD).
      unfold dvM5_stmt in K5.
      ddestruct RR3 as [[(-> & SG' & NN' & _)|(-> & ->)] _].
      + zstep.
        assert (NT' : md_n dl' = md_n dA + 2) by (rewrite NN', NT0; clear - NA; lia).
        eapply K5; [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD'| exact LFX| exact LFY| exact SGX| exact SGY| exact OZH| exact NZ| | exact NT'| exact UW3| exact VAB| exact NA98| |].
        * eapply out_heapA; [exact ML3| exact NS'| rewrite NT'; clear - NA; lia].
        * clear - HV. unfold_bud. lia.
        * clear - HF. unfold_bud. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * clear - HV NA0 NB0. unfold_bud. lia.
        * clear - HF D0. unfold_bud. lia.
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

  Hypothesis BITLEN : mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.

  (* [comment removed for export] *)
  Definition dvM6_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8v s10v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= md_n dY -> md_n dY <= md_n dLX -> md_n dLX <= md_n dA + 1 -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dLX = 1 -> md_sg dY = 1 -> 0 < mpd_val dY <= mpd_val dLX -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvV6 <= PHIb -> f + dvF6 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) s8v s10v (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f514) fc None mq (seg_rom asegs)).

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L12691537071.1 L14348534914.6 L15162592258.2 L18457770450.4 L1921887436.7  L25581210123.2 L25696891297.0 L27293207874.6 L2782056031.15 L28784609534.5 L2885095.4     L29956516996.0 L30780287258.12L31525463372.2 L31718147504.16L32284259785.0 L35526939379.7 L40149985318.4 L41415990515.2 L51794595714.2 L54274957729.0 L54519161338.13L56757544215.4 L58209102511.1 L58500772564.13L67647012628.6 00000400B00H00U00m01301401B02402E02S02T03?03G04?04@04X04h04i04o05005^05n06206c078S2FBS3FRb3FRr1f2HFS1k2HKS2dY1k3NY12GYS1d3FRb2D03FRr4FRR01f2HFS1k2HKSS3FRb3FRr1f2HFS2dA2dB4PHIb4PHIr3NA03dLX2dY1v1k3NXA3NYB2HV2SN3SNYS2dA3dLX1k3NXA2SNS3FRb3FRr1f2HFSS2dA2dB4PHIb4PHIr3NA03NB03dLX1v1k3NXA2HV2SNS2dY3NY1S2dA2dB4PHIb4PHIr5PHIR03NA03dLX2dY1v1k3NXA3NYB2HV2SN3SNYSS1d3FRb2D03FRr4FRR01f2HFS3dLX2dY3NY13NYXSS1k2HKSS2dA2dB4PHIb4PHIr3dLX2dY1v1k3NXA3NYB2HV2SN3SNYS3dLX2dY3NY13NYXS2FBS2dA2dB4PHIb4PHIr5PHIR03NA03NB03dLX1v1k3NXA2HV2SNS3dLX2dY1k3NY13NYX2GX". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H PHIR0 FRR0 NA0 NB0 SHL"] Lemma dv_M5b : dvM6_stmt ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8v s10v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    nfacts dLX dY dZ dT -> md_n dY <= md_n dLX -> md_n dLX <= md_n dA -> md_n dY <= md_n dB -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvV5 <= PHIb -> f + dvF5 <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) s8v s10v (Z_to_bv 64 (-16)) t3 t4 t5 t6) F (Z_to_bv 64 0x9f99c) fc None mq (seg_rom asegs)).
  Proof.
    intros K6. intros until t6. intros CST EAX EAY EAZ EAD NF NYX NXA NYB HK UW BPOS NA98 HV HF. rt_facts.
    ddestruct NF as (OXH & OYH & OZH & OTH & NY1 & NZ & NT & SGX & SGY & VXY).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & _); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof (val_lvalA _ _ _ MLX SGX) as VLX. pose proof (val_lvalA _ _ _ MLY SGY) as VLY.
    assert (BLE : core_bitlen (md_limbs dY) (md_n dY) <= core_bitlen (md_limbs dLX) (md_n dLX)).
    { apply core_bitlen_mono_val; [clear - NY1 NYX; lia| clear - NY1; lia| rewrite <- VLX, <- VLY; exact (proj2 VXY)]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    unfold mpi_shift_l_stmtA_c in SHL.
    eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := mq) (i := 0%nat) (dl := dLX) (c := k) (retpc := 0x9f9a8); try eassumption; try reflexivity; try (rewrite EAX; reflexivity).
    - rewrite EAX. clear. lia.
    - cbv beta. clear - HK. lia.
    - pose proof (shift_l_n_le_succ k dLX ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia)) as SN. unfold shift_l_PHI. clear - HV NA0 NB0 PHIR0 SN NXA. unfold_bud. lia.
    - cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dX3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      pose proof (shift_l_n_le_succ k dLX ltac:(clear - HK; lia) ltac:(clear - NY1 NYX; lia)) as SN.
      assert (EAX3 : md_addr dX3 = FB + 32) by (rewrite EAL3; exact EAX).
      ddestruct RR3 as [[(-> & VX3 & SG3 & NX3)| ->] _].
      + zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. clear MU WM.
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 1%nat) (d := dY) as (MLY3 & _); try eassumption; [reflexivity|].
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m3) (i := 0%nat) (d := dX3) as (_ & NSX3 & _); try eassumption; [reflexivity|].
        pose proof (shift_l_n_le_succ k dY ltac:(clear - HK; lia) ltac:(clear - NY1; lia)) as SNY.
        eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3) (i := 1%nat) (dl := dY) (c := k) (retpc := 0x9f9b8); try eassumption; try reflexivity; try (rewrite EAY; reflexivity).
        * rewrite EAY. clear. lia.
        * cbv beta. clear - HK. lia.
        * unfold shift_l_PHI. clear - HV NA0 NB0 PHIR0 SN SNY NXA NYB. unfold_bud. lia.
        * cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
        * clear. lia.
        * intros m4 h4 LB4 dY4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
          pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV4.
          pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
          assert (EAY4 : md_addr dY4 = FB + 64) by (rewrite EAL4; exact EAY).
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
             eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| exact EAX3| exact EAY4| exact EAZ| exact EAD| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             ++ unfold shift_l_PHI. clear - HV NA0 NB0 SN SNY NXA NYB. unfold_bud. lia.
             ++ clear - HF D0. unfold_bud. lia.
      + zstep.
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX3| exact EAY| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
        * unfold shift_l_PHI. clear - HV NA0 NB0 SN NXA. unfold_bud. lia.
        * clear - HF D0. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0@L13869207609.0  L15908753905.3  L20490385257.3  L24356459904.252L24950277677.2  L27605258696.3  L27940357248.16 L27940405558.7  L2817928458.1   L31527560548.3  L32121109934.3  L33809151616.3  L33816087292.3  L3482839849.16  L35663928186.7  L3602826797.250 L37360441626.3  L38235734261.1  L38692635477.0  L3918199789.16  L41663468825.227L43097941400.3  L49631569796.7  L49992332264.3  L51070401118.0  L5156091514.227 L54200787000.3  L54424851272.16 L60098763854.3  L61507631172.4  L6493359339.16  L65999237284.8  L67931420133.3  L7484103457.0   L9080220944.4   L9356559676.11  Q10472012439.233Q34673729958.233Q44622834822.233Q522700727.233  00000100<00G00k01301=01_02:02?02I02T02^02i03f04;05=05H05L05M06@06a06l07D07N07O08008:08m09709E0:B0:`0:k0:l0;;0;f0<=0<T0<k0=BSS3dLX2dY2LTS2dA3dLX2NXS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2blS2dY3NRYS2dY2bl2BMS1R5NEEDR2sp2lo3SLO3sp13SP12dY3PY0S1R5NEEDR2sp2lo3SLO3sp13SP1S3sp1S2dB2dY2NYS2dA2dB3VABS2dB2dY2NYS2dA3dLX2NXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4LENY4PY163PY03PYCS1R3HIA1h2sp2lo3TOP1HS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY3ACV3SPR2F04SP1R3PY03PYC2bl3BLRS2dA3dLX2NXS2loSS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY3PY03PYCS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2dY2bl3BLRS2dA2dB3dLX2dY3VAB3BDX1TS2dY2bl2BMSS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dYS2dB2dY2NYS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY3PY03PYCS1R2lo3LOSS3FRb3FRr1f2HFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4LENY4PY163PY03PYCS2dA2dB4PHIb4PHIr3NA03NB01v2HVS2dA3dLX2NXSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dYS2LF3LFB2FB4gapn3dLX2dY". (* [comment removed for export] *)
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
      zstep. rewrite (lxor_ones5 (bl mod 32)) by (clear - BM; lia).
      eapply (dv_M5b K6) with (k := 31 - bl mod 32); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact NF| exact NYX| clear - NX; lia| clear - NY; lia| clear - BM; lia| exact UW2| clear - VAB; lia| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      zstep. ddestruct NF as (_ & _ & _ & _ & NY1 & _ & _ & _ & _ & VXY).
      unfold dvM6_stmt in K6.
      eapply K6 with (k := 0); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| exact NYX| clear - NX; lia| exact NZ| exact NT| exact SGX| exact SGY| exact VXY| clear; lia| exact UW2| clear - VAB; lia| exact NA98| |].
      + clear - HV NA0 NB0. unfold_bud. lia.
      + clear - HF. unfold_bud. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq :=
    (DCSM c0 c8 c16 c24 (Z_to_bv 64 (32 * (nx - ny))) (Z_to_bv 64 nx) (Z_to_bv 64 k) (Z_to_bv 64 (nx - ny)) (Z_to_bv 64 ny) c128 c136 t2pad gb u0 u1 u2 jq).

  (* [comment removed for export] *)
  Definition dvBT : Z := 2 ^ (32 * (md_n dA + 1)).

  (* [comment removed for export] *)
  Definition dvL1_stmt (D : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c128 c136 t2pad gb u0 u1 u2 jq v f (nx ny k vy : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dY = 1 -> mpd_val dY = vy -> 0 < vy -> 0 <= mpd_val dLX < Z.of_nat D * vy -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    mpd_val dLX < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 ny) (Z_to_bv 64 (4 * (nx - ny))) s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f554) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01e0@D25900232977.284D25900232977.285D35300034347.229D35300034347.230D60189065437.229D60189065437.230D60189065437.284D60189065437.285L10711524986.225L10729413793.2  L11144352574.3  L12469921329.0  L12691537071.1  L14348534914.4  L1504043955.5   L1685717371.0   L1921887436.7   L22647212463.3  L24281952833.2  L24950277677.2  L25543724691.4  L26988105723.2  L27109749153.0  L28508310067.224L28632618922.2  L29956516996.0  L30437538938.5  L30778190102.10 L31145622673.2  L31525463372.2  L32284259785.0  L33552778908.3  L33552778908.4  L34897664049.224L35663928186.7  L36757749421.12 L38060875949.12 L38126143619.2  L38259954321.2  L39172636981.0  L39284637285.0  L39834034895.2  L40149985318.4  L40150378917.3  L41417987709.6  L42397482388.6  L42888674241.1  L46561319510.3  L48700858022.1  L49304025233.2  L49442955282.12 L50996975716.1  L5156091514.225 L52258283942.1  L53577728712.1  L57698627611.2  L58498675416.11 L59723910010.4  L60098763854.3  L62072417481.2  L62365239714.4  L63744388140.2  L66426995373.12 L67372926033.2  L8927460375.224 L8929292959.279 L9356559676.11  P28627113325.230P28627113325.284P28627113325.285P31146933846.230P38261788758.230P49296947798.230P49296947798.284P49296947798.285P57713046236.230P57713046236.284P57713046236.285P67365848726.230P67365848726.284P67365848726.285Q10469979421.226Q11968186855.230Q1433360151.226 Q15236383893.281Q15901829514.280Q16827575549.230Q19403150984.281Q20545879308.226Q25954107624.230Q28465177121.227Q28465177121.281Q28465177121.282Q3421936230.229 Q3421936230.283 Q3421936230.284 Q37989389597.226Q37991750549.281Q3853489290.226 Q4182270749.226 Q44620800780.226Q5265442331.228 Q5265442331.282 Q5265442331.283 Q53878910229.281Q57228775306.229Q57228775306.283Q57228775306.284Q60189065437.230Q66559471232.226Q66561826824.281Q67147694615.280Q68235297648.229Q68235297648.230Q68235297648.284Q68235297648.285Q9874441992.281 00001F02\03j05=06K07^0940:J0:d0:l0;80;90;=0;K0;_0;`0<80<D0<L0<T0<d0<n0<o0=T0=U0=V0=h0>M0>N0>V0>W0>c0>o0?Q0?f0@O0A80A?0A@0AA0AB0AJ0AZ0Af0Ag0B30B80BD0BI0BJ0BO0BT0Bn0C30C80C90Cd0Cl0D60D=0DK0DT0E=0E>0F?0GC0Gn0I;0JI0KW0Ld0N10O>0PL0QZ0RJ0S;0Sl0U90VG0WU0We0Xk0YF0Yk0ZM0ZN0[00[@0[A0[Z0\=0\`0]S0^G0_;0_V0`;0`S0`c0a30aM0b10bU0c:0cj0d[0eL0fH0f`0gB0gg0hI0i00iZ0jD0jfS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP3dLX2dY3SPR2F04SP1R2cc2h33HT32HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP3dLX2dY3SPR2F04SP1R2cc2h33HT32HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq1k3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R2cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3SPR2F04SP1R2cc2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapnS3dLX2dYS2sp3sp13SP1FS2FBS3FRb3FRr1f2HFS3dLX2dY3NY13NYX3NRXSS1d3FRb2D03FRr4FRR01f2HFS3dLX2dY3VXYS3dLX2dYS2dY3NRYS3dLX2dY3NYX3BLRS3sp14gapnSS2LF2ra2sp3LFB2FB3sp14gapn2dY3NY13NRYFSS3dLX2dY3NY12cc2GYS2dA4PHIb4PHIr3dLX2dY1v3NXA2HV2cc3SNBFS2dY3NY1SS3dLX2dY3NYXS3dLX2dY3NYXS2LF2ra2sp3LFB2FB3sp14gapn3dLX3NRXS1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2dY2LRFSSS3dLX2dYS3dLX2dY3NY13NYXS3dLX2dY3VXYSS2dA3dLX3NXAS3sp1S3dLX2dY3BLRS3sp1FS3sp1S3dLXS2LF2ra2sp3LFB2FB3sp14gapnS3sp1S3sp1FS2dA4PHIb4PHIr5PHIR03dLX2dY1v3NXA2HV2cc3SNBS2dY3NY1S1R2lo3LOSS2dY2LRS2dA3dLX2LR2PMS3dLX3NRXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY3NY13NYX3NXA4NA983SPR2F04SP1RS2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY3NYX3NXA4NA983SPR2F04SP1R2cc3BLRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_st3dLX2dYS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_st3dLX2dYS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_st3dLX2dYS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_st3dLX2dYS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_st3dLX2dYS2LF2sp3LFB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_st3dLX2dYS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY3ALO2F12cc2HB5Ha_st5Hl_stS2LF3LFB2FB4gapnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11k3ALO2F12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccFS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF3LFB2FB4gapnFS2LF3LFB3sp14gapn4SP1R2HBS2LF3LFB3sp14gapn3dLX2dY4SP1R2cc2HBS2LF3LFB3sp14gapn3dLX2dY4SP1R2cc2HBS2LF2sp2lo3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_st3dLX2dYS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2cc2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF2lo3LFB3sp14gapn3LOCS2LF3LFB2FB4gapnS2LF3LFB2FB4gapnS2LF3LFB3sp14gapn2HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF2lo3LFB3sp14gapn3LOC1k2HB5Ha_st5Hl_st3dLX2dYS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2cc2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2cc2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11k2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2ccS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2ccS2LF3LFB3sp14gapn1k2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2cc2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2cc". (* [comment removed for export] *)
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
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'.
    apply Forall_cons_iff in CHq'. destruct CHq' as [SPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [T2Cq CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [ZCq CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [TPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [JQC _].
    cbn [fst snd] in SPC, T2Cq, ZCq, GAPC, SAVE, FHD, TPC, JQC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & _ & _ & _ & _ & _ & _ & _ & _ & _ & OXs); try eassumption; [reflexivity|].
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & _ & _ & NRX & _) _]. pose proof MLY as [(CY & _ & _ & _ & NRY & _) _]. rewrite EAX in CX, OXs. rewrite EAY in CY, OYs. unfold mpi_cells in CX, CY. unfold MPI_MAX_LIMBS in NRX, NRY.
    pose proof (munch_refl [(sp1, sp1 + 152)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (zx16_small (md_n dLX)) by (clear - NRX; lia). zstep. rewrite (zx16_small (md_n dY)) by (clear - NRY; lia). zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) (Z_to_bv 64 (md_n dLX - md_n dY)) c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM.

    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    set (cc := (md_n dLX - md_n dY) * 32).
    pose proof (core_bitlen_range (md_limbs dY) (md_n dY) ltac:(clear - NY1; lia)) as BLR.
    assert (SNB : shift_l_n cc dY <= md_n dLX).
    { unfold shift_l_n. destruct (Z.ltb_spec (md_n dY * 32) (core_bitlen (md_limbs dY) (md_n dY) + cc)); [| exact NYX].
      apply limbs_of_bits_le; [subst cc; clear - BLR NYX; lia| subst cc; clear - BLR; lia]. }
    unfold mpi_shift_l_stmtA_c in SHL.
    eapply (call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m2) (i := 1%nat) (dl := dY) (c := cc) (retpc := 0x9f538); try eassumption; try reflexivity; try (rewrite EAY; reflexivity).
    - rewrite EAY. clear. lia.
    - cbv beta. subst cc. change (2 ^ 32) with 4294967296. clear - NYX NRX NY1. lia.
    - unfold shift_l_PHI. clear - HV SNB NXA PHIR0. unfold_bud. lia.
    - cbv beta. clear - HF D0 FRR0. unfold_bud. lia.
    - clear. lia.
    - intros m3 h3 LB3 dY3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      assert (EAY3 : md_addr dY3 = FB + 64) by (rewrite EAL3; exact EAY).
      destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (CH3 & _ & MI3 & ST3 & HH3).
      destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as (HT3 & HS3 & _ & HCS3 & _ & _).
      pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST3) as OK3.
      pose proof (hcs_ok asegs R HIA h3) as CSOK3. pose proof (cs_ok_sb _ _ CSOK3) as SB643. pose proof (hcs_stack asegs R HIA h3) as SCS03.
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| rewrite HS3; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
      ddestruct RR3 as [[(-> & VY3 & SG3 & NY3)| ->] _].
      + pose proof CH3 as CH3'. unfold A_mpi_div_mpi_C.DCS in CH3'. repeat (apply Forall_cons_iff in CH3'; destruct CH3' as [?CK CH3']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
        pose proof (munch_refl [(sp1, sp1 + 152)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        match goal with H : HM asegs R HIA h3 LB3 LF1 m4 |- _ => rename H into HH4 end.
        match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
        match goal with H : stk asegs m4 lo sp1 |- _ => rename H into ST4 end.

        assert (CST4 : CSTA m4 h3 LB3 [dLX; dY3; dZ; dT] dX (DCSL c0 c8 c16 c24 (md_n dLX) (md_n dY) k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH (v + shift_l_PHI dY cc) (f + shift_l_FR)).
        { eapply S_cs_store with (mq := m3) (a := sp1) (b := sp1 + 152); try eassumption.
          - clear; lia.
          - left. clear - SP1. lia.
          - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY3, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
          - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. subst cc.
            replace (Z_to_bv 64 (32 * (md_n dLX - md_n dY))) with (Z_to_bv 64 ((md_n dLX - md_n dY) * 32)) by (f_equal; clear; lia).
            repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
          - eapply S_dcs_ok; [exact OK3| reflexivity| reflexivity| reflexivity| reflexivity]. }
        assert (UW4 : UWCD m4) by (eapply S_uwcd_store; [exact UW3| exact MU| clear; lia]).
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 1%nat) (d := dY3) as (_ & NSY3 & _); try eassumption; [reflexivity|].
        edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (shift_l_n_ge cc dY ltac:(subst cc; clear - NYX; lia) ltac:(clear - NY1; lia)) as GY.
        assert (P2 : 0 < 2 ^ cc) by (apply Z.pow_pos_nonneg; [clear; lia| subst cc; clear - NYX; lia]).
        assert (VY3P : 0 < mpd_val dY3) by (rewrite VY3; clear - VXY P2; nia).
        replace (Z_to_bv 64 (md_n dY + -1)) with (Z_to_bv 64 (md_n dY - 1)) by (f_equal; clear; lia).
        replace (Z_to_bv 64 ((md_n dLX - md_n dY) * 4)) with (Z_to_bv 64 (4 * (md_n dLX - md_n dY))) by (f_equal; clear; lia).
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
        eapply dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY3| exact EAZ| exact EAD| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L12128799109.1 L19980016842.7 L25148064707.3 L35590224338.3 L39261961171.9 L39272446419.9 L4223562214.6  L4781719053.2  L50313707442.2 L52101693566.17L59308631662.4 L60162046265.6 L61214967477.6 L62037211595.7 L6203936179.1  L66151427842.16L66668349941.1 L9356559676.11 L9838743115.2  00000300K00V00a01?01^02202802@03<03J03^04304N04S04o05205]05gS1fS1R3HIA1h2sp3TOP3sp13SP1S2di2dj3VJIS2di2dj3VIJS1R3HIA1h4PHIb3BUD2hq1v2HV3HVqS1R3HIA1h3FRb4BUDF2hq1f2HF4HFRqS1R2FB2dj3DJF3ALO2F1S1d2D0S2di3VIIS1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS2di2dj3ABL2KKS1R2FB2di3DIF3ALO2F1S1R2sp2lo3SLO3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
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
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c128 c136 t2pad gb u0 u1 u2 jq v f (nx ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 ny) (Z_to_bv 64 (4 * (nx - ny))) s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f9c0) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00m0@C7096915042.244 D33876909647.243D63873442836.243K66327680928.244L12691537071.1  L13843160408.5  L14940460802.5  L17162795167.5  L19133426325.6  L27153772539.5  L29832375856.1  L35663928186.7  L40066488116.5  L40374229935.6  L46331316844.15 L47887867615.6  L49168952290.8  L5376886168.7   L55990716303.233L57625758213.5  L58209102511.1  L59308550125.6  L59310648043.7  L59667784614.1  L60098763854.3  L6106346273.0   L62018535662.1  L63883836664.5  L66199197884.5  L66330468140.4  L8532400182.5   L8929159528.235 L8929620893.232 L9356559676.11  P40077402040.245P66327680928.244Q10812129647.239Q11801279589.243Q19991027068.245Q26295627581.239Q31205954960.245Q3375676648.245 Q33874924623.244Q33877164610.239Q33889765055.239Q40217825408.245Q45057547415.245Q48467890406.245Q49472925079.236Q49698585326.243Q50458135125.239Q51003780618.236Q51120983794.239Q51135677050.242Q51337909069.236Q63871233556.244Q63873185817.239Q63883819088.239Q63885703535.236Q63885753572.239Q8943555749.236 00000101L02]02^02b03803L03^04504B04F04[04\05205j06=06\07407g08708;08O08j08n09809909<09N09`09a0:30;O0<k0=V0?30?40?l0@U0@V0A<0A=0A>0B90C10Ci0Cj0Ck0Cl0D`0ET0F:0Fk0G]0HQ0II0J:0Jh0KV0LD0M20MXFS2LF2ra2sp3LFB2dA2FB3sp14gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3SPR2F03idx2wv4SP1R2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy3NY12VX3SPR2F03idx2wv4SP1R2Z03PZ03IDXFS2FBS4PHIb4PHIr5PHIR01v2HVS3dLX2nx3NXL3dX43NK4S2dZ2nx2ny3idx3IDXS2dZ2nx2ny4LENZ3idx3IDXS1D3dLX2vy2VXS2dZS1R3HIA1h2sp2lo3TOP1HFS2dA2nx2ny3NY13NYX3NXAS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dZ2nx2ny3ALO3idx3PZC3IDXS1D3dLX2dY2vy2VY2VXS3dLX2nx2ny3NY13NYX3NXL3dX43NK4S1d3FRb2D03FRr4FRR01f2HFS2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy2VX3idxS3dLX2vy3VY03XBDS2FBS1D3dLX2vy3VY02VX2NNS2dZ2nx2ny4LENZ3idx3IDX3NTHS2dZS1R2lo3LOSSS1RS2dZ2nx2ny3idx3IDXS2dZ2nx2ny3idx3IDXFS2dZ2nx2ny3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy3NY13NYX2VX3ACV3SPR2F04SP1R2Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1D3dLX2dZ2nx2ny2vy3NY13NYX2VX3ACV3SPR2F04SP1R2Z03PZ03PZC3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3ALO3idx2wv3PZCFS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx2wvFS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idxFFS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idx2wvS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxFFFS2LF2sp2lo3LFB3sp14gapn3SP11D3dLX2dZ2nx2ny2vy2VX3idxS1R2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3ACV3idx3PZC3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idxS2LF2lo3LFB3sp14gapn3LOC1D3dLX2dZ2nx2ny2vy2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3PZ03idx3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx3IDX5HBarrS2LF3LFB2dA4gapn3NA01D3dLX2dZ2nx2ny2vy3NY13NXA2NZ2VX3idxS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx2wv3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy3NY12VX3idx3IDXS2LF3LFB4gapn1D3dLX2dZ2nx2ny2vy2VX3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF PHIR0 FRR0 NA0 ASNG"] Lemma dv_L1body : forall D, dvL1_stmt D ->
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c128 c136 t2pad gb u0 u1 u2 jq v f (nx ny k vy : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny <= nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    md_sg dY = 1 -> mpd_val dY = vy -> 0 < vy -> vy <= mpd_val dLX < Z.of_nat (S D) * vy -> 0 <= k < 32 ->
    UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    mpd_val dLX < dvBT -> mpd_abs dY < 2 ^ (32 * nx) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 ny) (Z_to_bv 64 (4 * (nx - ny))) s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9f564) fc None mq (seg_rom asegs)).
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
    zstep. zstep. zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
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
    match goal with H : rw_cells asegs m3 (sp1 + 168) _ |- _ => rename H into CZ3 end.
    set (dZ3 := set_limbsA dZ (upd (md_limbs dZ) (Z.to_nat idx) wv)).
    assert (MLZ3 : mpd_at asegs m3 LBq dZ3).
    { split; [| exact SGZ]. unfold dZ3, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAZ.
      split; [exact CZ3|]. split; [rewrite <- EAZ; exact Z8|]. split; [rewrite <- EAZ; exact Z0|]. split; [rewrite upd_length; exact LENZ|]. split; [exact NRZ|].
      rewrite OZH. split; [exact NZ1|]. split; [exact INZ|]. split; [exact PZ16| exact UAZ']. }
    assert (HPA3 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] mq m3).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m3 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPZ)| clear - IDX; lia| clear - IDX; lia]. }
    assert (CST3 : CSTA m3 hq LBq (set_nth 2 [dLX; dY; dZ; dT] dZ3) dX (DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
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
    eapply (call_sub_ng_ll m3 hq LBq _ _ v f 0%nat 1%nat dLX dY 0x9f59c); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAY; reflexivity).

    - discriminate.
    - rewrite EAX. clear. lia.
    - rewrite EAY. clear. lia.
    - clear - HV PHIR0. unfold AVOL_CALL in PHIR0. lia.
    - clear - HF FRR0 D0. unfold fr_charge in FRR0. lia.
    - clear. lia.
    - intros m4 h4 LB4 dX4 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
      pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo0) as KINV4.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      assert (EAX4 : md_addr dX4 = FB + 32) by (rewrite EAL4; exact EAX).
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
        eapply dv_ERR16; [exact CST4| exact EAX4| exact EAY| exact EAZ| exact EAD| exact UW4| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L26466616993.0L36799126446.5L36799158313.5L40148281766.4L59308944635.400000100A00Q00^00iSS1D3dLX2vy2VX2GTS1D3dLX2vy2VX2EQS1D3dLX2vy2VXS3dLX2vy2VX". (* [comment removed for export] *)
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
    eapply (call_cmp_ll mq hq LBq [dLX; dY; dZ; dT] _ v f 0%nat 1%nat dLX dY 0x9f560); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAY; reflexivity); [clear; lia|].
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

  Hypothesis CSR : mpi_core_shift_r_stmtA asegs R HIA A_MPI_CORE_SHIFT_R.

  (* [comment removed for export] *)
  Definition dvFIN_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f (k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSM c0 c8 c16 c24 c32 c40 (Z_to_bv 64 k) c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < (2 * md_n dA + 2) * dvBT ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 0x9fe38) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition dvLOOP_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c16 c128 c136 t2pad gb u0 u1 u2 jq v f (nx ny k : Z)
           xra t0 t2 a1 a2 a3 a4 a5 a6 a7 s10v s11v t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSM c0 (Z_to_bv 64 4294967295) c16 (Z_to_bv 64 (Z.lxor ny 18446744073709551615 * 4)) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) (Z_to_bv 64 nx) (Z_to_bv 64 k) (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 ny)
               c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LHeap -> md_own dY = LHeap -> md_own dZ = LHeap -> md_own dT = LHeap ->
    1 <= ny -> ny < nx -> nx <= md_n dA + 1 -> nx <= md_n dLX -> ny <= md_n dY -> md_n dZ = md_n dA + 2 -> md_n dT = md_n dA + 2 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + PHIr <= PHIb -> f + FRr <= FRb ->
    Z.abs (mpd_val dLX) < dvBT -> mpd_abs dY < 2 ^ (32 * ny) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 (Z_to_bv 64 4294967295) t2 (Z_to_bv 64 (nx - 1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 ny) s10v s11v (Z_to_bv 64 nx) t4 t5 t6)
          F (Z_to_bv 64 0x9fa08) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D35300034347.278D35300034347.279D60189065437.278D60189065437.279L11144352574.3  L12251719832.2  L14933635412.4  L17786231048.2  L18966192929.0  L19980016842.7  L24950277677.2  L25069779609.14 L26988105723.2  L28506342712.227L28632618922.2  L28923063823.271L31145622673.2  L31388771843.25 L32703425643.1  L32955855566.25 L34811591499.25 L3482839849.25  L35663928186.7  L36757749421.12 L37021784866.270L38060875949.12 L38235734261.1  L3883892771.1   L39172636981.0  L41663468825.228L42888674241.1  L42967148590.270L45174325948.1  L45189828850.11 L47990265982.2  L48700858022.1  L49304025233.2  L49442955282.12 L49516137587.3  L50574758523.3  L50574758523.4  L5156091514.227 L51841720889.1  L52258283942.1  L53576474186.25 L53577728712.1  L54424851272.25 L57442474248.4  L57698627611.2  L59308632045.3  L60098763854.3  L62018535662.1  L6493359339.25  L66426995373.12 L67372926033.2  L68148039674.270L68148167523.271L8931608776.1   L9080220944.4   L9356559676.11  P28627113325.278P28627113325.279P31146933846.278P31146933846.279P49296947798.278P49296947798.279P57432086862.278P57432086862.279P57713046236.278P57713046236.279P67365848726.278P67365848726.279Q10472012439.230Q15236711831.273Q15901829514.230Q15902156936.275Q19403282961.274Q21912967688.275Q28465177121.275Q28465177121.276Q33949380872.275Q3421936230.277 Q3421936230.278 Q34673271079.231Q37991880460.274Q44622834822.230Q522241846.231  Q5265442331.276 Q5265442331.277 Q53878776204.274Q57228775306.277Q57228775306.278Q63755623061.275Q66561961105.274Q67147694615.230Q67148022549.275Q68235297648.278Q68235297648.279Q7526424981.275 Q9874769418.273 00001Y03B04k06T06`06h07007707807P07X08708A08i08j09Z09[0:;0:?0:P0;]0<Z0<o0=X0?=0?f0?j0?n0?o0@S0@X0B40B80Bb0Bj0Bo0C00C50C?0CJ0CU0D90D=0DB0E:0E?0F70F80F90FE0FO0FR0GO0H80H90IQ0Ji0Jn0K=0Kh0MB0N\0P60QP0Rj0TD0Ua0W>0X;0Y80ZR0[l0\F0]70]Y0^G0_50_c0`R0aA0ao0bo0co0dI0e:0eT0en0f^0gN0h?0i<0j90jj0kX0l=0ln0md0nZ0oK109S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY2nx2ny3SPR2F03HTq4SP1R2Y03PY03ys24LEN22HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3dLX2dY2nx2ny3SPR2F03HTq4SP1R2Y03PY03ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3SPR2F04SP1R2Y03PY03ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3SPR2F04SP1R2Y03PY03ys24LEN22HB5Ha_st5Hl_stS2sp3sp13SP1S2lo3sp1S2ny3NY1S2nx2nySS1R3HIA1h2sp3TOP3sp13SP1S2dY3NRYS1R2lo3LOS2FB3sp12dY3ALO2F13PYFS3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx3NRYFS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3ys24LEN2FS1R2sp2lo3SLO3sp13SP12dY3NRA3PY0S2dYS3sp12dY3NRY4NY1'S1R5NEEDR2sp2lo3LOS3SLO2dA3sp13SP12dY2nx2ny3NY13NYX3NXA4NA983ALO4NY1'3PY03PYCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4NY1'4PY163PY03PYCS1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn3dLX2dY2nx2ny3NY13NYX3NXA3NYL4NA983ACV3SPR2F04SP1R2Y03PY03PYC3ys24LEN2S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2loS2dYSS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nxS3sp1S1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3NY13NYX3NYL3ACV3SPR2F04SP1R2Y03PY03PYC3ys24LEN22KTS2dYS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO3PYCS2dA3NA0S3sp1FS3sp1S2nx2ny2KTS2nx2ny3NYXS2nx2ny3NYXS2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nxS2dYS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY4NY1'3PY03PYCS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dY3ALO4LENY4NY1'3PY03PYCFFS2dY4NY1'2KNS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M2dY3ALO4NY1'4PY163PY03PYCS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3NY13NYL3ACV3SPR2F04SP1R2Y03PY03PYC3ys24LEN22KTS1R2LF2ra2sp3LFB2FB3sp14gapn3dLX2dY2nx2ny3NY13NYL3ACV3SPR2F04SP1R2Y03PY03PYC3ys24LEN22KTS3sp1S2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP13dLX2dY2nx2ny3ALO4LENY3PYC3ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP13dLX2dY2nx2ny3ALO4LENY3PYC3ys24LEN22HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13dLX2dY2nx2ny3ALO2F13ys24LEN22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2nxS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nxS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2S2LF3LFB3sp14gapn3dLX2dY2nx2ny4SP1R3ys24LEN22HBS2LF3LFB3sp14gapn3dLX2dY2nx2ny4SP1R3ys24LEN22HBS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3dLX2dY2nxS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF3LFB2FB4gapn3dLX2dY2nxS2LF3LFB2FB4gapn3dLX2dY2nxS2LF3LFB3sp14gapn3dLX2dY2nx2ny3ys24LEN22HB5Ha_stS2LF3LFB3sp14gapn3dLX2dY2nx2ny3ys24LEN22HB5Ha_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2S2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nxS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF3LFB3sp14gapn3dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3dLX2dY2nx2ny3ys24LEN22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13dLX2dY2nx2ny3ys24LEN2S2LF2lo3LFB3sp14gapn3LOC3dLX2dY2nx2ny3ys24LEN2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 SP1M GAP F64 FRSH CFB ESF LOC CSP FN64 FB8 NA0 CSR"] Lemma dv_M8 : dvFIN_stmt -> dvLOOP_stmt -> dvM8_stmt.
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
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (mq := mq) (i := 1%nat) (d := dY) as (MLY & NSY & _ & _ & _ & _ & HFY & _ & Y8 & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & Y0 & LENY & NRY & OWY) SGYd]. rewrite OYH in OWY. ddestruct OWY as (NY1' & INY & PY16 & UAY). rewrite EAY in CY, OYs. unfold mpi_cells in CY. unfold MPI_MAX_LIMBS in NRY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dY)) by (clear - NRY; lia). zstep.
    zstep. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NRY; lia); [exfalso; clear - KN NY1'; lia|].
    zstep. zstep.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_core_shift_r_stmtA, A_MPI_CORE_SHIFT_R in CSR.
      eapply CSR with (h := hq) (LB := LBq) (LF := LF1) (X := md_p dY) (n := md_n dY) (cnt := 32 * (nx - ny)) (lo := lo) (xs := md_limbs dY);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (eapply client_wrange_block; [apply in_or_app; left; exact INY| clear; lia| clear; lia]).
      all: try (rewrite HTq; clear - SP1 TOP; lia).
      all: unfold MPI_CORE_SHIFT_R_STACK_A; try (clear - NRY NY1' LENY PY16 PY0 PYC ALO LOS SLO SP1 SP1M NEEDR NRA NY1 NYX NXA NA98; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CSR-PRE-LEFT:" g end ]. }

    cbv beta. intros ms' PO. unfold mpi_core_shift_r_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & UA2 & LEN2 & _ & LV2 & ST2 & HH2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    lazymatch type of UA2 with u32arr _ _ _ ?l => set (ys2 := l) in * end.
    set (dY2 := set_limbsA dY ys2).
    assert (CY2 : rw_cells asegs m2 (FB + 64) [C8 (Z_to_bv 64 (md_p dY)); C2 (Z_to_bv 64 (md_sg dY)); C2 (Z_to_bv 64 (md_n dY)); C4 (md_pad dY)]).
    { eapply rw_cells_transport; [exact CY| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add fst snd]. clear - PYF F1 ALO LOS SLO SP1 NEEDR LOC. lia. }
    assert (MLY2 : mpd_at asegs m2 LBq dY2).
    { split; [| exact SGYd]. unfold dY2, set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. unfold mpi_cells. rewrite EAY.
      split; [exact CY2|]. split; [rewrite <- EAY; exact Y8|]. split; [rewrite <- EAY; exact Y0|]. split; [rewrite LEN2; exact LENY|]. split; [unfold MPI_MAX_LIMBS; exact NRY|].
      rewrite OYH. split; [exact NY1'|]. split; [exact INY|]. split; [exact PY16| exact UA2]. }
    assert (HPA2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dY, md_p dY + 4 * md_n dY); (lo, sp1)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_cons; [cbn [fst snd]| apply Forall_nil]].
      - eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPY)| clear; lia| clear; lia].
      - eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]. }
    assert (CST2 : CSTA m2 hq LBq (set_nth 1 [dLX; dY; dZ; dT] dY2) dX (DCSL c0 c8 c16 c24 nx ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_upd_l asegs R HIA) with (mq := mq) (d := dY) (WX := [(md_p dY, md_p dY + 4 * md_n dY); (lo, sp1)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OYH| clear; lia]| apply Forall_cons; [right; right; cbn [fst snd]; clear; lia| apply Forall_nil]]. }
    cbn [set_nth] in CST2.
    assert (UW2 : UWCD m2).
    { eapply uwcd_munch; [exact UW| exact MU2|]. apply Forall_cons; [cbn [snd]; clear - PYC ALO LOS SLO SP1 NEEDR; lia| apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil]]. }
    assert (YB2 : mpd_abs dY2 < 2 ^ (32 * ny)).
    { pose proof MLY2 as [(_ & _ & _ & HL2 & _) _]. pose proof MLY as [(_ & _ & _ & HLY0 & _) _]. rewrite (mpd_abs_lval dY2 HL2). unfold dY2, set_limbsA. cbn [md_limbs md_n].
      rewrite LV2. rewrite <- (mpd_abs_lval dY HLY0).
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; [clear; lia| clear - NYX; lia]|]. rewrite <- Z.pow_add_r by (clear - NY1 NYX; lia).
      replace (32 * (nx - ny) + 32 * ny) with (32 * nx) by (clear; lia). exact YBD. }
    assert (BTP : 0 < dvBT) by (unfold dvBT; apply Z.pow_pos_nonneg; [clear; lia| clear - NA0; lia]).
    clear MU WM SPC MU2 WM2.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as (CH2 & _ & _ & _ & _).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as OK2.
    pose proof CH2 as CH2'. unfold A_mpi_div_mpi_C.DCS in CH2'. repeat (apply Forall_cons_iff in CH2'; destruct CH2' as [?CK CH2']). cbn [fst snd] in *. unfold A_mpi_div_mpi_C.dv_sp in *.
    pose proof (munch_refl [(sp1, sp1 + 152)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - NY1 NYX NXA NA98; lia).

    - (* [comment removed for export] *)
      unfold dvFIN_stmt in KFIN.
      eapply KFIN with (k := k); [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact HK| exact UW2| exact BPOS| exact HV| exact HF| clear - XBD BTP NA0; nia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite ?Z.shiftl_mul_pow2 in * by (clear; lia). change (2 ^ 2) with 4 in *.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
      match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
      match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
      assert (CST3 : CSTA m3 hq LBq [dLX; dY2; dZ; dT] dX
                (DCSM c0 (Z_to_bv 64 4294967295) c16 (Z_to_bv 64 (Z.lxor ny 18446744073709551615 * 4)) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) (Z_to_bv 64 nx) (Z_to_bv 64 k) (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 ny)
                      c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
      { eapply S_cs_store with (mq := m2) (a := sp1) (b := sp1 + 152); try eassumption.
        - clear; lia.
        - left. clear - SP1. lia.
        - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; unfold dY2, set_limbsA; cbn [md_addr]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
        - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
        - eapply S_dcs_ok; [exact OK2| reflexivity| reflexivity| reflexivity| reflexivity]. }
      assert (UW3 : UWCD m3) by (eapply S_uwcd_store; [exact UW2| exact MU| clear; lia]).
      replace (Z_to_bv 64 (nx + -1)) with (Z_to_bv 64 (nx - 1)) by (f_equal; clear; lia).
      unfold dvLOOP_stmt in KLOOP.
      eapply KLOOP with (nx := nx) (ny := ny) (k := k); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact NY1| clear - KT; lia| exact NXA| exact NXL| exact NYL| exact NZ| exact NT| exact HK| exact UW3| exact BPOS| exact NA98| exact HV| exact HF| exact XBD| exact YB2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB AE BE HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SXA IA2 IB2 ESA ESB PHIR0 FRR0 BM_PHI BM_FR NA0 NB0 OA OB CALLOC AMS GROW BITLEN SHL CMP ASNG CSR"] Lemma dv_M : dvFIN_stmt -> dvLOOP_stmt ->
    A_mpi_div_mpi_S_c24.dv_MAIN_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn.
  Proof.
    intros KFIN KLOOP. unfold A_mpi_div_mpi_S_c24.dv_MAIN_stmt. intros until t6. intros CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 UW BPOS BLE.
    eapply (dv_MAIN (dv_M2 (dv_M3 (dv_M4 (dv_M4b (dv_M5 (dv_M6 (dv_LOOP1 (dv_M8 KFIN KLOOP)))))))));
      [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| exact OX0| exact OY0| exact OZ0| exact OT0| exact UW| exact BPOS| exact BLE].
  Qed.

  End Fr.
  End Call.
End WalkM.
