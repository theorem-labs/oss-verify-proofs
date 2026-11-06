(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_lset P_mpi_mul_int_W P_mpi_div_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_core_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_cmp_int A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24 A_mpi_div_mpi_M_c24 A_mpi_lset A_mpi_lset_ng A_mpi_mul_int A_mpi_mul_int_stmtV A_mpi_mul_int_ng A_mpi_cmp_mpi_raw.
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

Section WalkL.
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

  (* [comment removed for export] *)
  Hypothesis COPYX : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.
  Hypothesis LSETNG : mpi_lset_ng_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MULNG : mpi_mul_int_ng_stmtA asegs R HIA A_MPI_MUL_INT.
  Hypothesis MULI : mpi_mul_int_stmtA_v asegs R HIA A_MPI_MUL_INT.   (* [comment removed for export] *)
  Hypothesis CMPR : mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis CMPI : mpi_cmp_int_stmtA asegs AL A_MPI_CMP_INT.
  Hypothesis ASM : add_sub_mpi_stmtA_o_c (-1) asegs R HIA A_ADD_SUB_MPI.
  Hypothesis ASP : add_sub_mpi_stmtA_o_c 1 asegs R HIA A_ADD_SUB_MPI.
  (* [comment removed for export] *)
  Variables (slo : Z).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO2 : slo <= lo.
  Hypothesis SSH0 : sshad asegs AL m slo (bv_unsigned sp).

  (* [comment removed for export] *)
  Variables (PF FF : Z).
  Hypothesis PF0 : 4 * AVOL_CALL <= PF.
  Hypothesis FF0 : 4 * fr_charge (d + 1) <= FF.
  Definition dvcMUL : Z := grow_PHI (MPI_MAX_LIMBS + 1) + grow_PHI MPI_MAX_LIMBS.
  Definition dvcSHL : Z := grow_PHI (2 * MPI_MAX_LIMBS).
  Definition dvcAS : Z := grow_PHI MPI_MAX_LIMBS + 3 * grow_PHI (MPI_MAX_LIMBS + 2).
  Definition dvcCP : Z := grow_PHI MPI_MAX_LIMBS.
  Definition dvVrnd : Z := dvcMUL + 2 * dvcSHL + 2 * dvcAS + dvcCP.
  Definition dvFrnd : Z := mul_int_FR (d + 1) + 2 * shift_l_FR + 2 * add_sub_FR (d + 1) + copy_FR 0.
  Definition dvVr (n : nat) : Z := Z.of_nat n * dvVrnd + PF.
  Definition dvFr (n : nat) : Z := Z.of_nat n * dvFrnd + FF.

  Ltac unfold_bud := unfold dvVr, dvFr, dvVrnd, dvFrnd, dvcMUL, dvcSHL, dvcAS, dvcCP, mul_int_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, copy_PHI, grow_PHI, copy_FR, grow_FR, shift_l_FR, calls_FR, fr_charge, MPI_MAX_LIMBS in *; unfold AVOL_CALL in *.

  (* [comment removed for export] *)
  Local Notation M_call_copy_l := (A_mpi_div_mpi_M_c24.call_copy_l R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS FB sp1 gapn SP1 SP1M F64 FRSH ESF BUD BUDF C24H COPYX).
  Local Notation M_call_xop_l := (A_mpi_div_mpi_M_c24.call_xop_l R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS D0 FB sp1 gapn SP1 SP1M F64 FRSH ESF BUD BUDF C24H).
  Local Notation M_cs_stack_step := (A_mpi_div_mpi_M_c24.cs_stack_step R HIA IMG NEEDR h LB LF ra sp m lo LOS SLO TOP LFB dX d es DIMG H0M XW W0AS FB sp1 gapn SP1 F64 FRSH ESF).
  Local Notation M_locals_apart := (A_mpi_div_mpi_M_c24.locals_apart R HIA NEEDR h LB LF ra sp m lo LOS SLO TOP LFB dX es XW FB sp1 gapn SP1 FRSH).
  Local Notation M_uwcd_munch := (A_mpi_div_mpi_M_c24.uwcd_munch R HIA IMG NEEDR h sp lo LOS SLO d sp1 SP1).
  Local Notation M_out_heapA := (A_mpi_div_mpi_M_c24.out_heapA LF ra sp LFB FB sp1 gapn).
  Local Notation M_dv_ERR := (A_mpi_div_mpi_M_c24.dv_ERR R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF PF FF PF0 FF0).
  Local Notation set_limbsA := A_mpi_div_mpi_M_c24.set_limbsA.
  Local Notation dvBT := (A_mpi_div_mpi_M_c24.dvBT dA).
  Local Notation shl_fresh := A_mpi_div_mpi_M_c24.shl_fresh.
  Local Notation val_lvalA := (A_mpi_div_mpi_M_c24.val_lvalA).

  (* [comment removed for export] *)
  Local Notation K_local_facts := (A_mpi_client2.cs_local_facts asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es LOS LOC CSP TOP FRSH FN64 XW).
  Local Notation K_binop_l := (A_mpi_client2.cs_binop_l asegs R HIA HNDk DIMG h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es H0M LOS LOC CSP TOP FRSH FN64 FB8 XW W0AS ESF).
  Local Notation K_upd_l := (A_mpi_client2.cs_upd_l asegs R HIA HNDk DIMG h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es H0M LOS LOC CSP TOP FRSH FN64 FB8 XW W0AS ESF).

  Local Notation C_aobj_merge := (A_mpi_div_mpi_C.aobj_merge_dv R LF ra sp LFB FB sp1 gapn).
  Local Notation S_aobj_of_sshad := (A_mpi_div_mpi_S_c24.aobj_of_sshad_s R LF ra sp LFB FB sp1 gapn).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L35655538626.7L60098763854.300000I00SS1R3HIA1h2sp2lo3TOP5HTOP0S1R2lo3LOS". (* [comment removed for export] *)
  #[using="LOS TOP H0M CFB"] Lemma kit_facts : forall mq hq LBq ls dW CS0 v f, CSTA mq hq LBq ls dW CS0 DV_FSH v f ->
    Forall (fun c => rw_cells asegs mq (fst c) (snd c)) CS0 /\ rw_cells asegs mq (Z.shiftr FB 3 + al_sb AL) DV_FSH /\ mem_inv asegs mq /\ stk asegs mq lo sp1 /\ HM asegs R HIA hq LBq LF1 mq
    /\ htop asegs R HIA hq = htop asegs R HIA h /\ hstkhi asegs R HIA hq = hstkhi asegs R HIA h /\ hflag asegs R HIA hq = hflag asegs R HIA h
    /\ (forall a, hcs asegs R HIA h a -> hcs asegs R HIA hq a) /\ havol asegs R HIA hq <= havol asegs R HIA h + v /\ hfr asegs R HIA hq <= hfr asegs R HIA h + f
    /\ Forall (COK ls) CS0
    /\ cs_ok AL (hcs asegs R HIA hq) /\ 0 <= al_sb AL < 2^64
    /\ crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo) /\ crange (hcs asegs R HIA hq) FB 256
    /\ ainv_laws AL (AIh asegs R HIA hq) /\ kinv_laws (AIh asegs R HIA hq) (hcs asegs R HIA hq) (KF asegs R HIA hq mo0).
  Proof.
    intros mq hq LBq ls dW CS0 v f CST.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (A_mpi_client2.cs_chunks_ok asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as OKq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    repeat (split; [eassumption|]). split; [exact (cs_ok_sb _ _ CSOKq)|].
    split; [eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M) as HTOP0; clear - HTOP0 TOP; lia]|].
    split; [eapply crange_mono; [exact HCSq| exact CFB]|].
    split; [exact (AIh_laws asegs R HIA hq)| exact (KF_kinv asegs R HIA hq mo0)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac kit_pre CST mq hq :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    pose proof FRSH as (F0 & F1 & F2 & F3);
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia);
    destruct (kit_facts _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq & HTq & HSq & HFq & HCSq & HVq & HFRq & OKq & CSOKq & SB64q & SCSq & CFBq & LAWS & KINV).
  (* [comment removed for export] *)
  Ltac kit_chunks CHq :=
    let CHq' := fresh "CHq'" in
    pose proof CHq as CHq'; unfold A_mpi_div_mpi_C.DCS in CHq';
    apply Forall_cons_iff in CHq'; destruct CHq' as [SPC CHq']; apply Forall_cons_iff in CHq'; destruct CHq' as [T2Cq CHq']; apply Forall_cons_iff in CHq'; destruct CHq' as [ZCq CHq'];
    apply Forall_cons_iff in CHq'; destruct CHq' as [GAPC CHq']; apply Forall_cons_iff in CHq'; destruct CHq' as [SAVE CHq']; apply Forall_cons_iff in CHq'; destruct CHq' as [FHD CHq'];
    apply Forall_cons_iff in CHq'; destruct CHq' as [TPC CHq']; apply Forall_cons_iff in CHq'; destruct CHq' as [JQC _];
    cbn [fst snd] in SPC, T2Cq, ZCq, GAPC, SAVE, FHD, TPC, JQC; unfold A_mpi_div_mpi_C.dv_sp in SPC.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L66117246296.10200000OS2LF2ra2sp3LFB2FB3sp14gapn2PF1n". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma dvVr_S : forall n, dvVr (S n) = dvVrnd + dvVr n.
  Proof. intros n. unfold dvVr. rewrite Nat2Z.inj_succ. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L48078396760.10200000OS2LF2ra2sp3LFB2FB3sp14gapn2FF1n". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma dvFr_S : forall n, dvFr (S n) = dvFrnd + dvFr n.
  Proof. intros n. unfold dvFr. rewrite Nat2Z.inj_succ. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma dvVr_ge : forall n, PF <= dvVr n.
  Proof. intros n. unfold dvVr, dvVrnd, dvcMUL, dvcSHL, dvcAS, dvcCP, grow_PHI, MPI_MAX_LIMBS, AVOL_CALL. nia. Qed.
  Lemma dvFr_ge : forall n, FF <= dvFr n.
  Proof using D0. intros n. unfold dvFr, dvFrnd, mul_int_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, copy_FR, shift_l_FR, calls_FR, fr_charge. clear - D0. nia. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12128799109.1 L19980016842.7 L23929348277.6 L52101693566.17L62037211595.7 L6203936179.1  L66151427842.16L66668349941.1 L9356559676.11 L9838743115.2  00000300K00`01\02702<02X02[03F03PS1fS1R3HIA1h2sp3TOP3sp13SP1S1R2sp2lo3SLO3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2dl3DLF3ALO2F11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 LSETNG"] Lemma call_lset_ng_l : forall mq hq LBq ls CS0 v f i dl (z : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_addr dl + 16 <= FB + 256 -> 1 <= md_n dl -> -2^31 <= z < 2^31 ->
    UWCD mq -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr dl) -> a1v = Z_to_bv 64 z ->
    (forall m3 h3 LB3 dl' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls dl') dX CS0 DV_FSH v f -> lset_R z dl LBq r dl' -> mpd_at asegs m3 LB3 dl' -> md_addr dl' = md_addr dl -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_LSET) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NTH DLF N1 ZR UW RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct K_local_facts with (mq := mq) (i := i) (d := dl) as (ML & NSL & XWL & LLO & _ & _ & _ & _ & _ & _ & OL); try eassumption.
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
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "LSET-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dl3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls dl3) dX CS0 DV_FSH (v + 0) (f + 0)).
    { eapply K_binop_l with (i := i) (dX := dl) (mq := mq) (hq := hq); try eassumption.
      ddestruct RR3 as (_ & _ & KK). exact KK. }
    replace (v + 0) with v in CST3 by (clear; lia). replace (f + 0) with f in CST3 by (clear; lia).
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DLF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L18174096749.400000BS2LB4C24H3LBq4C24q". (* [comment removed for export] *)
  #[using="HNDk C24H"] Lemma cs_c24 : forall mq hq LBq dLX dY dZ dT CS0 v f, CSTA mq hq LBq [dLX; dY; dZ; dT] dX CS0 DV_FSH v f -> cnt24 LBq + 4 <= C24MAX.
  Proof.
    intros mq hq LBq dLX dY dZ dT CS0 v f CST.
    pose proof (A_mpi_client2.cs_cnt24 asegs R HIA HNDk h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as C24q.
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in C24q. unfold C24_DIV_MPI in C24H. clear - C24q C24H. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12128799109.1 L19980016842.7 L33860051774.2 L39261961171.9 L39272446419.9 L40907430069.6 L41650118032.6 L4781719053.2  L52101693566.17L62037211595.7 L6203936179.1  L66151427842.16L66668349941.1 L9356559676.11 L9838743115.2  00000300K00S01101P01e02902?03;03V03[04704:04e04oS1fS1R3HIA1h2sp3TOP3sp13SP1S2dl3VIIS1R3HIA1h4PHIb3BUD2hq1v2HV3HVqS1R3HIA1h3FRb4BUDF2hq1f2HF4HFRqS1R2sp2lo3SLO3sp13SP1S1R2FB2dl3DIF3ALO2F1S1d2D0S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2dl3DIF3ALO2F11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF MULNG"] Lemma call_mul_ng_l : forall mq hq LBq ls CS0 v f i dl (b U : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_addr dl + 16 <= FB + 256 -> md_own dl = LHeap ->
    0 <= U -> U + 1 <= md_n dl -> (forall j w, U <= j -> nth_error (md_limbs dl) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0) ->
    0 <= b < 2^32 -> bv_unsigned a2v mod 2^32 = b -> (bv_unsigned a2v = 0 <-> b = 0) -> cnt24 LBq + 4 <= C24MAX ->
    UWCD mq -> v <= PHIb -> f <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr dl) -> a1v = Z_to_bv 64 (md_addr dl) ->
    (forall m3 h3 LB3 dl' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls dl') dX CS0 DV_FSH v f -> mul_int_Rz b LBq dl dl r dl' -> mpd_at asegs m3 LB3 dl' -> md_addr dl' = md_addr dl -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2v a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_MUL_INT) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI DIF OI U0 UN UZ BR A2B A2Z C24q UW HV HF RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct K_local_facts with (mq := mq) (i := i) (d := dl) as (MI & NSI & XWI & LLI & CRI & CRLI & HFI & SLI & _ & ASI & OIs); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _).
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dl) _ _ HHq INI SLI) as VII.
    pose proof MULNG as SPEC. unfold mpi_mul_int_ng_stmtA in SPEC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := dl) (dA := dl) (b := b) (U := U) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact MI | exact NSI | exact XWI | exact LLI | exact CRI | exact CRLI | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | exact U0 | exact UN | exact UZ | exact BR | exact A2B | exact A2Z | reflexivity
              | (rewrite HSq; exact UW)
              | lazymatch goal with
                | |- mpd_sep dl dl => left; reflexivity
                | |- 1 <= md_n dl => exact N1I
                | |- opnd_sep dl dl _ _ => split; [intros _; clear - VII; lia| split; [intros _; clear - VII; lia| split; [left; reflexivity| split; [exact ASI| exact LLI]]]]
                | |- lo <= sp1 - _ - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ dl => split; [exact OIs| intros EO; exfalso; exact (NSI EO)]
                | |- md_own dl = LStatic -> _ => intros EO; exfalso; exact (NSI EO)
                | |- _ <> _ -> _ => intros KK; exfalso; apply KK; reflexivity
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold mul_int_PHI0; clear - HVq BUD HV; lia
                | |- uw_obj _ (md_addr dl) 16 _ => left; split; [clear - DIF F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold mul_int_FR0; clear - HFRq BUDF HF; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_MUL_INT; exact C24q
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "MULNG-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & di3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls di3) dX CS0 DV_FSH (v + 0) (f + 0)).
    { eapply K_binop_l with (i := i) (dX := dl) (mq := mq) (hq := hq); try eassumption.
      destruct RR3 as [_ (_ & _ & KK & _)]. exact KK. }
    replace (v + 0) with v in CST3 by (clear; lia). replace (f + 0) with f in CST3 by (clear; lia).
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DIF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L18359781713.10L19980016842.7 L20803336933.11L25148064707.3 L35590224338.3 L40907430069.6 L4223562214.6  L4781719053.2  L52101693566.17L60162046265.6 L62037211595.7 L6203936179.1  L66151427842.16L9356559676.11 L9838743115.2  00000Q00i01M01X01c02802L02R03N03b04=04B04^05I05SS1R3HIA1h1d3FRb4BUDF2hq1f2HF4HFRqS1R3HIA1h2sp3TOP3sp13SP1S1R3HIA1h4PHIb3BUD2hq1v2di2dj2HV3HVqS2di2dj3VJIS2di2dj3VIJS1R2sp2lo3SLO3sp13SP1S1R2FB2dj3DJF3ALO2F1S1d2D0S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS1R2FB2di3DIF3ALO2F1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF MULI"] Lemma call_mul_ll : forall mq hq LBq ls CS0 v f i j di dj (b : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some di -> nth_error ls j = Some dj -> i <> j ->
    md_addr di + 16 <= FB + 256 -> md_addr dj + 16 <= FB + 256 -> md_own di = LHeap -> md_own dj = LHeap ->
    0 <= b < 2^32 -> bv_unsigned a2v mod 2^32 = b -> (bv_unsigned a2v = 0 <-> b = 0) -> cnt24 LBq + 4 <= C24MAX ->
    UWCD mq -> v + mul_int_PHI di dj <= PHIb -> f + mul_int_FR (d + 1) <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (md_addr dj) ->
    (forall m3 h3 LB3 di' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls di') dX CS0 DV_FSH (v + mul_int_PHI di dj) (f + mul_int_FR (d + 1)) -> mul_int_R b LBq di dj r di' -> mpd_at asegs m3 LB3 di' -> md_addr di' = md_addr di -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2v a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_MUL_INT) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI NJ NE DIF DJF OI OJ BR A2B A2Z C24q UW HV HF RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & XWI & LLI & CRI & CRLI & HFI & SLI & _ & ASI & OIs); try eassumption.
    edestruct K_local_facts with (mq := mq) (i := j) (d := dj) as (MJ & NSJ & _ & LLJ & CRJ & CRLJ & HFJ & SLJ & _ & ASJ & OJs); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _). ddestruct (HFJ OJ) as (PJ0 & PJC & INJ & N1J & _).
    destruct (M_locals_apart _ _ _ _ _ _ _ _ i j di dj CST NI NJ NE) as [SAP LAP].
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INJ SLI) as VIJ.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dj) _ _ HHq INI SLJ) as VJI.
    pose proof MULI as SPEC. unfold mpi_mul_int_stmtA_v in SPEC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := di) (dA := dj) (b := b) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact MI | exact MJ | exact NSI | exact XWI | exact LLI | exact CRJ | exact CRLJ | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | exact BR | exact A2B | exact A2Z | reflexivity
              | (rewrite HSq; exact UW)
              | lazymatch goal with
                | |- mpd_sep di dj => right; exact SAP
                | |- opnd_sep di dj _ _ => split; [intros _; clear - VIJ; lia| split; [intros _; clear - VJI; lia| split; [right; right; right; exact (LAP OI OJ)| split; [exact ASJ| exact LLJ]]]]
                | |- lo <= sp1 - _ - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- mpd_aobjA _ _ _ _ di => split; [exact OIs| intros EO; exfalso; exact (NSI EO)]
                | |- mpd_aobjA _ _ _ _ dj => split; [exact OJs| intros EO; exfalso; exact (NSJ EO)]
                | |- md_own dj = LStatic -> _ => intros EO; exfalso; exact (NSJ EO)
                | |- _ <> _ -> md_own dj = LStatic -> _ => intros _ EO; exfalso; exact (NSJ EO)
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD HV; lia
                | |- uw_obj _ (md_addr di) 16 _ => left; split; [clear - DIF F1 ALO; lia| clear - D0; lia]
                | |- uw_obj _ (md_addr dj) 16 _ => left; split; [clear - DJF F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF; lia
                | |- cnt24 _ + _ <= C24MAX => unfold C24_MUL_INT; exact C24q
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "MUL-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & di3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls di3) dX CS0 DV_FSH (v + mul_int_PHI di dj) (f + mul_int_FR (d + 1))).
    { eapply K_binop_l with (i := i) (dX := di) (mq := mq) (hq := hq); try eassumption.
      destruct RR3 as [_ (_ & _ & KK & _)]. exact KK. }
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DIF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L18359781713.10L19980016842.7 L25148064707.3 L31667811433.11L35590224338.3 L4223562214.6  L4781719053.2  L50313707442.2 L52101693566.17L60162046265.6 L61214967477.6 L62037211595.7 L6203936179.1  L66151427842.16L9356559676.11 L9838743115.2  00000Q00i01401X01c02702=02E03A03U03j04E04J04f05Q05[S1R3HIA1h1d3FRb4BUDF2hq1f2HF4HFRqS1R3HIA1h2sp3TOP3sp13SP1S2di2dj3VJIS1R3HIA1h4PHIb3BUD2hq1v2di2dj2HV3HVqS2di2dj3VIJS1R2FB2dj3DJF3ALO2F1S1d2D0S2di3VIIS1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS1R2FB2di3DIF3ALO2F1S1R2sp2lo3SLO3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 FB8 BUD BUDF C24H"] Lemma call_addsub_ll : forall flip, add_sub_mpi_stmtA_o_c flip asegs R HIA A_ADD_SUB_MPI ->
    forall mq hq LBq ls CS0 v f i j di dj (retpc : Z)
      t0 t1 t2 a0v a1v a2v a3v a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> length ls = 4%nat -> nth_error ls i = Some di -> nth_error ls j = Some dj -> i <> j ->
    md_addr di + 16 <= FB + 256 -> md_addr dj + 16 <= FB + 256 -> md_own di = LHeap -> md_own dj = LHeap ->
    UWCD mq -> v + add_sub_PHI di di dj <= PHIb -> f + add_sub_FR (d + 1) <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (md_addr di) -> a2v = Z_to_bv 64 (md_addr dj) -> a3v = Z_to_bv 64 flip ->
    (forall m3 h3 LB3 di' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls di') dX CS0 DV_FSH (v + add_sub_PHI di di dj) (f + add_sub_FR (d + 1)) -> add_sub_mpi_R flip LBq di di dj r di' -> mpd_at asegs m3 LB3 di' -> md_addr di' = md_addr di -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2v a3v a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_ADD_SUB_MPI) fc None mq (seg_rom asegs)).
  Proof.
    intros flip SPEC0. intros until t6. intros CST LSL NI NJ NE DIF DJF OI OJ UW HV HF RPC RPE -> -> -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & XWI & LLI & CRI & CRLI & HFI & SLI & _ & ASI & OIs); try eassumption.
    edestruct K_local_facts with (mq := mq) (i := j) (d := dj) as (MJ & NSJ & _ & LLJ & CRJ & CRLJ & HFJ & SLJ & _ & ASJ & OJs); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _). ddestruct (HFJ OJ) as (PJ0 & PJC & INJ & N1J & _).
    destruct (M_locals_apart _ _ _ _ _ _ _ _ i j di dj CST NI NJ NE) as [SAP LAP].
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INI SLI) as VII.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INJ SLI) as VIJ.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dj) _ _ HHq INI SLJ) as VJI.
    pose proof SPEC0 as SPEC. unfold add_sub_mpi_stmtA_o_c, mpi_addsub_stmtA_o_c in SPEC.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SPEC with (h := hq) (LB := LBq) (LF := LF1) (dX := di) (dA := di) (dB := dj) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?(unsigned_lit retpc) by exact RPC;
        first [ exact HHq | exact HK1 | exact MI | exact NSI | exact XWI | exact LLI | exact CRI | exact CRLI | exact CRJ | exact CRLJ | exact STq | exact LOS | exact MIq | exact TPV | exact RPE | reflexivity
              | (left; exact MJ) | (rewrite HSq; exact UW)
              | lazymatch goal with
                | |- mpd_sep di di => left; reflexivity
                | |- mpd_sep di dj => right; exact SAP
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
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD HV; lia
                | |- uw_obj _ (md_addr di) 16 _ => left; split; [clear - DIF F1 ALO; lia| clear - D0; lia]
                | |- uw_obj _ (md_addr dj) 16 _ => left; split; [clear - DJF F1 ALO; lia| clear - D0; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "ADDSUB-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & di3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    assert (CST3 : CSTA m3 h3 LB3 (set_nth i ls di3) dX CS0 DV_FSH (v + add_sub_PHI di di dj) (f + add_sub_FR (d + 1))).
    { eapply K_binop_l with (i := i) (dX := di) (mq := mq) (hq := hq); try eassumption.
      destruct RR3 as [_ (_ & _ & KK & _)]. exact KK. }
    assert (UW3 : UWCD m3).
    { rewrite <- HSq. eapply S_uwc_presA; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha DIF F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply K; [exact CST3| exact RR3| exact MX3| exact (proj1 OUT3)| exact UW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L27940637589.11L29428324939.11L3482559548.11 L34979112605.7 L35663928186.7 L38235734261.1 L53035543507.6 L60098763854.3 L9080220944.4  L9356559676.11 00000W01>01j02E02Z02^03303=03L047S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACPS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HS2loS1R2lo3LOS2di3ALO3PICS1R2lo3LOSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH ESF LOC CSP FN64 CMPI"] Lemma call_cmpint_l : forall mq hq LBq ls CS0 v f i di (z : Z) (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some di ->
    md_own di = LHeap -> -2^31 <= z < 2^31 -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 z ->
    (forall m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m2 hq LBq ls dX CS0 DV_FSH v f -> (UWCD mq -> UWCD m2) ->
       aevtA asegs (KF asegs R HIA hq mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 (Z.sgn (mpd_val di - z))) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_CMP_INT) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI OI ZR RPC RPE -> -> K. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & _ & _ & _ & _ & _ & HFI & _ & _ & ASI & OI'); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & _).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT in CMPI. unfold A_MPI_CMP_INT.
      eapply CMPI with (CS := hcs asegs R HIA hq) (LB := LBq) (dX := di) (z := z) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (intros _; assumption).
      all: try (exact (art_alwf asegs R HIA)).
      all: try (exact (hm_abase asegs R HIA hq LBq LF1 mq HHq)).
      all: try (intros _; eapply hm_aobj_block; [exact HHq| eassumption]).
      all: try (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]).
      all: try (destruct ASI as [KK|KK]; [left; exact KK| right; exact KK]).
      all: try (intros _; left; clear - PIC ALO LOS; lia).
      all: try (clear - LOS ALO ACP SLO SP1 SP1M NEEDR; first [lia| Z.div_mod_to_equations; lia]).
      all: first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CMPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    destruct (M_cs_stack_step mq hq LBq _ _ _ _ _ _ lo CST MU2 WM2 MI2 ST2 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST2 UWK].
    eapply K; [exact CST2| exact UWK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L11109794231.9 L18788269472.1 L20108312707.4 L20964124776.1 L27285103933.6 L27650499371.1 L27940405558.7 L29428324939.5 L31034375991.6 L33449635840.2 L34979112605.7 L35663928186.7 L38235734261.1 L38551529394.0 L39268637205.0 L39332637397.0 L51725509627.1 L53035543507.6 L53577728712.1 L53886137103.2 L58782645332.1 L60098763854.3 L61977384168.3 L62335543678.0 L63041572022.7 L66151427842.16L9080220944.4  L9122136456.2  L9356559676.11 L9631767084.2  00000T00X00g00k01?01C01^02002C02M02h03=03A03B03C03D03H03]03b03i03m04704C04D04_05I05X05^06I06PS1R5NEEDR2sp2lo3SLO3sp13SP13slo4SLO2S2FBS2sp2lo3sp13SP1S2FBS1R2lo3LOS2FB3ALO2F1S2FBS1R5NEEDR2sp2lo3SLO3sp13SP1S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp3TOP2HTS3sp14SP1RS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HS2loSSSS2FBS1R2lo3LOS2di3ALO3PICS3sp1S2FB2F0S2FBS1R2lo3LOSS2sp3sp13SP1SS1R5NEEDR2sp2lo3SLO3sp13SP1S3sp12r04SP1M1q1r1H2H02q02H42FB3F642di3P16S2sp2lo3sp13SP1S1j2HjS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 SP1M F64 FRSH CFB ESF LOC CSP FN64 CMPR slo SLO1 SLO2 SSH0"] Lemma call_cmpraw : forall mq hq LBq ls c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq v f i di (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f -> nth_error ls i = Some di ->
    md_own di = LHeap -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (sp1 + 152) ->
    (forall m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m2 hq LBq ls dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f -> (UWCD mq -> UWCD m2) ->
       aevtA asegs (KF asegs R HIA hq mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1)
                  (Z_to_bv 64 (Z.sgn (md_sg di * lval (md_limbs di) (md_n di) - 1 * lval [u0; u1; u2] 3))) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_CMP_MPI_E) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI OI RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (A_mpi_client2.cs_pres asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as HP0.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (SSHq : sshad asegs AL mq slo (bv_unsigned sp)).
    { eapply (presA_sshad asegs R); [exact HP0| exact SSH0| exact SLO1|]. pose proof (hm_top asegs R HIA h LB LF m H0M) as HT. clear - HT TOP. lia. }
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'.
    apply Forall_cons_iff in CHq'. destruct CHq' as [SPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [T2Cq CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [ZCq CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [TPC CHq']. clear CHq' SPC ZCq GAPC SAVE FHD.
    cbn [fst snd] in T2Cq, TPC.
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & _ & _ & _ & _ & HFI & _ & _ & ASI & OI'); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _).
    dpose (A_mpi_div_mpi_S_c24.opv_of_mpd R HIA IMG hq LBq LF1 mq di HHq MI OI' ltac:(intros EO; exfalso; exact (NSI EO))) as (CI & _ & _ & I8 & BYI & LENI & NRI & PAI & SGI).
    unfold mpi_cells in CI.
    assert (OT2 : aobj asegs AL (hcs asegs R HIA hq) mq (sp1 + 152) 16).
    { apply (S_aobj_of_sshad (hcs asegs R HIA hq) mq slo (bv_unsigned sp) (sp1 + 152) 1 CSOKq SSHq);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCSq| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    assert (OTP : aobj asegs AL (hcs asegs R HIA hq) mq (FB + 128) 12).
    { replace 12 with (8 + 4) by reflexivity. apply C_aobj_merge; [clear; lia| clear; lia| |].
      - eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 128) 16 1 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| reflexivity|].
        intros j Hj. assert (j = 0%nat) as -> by (clear - Hj; lia). reflexivity.
      - eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 128 + 8) 17 4 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    assert (BYT : bytes_at asegs mq (FB + 128) (u32s [u0; u1; u2])) by (destruct TPC as [[_ KK] _]; exact KK).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { pose proof CMPR as SPEC. unfold mpi_cmp_mpi_raw_stmtA, A_MPI_CMP_MPI_E in SPEC. unfold A_MPI_CMP_MPI_E.
      eapply SPEC with (CS := hcs asegs R HIA hq) (lo := lo) (X := md_addr di) (P := md_p di) (n := md_n di) (sg := md_sg di) (xs := md_limbs di) (pad := md_pad di)
                       (Y := sp1 + 152) (Q := FB + 128) (n' := 3) (sg' := 1) (ys := [u0; u1; u2]) (pad' := t2pad);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact CI | exact BYI | exact LENI | exact NRI | exact SGI | exact I8 | exact T2Cq | exact BYT | exact MIq | exact OI' | exact OT2 | exact STq | exact CSOKq | reflexivity
              | exact (art_alwf asegs R HIA) | exact (hm_abase asegs R HIA hq LBq LF1 mq HHq)
              | (intros _; exact OTP) | (intros N1; exact (proj2 (PAI N1)))
              | (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia])
              | (destruct ASI as [KK|KK]; [left; exact KK| right; exact KK])
              | lazymatch goal with
                | |- md_n di = 0 \/ _ => right; split; [exact PI0| pose proof MI as [(_ & _ & _ & _ & _ & OWN) _]; rewrite OI in OWN; ddestruct OWN as (_ & _ & P16 & _); clear - P16; Z.div_mod_to_equations; lia]
                | |- 3 = 0 \/ _ => right; split; [clear - F0; lia| clear - F64; Z.div_mod_to_equations; lia]
                | |- 1 = 1 \/ _ => left; reflexivity
                | |- 0 <= 3 <= _ => clear; lia
                | |- (sp1 + 152) mod 8 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 + 152 + 16 <= lo \/ _ => right; clear; lia
                | |- 1 <= md_n di -> _ => intros _; left; clear - PIC ALO LOS; lia
                | |- 1 <= 3 -> _ => intros _; left; clear - F1 ALO LOS; lia
                | |- 0 <= lo => clear - LOS ALO ACP; lia
                | |- lo <= sp1 - _ => clear - SLO SP1 NEEDR; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CMPR-PRE-LEFT:" g end ] ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    destruct (M_cs_stack_step mq hq LBq _ _ _ _ _ _ lo CST MU2 WM2 MI2 ST2 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST2 UWK].
    eapply K; [exact CST2| exact UWK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation DCSO c0 c16 c40 ny k c128 c136 t2pad gb u0 u1 u2 jq :=
    (DCSM c0 (Z_to_bv 64 4294967295) c16 (Z_to_bv 64 (Z.lxor ny 18446744073709551615 * 4)) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) c40 (Z_to_bv 64 k) (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 ny) c128 c136 t2pad gb u0 u1 u2 jq).

  (* [comment removed for export] *)
  Definition linvk (kx : Z) (dLX dY dZ dT : mpd) (i ny : Z) : Prop :=
    md_addr dLX = FB + 32 /\ md_addr dY = FB + 64 /\ md_addr dZ = sp1 + 168 /\ md_addr dT = FB + 96
    /\ md_own dLX = LHeap /\ md_own dY = LHeap /\ md_own dZ = LHeap /\ md_own dT = LHeap
    /\ 1 <= ny /\ ny <= i /\ i <= md_n dA /\ i + 1 <= md_n dLX /\ ny <= md_n dY /\ md_n dZ = md_n dA + 2 /\ md_n dA + 2 <= md_n dT
    /\ mpd_abs dY < 2 ^ (32 * ny) /\ Z.abs (mpd_val dLX) + kx * dvBT < (2 * md_n dA + 2) * dvBT.
  (* [comment removed for export] *)
  Local Notation linv dLX dY dZ dT i ny := (linvk (2 * (i - ny + 1)) dLX dY dZ dT i ny).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L39172636981.0L47990265982.2000001009SS2dA3NA0". (* [comment removed for export] *)
  #[using="Type"] Lemma dvBT_pos : 0 <= md_n dA -> 0 < dvBT.
  Proof. intros NA0. unfold A_mpi_div_mpi_M_c24.dvBT. apply Z.pow_pos_nonneg; [clear; lia| clear - NA0; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis KFIN : A_mpi_div_mpi_M_c24.dvFIN_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn PF FF.

  (* [comment removed for export] *)
  Definition dvLH_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c16 c40 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t2 a1 a2 a3 a4 a5 a6 a7 s8v s10v s11v t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 c16 c40 ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny + 1 <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvVr n <= PHIb -> f + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 (Z_to_bv 64 4294967295) t2 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) s8v s10v s11v (Z_to_bv 64 (i + 1)) t4 t5 t6)
          F (Z_to_bv 64 0x9fa08) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition dvL5_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c40 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) c40 ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linvk (2 * (i - ny)) dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvVr n <= PHIb -> f + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) s8v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fd84) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L13270049643.9  L27515139277.9  L31813027332.6  L32867401788.212L33323923983.9  L3482964649.9   L3798149545.7   L42967147320.212L49000787209.4  L61436909883.2  L64503042233.6  L8632193901.1   L9356559676.11  Q27938377354.213Q33949708298.213Q35291925783.213Q63755819927.21300000;00E00Z01_01`01i02:03?03J03P03b03e04P05105R06606ZS3dLX1i3IXLS2dA1i3INAS2dA1i2ny3NY13NYI3INAS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX1i2ny3NY13NYI3INA4NA983SPR2F04SP1RFS1i2ny2KBS3FRb2FF1n1f2HF1HS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX1i2ny3NY13NYI3INA4NA983SPR2F04SP1RS1n1i2ny2RNS1i2nyS4PHIb2PF1n1v2HV1HS1iS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M D0 SP1 GAP FRSH CFB LOC KFIN"] Lemma dv_L5 : forall n, dvLH_stmt n -> dvL5_stmt n.
  Proof.
    intros n KH. unfold dvL5_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    ddestruct LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep; if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear - NY1 NYI INA NA98; lia).
    - unfold dvLH_stmt in KH.
      replace (Z_to_bv 64 i) with (Z_to_bv 64 (i - 1 + 1)) by (f_equal; clear; lia). replace (Z_to_bv 64 (i + -1)) with (Z_to_bv 64 (i - 1)) by (f_equal; clear; lia).
      eapply KH with (i := i - 1) (ny := ny) (k := k); [exact CST| | clear - RN; lia| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
      unfold linvk. repeat split; try assumption; try (clear - KB NY1 NYI INA IXL; lia).
      replace (2 * (i - 1 - ny + 1)) with (2 * (i - ny)) by (clear; lia). exact XB.
    - zstep. unfold A_mpi_div_mpi_M_c24.dvFIN_stmt in KFIN.
      eapply KFIN with (k := k); [exact CST| exact EAX| exact EAY| exact EAZ| exact EAD| exact OXH| exact OYH| exact OZH| exact OTH| exact HK| exact UW| exact BPOS| | |].
      + pose proof (dvVr_ge n). clear - H HV. lia.
      + pose proof (dvFr_ge n). clear - H HF. lia.
      + pose proof (dvBT_pos ltac:(clear - NY1 NYI INA; lia)) as BTP. clear - XB NYI BTP. nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L39728673364.3 L41019279709.3 L46330908273.13L59529426586.3 L62018535662.1 L9356559676.11 00000<00H01:01F01I024S2dl3idx3IDXS2dl3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dl3idx3IDX3ALO3PLCS2dl3idx3IDXS1RS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NEEDR ra mo0 LOS SLO TOP LFB HNDk DIMG H0M XW W0AS gapn SP1 F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma limb_store_kit : forall mq m3 hq LBq ls CS0 v f i dl idx xs',
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> nth_error ls i = Some dl -> md_own dl = LHeap -> 0 <= idx < md_n dl ->
    munch [(md_p dl + 4 * idx, md_p dl + 4 * idx + 4)] mq m3 -> wmono asegs mq m3 ->
    HM asegs R HIA hq LBq LF1 m3 -> mem_inv asegs m3 -> stk asegs m3 lo sp1 ->
    rw_cells asegs m3 (md_addr dl) (mpi_cells (md_p dl) (Z_to_bv 64 (md_sg dl)) (md_n dl) (md_pad dl)) ->
    u32arr asegs m3 (md_p dl) xs' -> length xs' = length (md_limbs dl) ->
    CSTA m3 hq LBq (set_nth i ls (set_limbsA dl xs')) dX CS0 DV_FSH v f /\ mpd_at asegs m3 LBq (set_limbsA dl xs') /\ (UWCD mq -> UWCD m3).
  Proof.
    intros mq m3 hq LBq ls CS0 v f i dl idx xs' CST NI OI IDX MU WM HH3 MI3 ST3 CZ3 UA3 LEN3. kit_pre CST mq hq.
    edestruct K_local_facts with (mq := mq) (i := i) (d := dl) as (ML & NSL & _ & _ & _ & _ & HFL & _ & L8 & _ & OLs); try eassumption.
    pose proof ML as [(CL & _ & L0 & LENL & NRL & OWL) SGL]. rewrite OI in OWL. ddestruct OWL as (NL1 & INL & PL16 & UAL).
    ddestruct (HFL OI) as (PL0 & PLC & _ & _ & PLF & _).
    assert (OPL : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dl) (4 * md_n dl)) by (eapply hm_aobj_block; [exact HHq| exact INL]).
    assert (ML3 : mpd_at asegs m3 LBq (set_limbsA dl xs')).
    { split; [| exact SGL]. unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CZ3|]. split; [exact L8|]. split; [exact L0|]. split; [rewrite LEN3; exact LENL|]. split; [exact NRL|].
      rewrite OI. split; [exact NL1|]. split; [exact INL|]. split; [exact PL16| exact UA3]. }
    assert (HPA3 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(md_p dl + 4 * idx, md_p dl + 4 * idx + 4)] mq m3).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m3 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH3| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      eapply crange_sub; [exact (aobj_crange _ _ _ _ _ _ OPL)| clear - IDX; lia| clear - IDX; lia]. }
    split; [| split; [exact ML3|]].
    - eapply K_upd_l with (mq := mq) (d := dl) (WX := [(md_p dl + 4 * idx, md_p dl + 4 * idx + 4)]); try eassumption; try reflexivity.
      apply Forall_cons; [right; left; cbn [fst snd]; split; [exact OI| clear - IDX; lia]| apply Forall_nil].
    - intros UW. eapply M_uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - IDX PLC ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L25148064707.3L26983617546.4L35590224338.3L9356559676.1100000;00H00S01>S2di2dj3VJIS2dj3AJ01a2HaS2di2dj3VIJS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS gapn SP1 SP1M F64 FRSH CFB ESF LOC CSP FN64 BUD BUDF C24H COPYX"] Lemma call_copy_ll : forall mq hq LBq ls CS0 v f i j di dj (retpc : Z)
      t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX CS0 DV_FSH v f -> length ls = 4%nat -> nth_error ls i = Some di -> nth_error ls j = Some dj -> i <> j ->
    md_addr di + 16 <= FB + 256 -> md_own di = LHeap -> md_own dj = LHeap ->
    UWCD mq -> v + copy_PHI dj <= PHIb -> f + copy_FR 0 <= FRb -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (md_addr dj) ->
    (forall m3 h3 LB3 di' (r : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m3 h3 LB3 (set_nth i ls di') dX CS0 DV_FSH (v + copy_PHI dj) (f + copy_FR 0) -> copy_Rx dj di LBq r di' -> mpd_at asegs m3 LB3 di' -> md_addr di' = md_addr di -> UWCD m3 ->
       aevtA asegs (KF asegs R HIA h3 mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1) (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m3 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_COPY) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST LSL NI NJ NE DIF OI OJ UW HV HF RPC RPE E0 E1 K. kit_pre CST mq hq.
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & XWI & LLI & CRI & CRLI & HFI & SLI & _ & ASI & OIs); try eassumption.
    edestruct K_local_facts with (mq := mq) (i := j) (d := dj) as (MJ & NSJ & _ & LLJ & CRJ & CRLJ & HFJ & SLJ & _ & ASJ & OJs); try eassumption.
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _). ddestruct (HFJ OJ) as (PJ0 & PJC & INJ & N1J & _).
    destruct (M_locals_apart _ _ _ _ _ _ _ _ i j di dj CST NI NJ NE) as [SAP LAP].
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr di) _ _ HHq INJ SLI) as VIJ.
    pose proof (A_mpi_client2.loc_vs_blk asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOS LOC CSP FRSH FN64 XW mq hq LBq (md_addr dj) _ _ HHq INI SLJ) as VJI.
    pose proof MJ as [(_ & _ & AJ0 & _) _].
    eapply (M_call_copy_l mq hq LBq ls CS0 v f i di dj retpc); [exact CST| exact LSL| exact NI| exact DIF| exact MJ| exact OJs| exact CRJ| exact CRLJ| right; exact SAP| | intros EO; exfalso; exact (NSJ EO)| exact UW| exact HV| exact HF| exact RPC| exact RPE| exact E0| exact E1| exact K].
    split; [intros _; clear - VIJ; lia|]. split; [intros _; clear - VJI; lia|]. split; [right; right; right; exact (LAP OI OJ)|]. split; [exact ASJ|]. split; [exact LLJ|].
    intros a Ha. clear - Ha AJ0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma mpd_nr : forall mq LBq d0, mpd_at asegs mq LBq d0 -> 0 <= md_n d0 <= MPI_MAX_LIMBS.
  Proof. intros mq LBq d0 [(_ & _ & _ & _ & NR & _) _]. exact NR. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L67741340990.10400000OS2LF2ra2sp3LFB2FB3sp14gapn2dy1H". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma cp_cap : forall dy, 0 <= md_n dy <= MPI_MAX_LIMBS -> copy_PHI dy <= dvcCP.
  Proof. intros dy H. unfold copy_PHI, dvcCP, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L45148039480.10500000OS2LF2ra2sp3LFB2FB3sp14gapn2dy1H". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma mul_cap : forall dt dy, 0 <= md_n dy <= MPI_MAX_LIMBS -> mul_int_PHI dt dy <= dvcMUL.
  Proof. intros dt dy H. unfold mul_int_PHI, copy_PHI, dvcMUL, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L49429103922.10600000VS2LF2ra2sp3LFB2FB3sp14gapn2dx2dt2H12H2". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma as_cap : forall dx dt, 0 <= md_n dx <= MPI_MAX_LIMBS -> 0 <= md_n dt <= MPI_MAX_LIMBS -> add_sub_PHI dx dx dt <= dvcAS.
  Proof. intros dx dt H1 H2. unfold add_sub_PHI, A_mpi_add_abs_W.add_abs_PHI, dvcAS, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L22712702117.108L40881342907.108L41997743205.108L53427879150.107L67536571068.10600000Y01>01g02I02iS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2Hc2Hn3BLRS2LF2ra2sp3LFB2FB3sp14gapn1c2dl3BLR1HS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2Hc2Hn3BLRS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2SNS2LF2ra2sp3LFB2FB3sp14gapn2dl2Hn". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma shl_cap : forall c dl, 0 <= c <= 32 * MPI_MAX_LIMBS -> 0 <= md_n dl <= MPI_MAX_LIMBS -> shift_l_PHI dl c <= dvcSHL.
  Proof.
    intros c dl Hc Hn. unfold shift_l_PHI, dvcSHL.
    assert (SN : shift_l_n c dl <= 2 * MPI_MAX_LIMBS).
    { pose proof (core_bitlen_range (md_limbs dl) (md_n dl) ltac:(lia)) as BLR. unfold shift_l_n.
      destruct (Z.ltb_spec (md_n dl * 32) (core_bitlen (md_limbs dl) (md_n dl) + c)); [| lia].
      apply limbs_of_bits_le; lia. }
    unfold grow_PHI. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L26523304876.10200000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma caps_nonneg : 0 <= dvcMUL /\ 0 <= dvcSHL /\ 0 <= dvcAS /\ 0 <= dvcCP.
  Proof. unfold dvcMUL, dvcSHL, dvcAS, dvcCP, grow_PHI, MPI_MAX_LIMBS, AVOL_CALL. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L60849827364.2000006S1d2D0". (* [comment removed for export] *)
  Lemma frs_nonneg : 0 <= mul_int_FR (d + 1) /\ 0 <= shift_l_FR /\ 0 <= add_sub_FR (d + 1) /\ 0 <= copy_FR 0.
  Proof using D0. unfold mul_int_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, copy_FR, shift_l_FR, calls_FR, fr_charge. clear - D0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47959989799.600000DS1d2D02PF2FF3PF03FF0". (* [comment removed for export] *)
  Lemma pf_nonneg : 0 <= PF /\ 0 <= FF.
  Proof using D0 PF0 FF0. clear - D0 PF0 FF0. unfold AVOL_CALL in PF0. unfold fr_charge in FF0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L11463080128.1700000[S2dA2FB3sp12kx3dLX2dY2dZ2dT1i2ny4dLX'2LI2NN". (* [comment removed for export] *)
  #[using="Type"] Lemma linv_X : forall kx kx' dLX dY dZ dT i ny dLX', linvk kx dLX dY dZ dT i ny -> md_addr dLX' = md_addr dLX -> md_own dLX' = LHeap -> md_n dLX <= md_n dLX' ->
    Z.abs (mpd_val dLX') + kx' * dvBT < (2 * md_n dA + 2) * dvBT -> linvk kx' dLX' dY dZ dT i ny.
  Proof. intros kx kx' dLX dY dZ dT i ny dLX' LI EA OH NN XB'. clear - LI EA OH NN XB'. unfold linvk in *. rewrite EA. repeat split; try tauto. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10309448349.1500000ZS2dA2FB3sp12kx3dLX2dY2dZ2dT1i2ny3dT'2LI2NN". (* [comment removed for export] *)
  #[using="Type"] Lemma linv_T : forall kx dLX dY dZ dT i ny dT', linvk kx dLX dY dZ dT i ny -> md_addr dT' = md_addr dT -> md_own dT' = LHeap -> md_n dT <= md_n dT' -> linvk kx dLX dY dZ dT' i ny.
  Proof. intros kx dLX dY dZ dT i ny dT' LI EA OH NN. clear - LI EA OH NN. unfold linvk in *. rewrite EA. repeat split; try tauto. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma linv_Z : forall kx dLX dY dZ dT i ny zs, linvk kx dLX dY dZ dT i ny -> linvk kx dLX dY (set_limbsA dZ zs) dT i ny.
  Proof. intros kx dLX dY dZ dT i ny zs LI. unfold linvk, A_mpi_div_mpi_M_c24.set_limbsA in *. cbn [md_addr md_own md_n]. exact LI. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L14056246631.14L14935568727.14L14935569628.13L18692947600.14L26290884114.19L27543419725.14L29016213614.15L34574852874.12L34577087250.14L39170151170.14L41415856750.13L41418084349.12L41422330361.15L44015297541.1400000>00R00f01501^01n02N02b03603F03Q03X03e040S2vy3idx2ny2PPS2vy3idx2ny3Hny4HidxS2vy3idx2ny3Hny4HidxS2vy3idx2ny3HnyS2dA2vy1q3idx2ny1i3Hny4Hidx2Hi3HiA1E1M2S2S2vy3idx2ny1i2HiS2dA2vy3idx2ny1i3Hny4Hidx2Hi3HiAS2vy3idx2ny3Hny4HidxS2vy3idx2ny3Hny4HidxS2vy1q3idx2ny2HqS2vy3idx2nyS2vy2nyS2vy3idx2ny1iS2vy3idx2ny". (* [comment removed for export] *)
  #[using="Type"] Lemma t1_bound : forall vy q idx ny i, 0 <= q < 2^32 -> Z.abs vy < 2 ^ (32 * ny) -> 0 <= ny -> 0 <= idx -> ny + idx = i -> i <= md_n dA ->
    Z.abs (vy * q * 2 ^ (idx * 32)) < dvBT.
  Proof.
    intros vy q idx ny i Hq Hy Hny Hidx Hi HiA. clear - Hq Hy Hny Hidx Hi HiA. unfold A_mpi_div_mpi_M_c24.dvBT.
    pose proof (Z.pow_pos_nonneg 2 (idx * 32) ltac:(lia) ltac:(lia)) as PP. pose proof (Z.pow_pos_nonneg 2 (32 * ny) ltac:(lia) ltac:(lia)) as PY.
    rewrite !Z.abs_mul. rewrite (Z.abs_eq q) by lia. rewrite (Z.abs_eq (2 ^ (idx * 32))) by lia.
    assert (E : 2 ^ (32 * (i + 1)) = 2 ^ (32 * ny) * 4294967296 * 2 ^ (idx * 32)).
    { replace (32 * (i + 1)) with (32 * ny + 32 + idx * 32) by lia. rewrite !Z.pow_add_r by lia. reflexivity. }
    assert (M : 2 ^ (32 * (i + 1)) <= 2 ^ (32 * (md_n dA + 1))) by (apply Z.pow_le_mono_r; lia).
    pose proof (Z.abs_nonneg vy) as AN.
    assert (S1 : Z.abs vy * q < 2 ^ (32 * ny) * 4294967296) by nia.
    assert (S2 : Z.abs vy * q * 2 ^ (idx * 32) < 2 ^ (32 * ny) * 4294967296 * 2 ^ (idx * 32)) by (apply Z.mul_lt_mono_pos_r; assumption).
    lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L61639115041.0L66453583803.2000001009SS2vy3idx". (* [comment removed for export] *)
  #[using="Type"] Lemma y_bound : forall vy idx ny i, Z.abs vy < 2 ^ (32 * ny) -> 0 <= ny -> 0 <= idx -> ny + idx = i -> i <= md_n dA ->
    Z.abs (vy * 2 ^ (idx * 32)) < dvBT.
  Proof.
    intros vy idx ny i Hy Hny Hidx Hi HiA. replace (vy * 2 ^ (idx * 32)) with (vy * 1 * 2 ^ (idx * 32)) by (clear; lia).
    apply (t1_bound vy 1 idx ny i); try assumption. clear. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL4c_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linvk (2 * (i - ny) + 1) dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + (dvcCP + dvcSHL + dvcAS) + dvVr n <= PHIb -> f + (copy_FR 0 + shift_l_FR + add_sub_FR (d + 1)) + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 (4 * (i - ny))) (Z_to_bv 64 ((i - ny) * 32)) s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fd28) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01N0@C7096915042.397 D33876909647.396D63873442836.396K21870859916.398K33980871419.398K52049772347.398K66327680928.397L11327188655.1  L12469921329.0  L12861988900.9  L14447101554.5  L14820281134.10 L16000728743.6  L1685717371.0   L18351506484.5  L18357479357.11 L1855173106.9   L19133426325.6  L19556266785.0  L21868076544.5  L23524570067.14 L25095893474.13 L26845910153.2  L29832375856.1  L29936708385.0  L29956516996.0  L31527751786.6  L32284259785.0  L33324104207.7  L33982282359.5  L34860304136.6  L40066488116.5  L41302442785.0  L42816623016.8  L47314679148.11 L51158826717.16 L52051507127.5  L52428691159.8  L53618266946.2  L54060558805.11 L55990716303.386L5605601736.8   L58209102511.1  L59310648043.7  L59667784614.1  L6178369912.3   L61798049332.6  L63650381673.14 L66084005463.13 L66084350309.14 L66330468140.4  L67345532263.10 L7735389571.5   L8045422791.2   L8532400182.5   L8820192273.7   L8929159528.388 L8929620893.385 L9356559676.11  L9931879857.7   P14461423358.398P18341645496.398P40077402040.398P61800574648.398P66327680928.397P7750690063.398 Q10812129647.392Q11801279589.396Q19991027068.398Q26295627581.392Q28094096925.318Q28094326941.271Q28096359191.225Q33874924623.397Q33877164610.392Q33889765055.392Q45539900993.398Q48467890406.398Q49472925079.389Q49698585326.396Q50458135125.392Q51003780618.389Q51120983794.392Q51135677050.395Q51337909069.389Q52015217408.271Q52015510912.318Q52017248394.225Q63871233556.397Q63873185817.392Q63883819088.392Q63885703535.389Q63885753572.392Q8943555749.389 00000101G02W03X04Y05Z05[05_05`06906:06W06l06m06n07U08208H08I08J09:09h09n0:20:30:40:B0:C0:Y0:Z0;10;20;30;Q0<70<o0=00=F0=N0>10>c0?<0?@0?Z0?^0?h0?i0@V0A?0Ak0Al0BM0BN0BT0Be0C?0DZ0F50F`0G:0HV0J20KN0Lj0Lk0N?0O20OZ0O[0P@0Pl0QV0R:0S00Sc0TV0TW0TX0UK0VH0Vm0W]0XN0Y?0Z20ZY0[B0[c0\S0]@0]m0^Z0_G0_lFS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY13INA2NZ3idx2wv2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY13idx2wv2Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wv3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wv3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wv3PZF3IDXFS2FBFS1d3FRb2FF1n1f2HF3FN33FRGFS1d3FRb2FF1n1f2HF3FN23FN33FRGS2dA1i2ny3NY13NYI3INASFS4PHIb2PF1n2dY1v2HV3CN23CN33VRG3PFN3CPCS1d3FRb2FF1n1f2HF3FN33FRG3FFNS2dZ1i2ny4LENZ3idx3IDXSFS4PHIb2PF1n2dY1v1i2ny2HV3CN33VRG3PFN3CPC3dT33SHCS2dA2dY2dT1i2ny3NY13NYI3INA2NT3dT33NK33dT43NK4S1i2nyS2dZSSS1d3FRb1n1f2HFSS2dA3dLX2dY1i2ny2XB2TBFS2dY2dT3dT33NK33dT43NK4FSS3dLX1i2ny3NY13NYI3IXL3dX53NK5S2dA2dY2dT1i2ny3NY13NYI3INA2NT3dT33NK3S4PHIb2PF1n3dLX2dY1v1i2ny2HV3VRG3PFN3CPC3dT33SHC3dT43ASCFS1d3FRb2FF1n1f3FRG3HF5S2ny3NY1S4PHIb2PF1n2dY1v2HV3CN23CN33VRG3CPCS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3idxS1d3FRb2FF1n1f2HF3FRG3FFNS2FBS2dZ1i2ny4LENZ3idx3IDX3NTHS2dZS1i2ny3NYIFS4PHIb1n3dLX2dY1v1i2ny2HV3CPC3dT33SHC3dT43ASCS4PHIb2PF1n3dLX2dY1v1i2ny3VRG3dT33dT43HV5S4PHIb2PF1n2dY1v1i2ny2HV3CN33VRG3CPC3dT33SHCFS1d3FRb2FF1n1f2HF3FN23FN33FRG3FFNFS1i2nyS2dZ1i2ny3idx3IDXS2dA1i2ny4NA983NY13NYI3INAS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13NYI2Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13NYI2Z03PZ03PZC3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2dA1i2ny4NA983NY13NYI3INAS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idx2wvFS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dT1i2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dT2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wvS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxFFS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3idxS1R2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3ACV3NY13INA2NZ3idx3PZCS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2dT1i2ny3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13PZ03idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3PZ03IDXS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dT2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dT1i2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx2wv3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SHL ASP PF0 FF0"] Lemma dv_L4c : forall n, dvL5_stmt n -> dvL4c_stmt n.
  Proof.
    intros n K5. unfold dvL4c_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    dpose caps_nonneg as (CN1 & CN2 & CN3 & CN4). dpose frs_nonneg as (FN1 & FN2 & FN3 & FN4).
    pose proof (dvVr_ge n) as VRG. pose proof (dvFr_ge n) as FRG. pose proof pf_nonneg as (PFN & FFN).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof (cp_cap dY (mpd_nr _ _ _ MLY)) as CPC.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    eapply (call_copy_ll mq hq LBq _ _ v f 3%nat 1%nat dT dY 0x9fd34); try eassumption; try reflexivity; try (rewrite EAD; reflexivity); try (rewrite EAY; reflexivity).
    - discriminate.
    - rewrite EAD. clear. lia.
    - clear - HV CPC CN2 CN3 VRG PFN. lia.
    - clear - HF FN2 FN3 FRG FFN. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST3) as (CH3 & SH3 & MI3 & ST3 & HH3 & HT3 & HS3 & HFL3 & HCS3 & HVQ3 & HFQ3 & OK3 & CSOK3 & SB643 & SCS3 & CFB3 & LAWS3 & KINV3).
      clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      assert (EAD3 : md_addr dT3 = FB + 96) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[[(-> & VT3 & NK3)|(-> & NK3 & _)] _] _].
      2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
           - clear - HV CPC CN2 CN3 VRG PFN. lia.
           - clear - HF FN2 FN3 FRG FFN. lia. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      pose proof (shl_cap ((i - ny) * 32) dT3 ltac:(unfold MPI_MAX_LIMBS; clear - NY1 NYI INA NA98; lia) (mpd_nr _ _ _ ML3)) as SHC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. clear MU WM.
      unfold mpi_shift_l_stmtA_c in SHL.
      eapply (M_call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3) (i := 3%nat) (dl := dT3) (c := (i - ny) * 32) (retpc := 0x9fd44); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity).
      + rewrite EAD3. clear. lia.
      + cbv beta. clear - NY1 NYI INA NA98. lia.
      + clear - HV CPC SHC CN3 VRG PFN. lia.
      + cbv beta. clear - HF FN3 FRG FFN. lia.
      + clear. lia.
      + intros m4 h4 LB4 dT4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
        destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4 & MI4 & ST4 & HH4 & HT4 & HS4 & HFL4 & HCS4 & HVQ4 & HFQ4 & OK4 & CSOK4 & SB644 & SCS4 & CFB4 & LAWS4 & KINV4).
        clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH4.
        pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        assert (EAD4 : md_addr dT4 = FB + 96) by (rewrite EAL4; exact EAD3).
        ddestruct RR4 as [[(-> & VT4 & _ & _)| ->] (_ & _ & _ & NK4)].
        2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| exact EAX| exact EAY| exact EAZ| exact EAD4| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             - clear - HV CPC SHC CN3 VRG PFN. lia.
             - clear - HF FN3 FRG FFN. lia. }
        zstep.
        edestruct K_local_facts with (mq := m4) (i := 3%nat) (d := dT4) as (_ & NST4 & _); try eassumption; [reflexivity|].
        assert (OTH4 : md_own dT4 = LHeap) by (eapply M_out_heapA; [exact ML4| exact NST4| clear - NK4 NK3 NT INA NY1 NYI; lia]).
        edestruct K_local_facts with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (as_cap dLX dT4 (mpd_nr _ _ _ MLX4) (mpd_nr _ _ _ ML4)) as ASC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. clear MU WM.
        eapply (call_addsub_ll 1 ASP m4 h4 LB4 _ _ _ _ 0%nat 3%nat dLX dT4 0x9fd5c); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAD4; reflexivity).
        * discriminate.
        * rewrite EAX. clear. lia.
        * rewrite EAD4. clear. lia.
        * clear - HV CPC SHC ASC VRG PFN. lia.
        * clear - HF FRG FFN. lia.
        * clear. lia.
        * intros m5 h5 LB5 dX5 r y0'' y1'' y2'' ya1'' ya2'' ya3'' ya4'' ya5'' ya6'' ya7'' y3'' y4'' y5'' y6'' CST5 RR5 ML5 EAL5 UW5. cbn [set_nth] in CST5.
          assert (EAX5 : md_addr dX5 = FB + 32) by (rewrite EAL5; exact EAX).
          assert (HV5 : v + copy_PHI dY + shift_l_PHI dT3 ((i - ny) * 32) + add_sub_PHI dLX dLX dT4 + dvVr n <= PHIb) by (clear - HV CPC SHC ASC; lia).
          assert (HF5 : f + copy_FR 0 + shift_l_FR + add_sub_FR (d + 1) + dvFr n <= FRb) by (clear - HF; lia).
          destruct (kit_facts _ _ _ _ _ _ _ _ CST5) as (CH5 & SH5 & MI5 & ST5 & HH5 & HT5 & HS5 & HFL5 & HCS5 & HVQ5 & HFQ5 & OK5 & CSOK5 & SB645 & SCS5 & CFB5 & LAWS5 & KINV5).
          clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH5.
          pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
          ddestruct RR5 as [[(-> & VX5)| ->] (_ & _ & _ & NK5)].
          2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST5| exact EAX5| exact EAY| exact EAZ| exact EAD4| exact UW5| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
               - clear - HV5 VRG PFN. lia.
               - clear - HF5 FRG FFN. lia. }
          zstep. clear MU WM.
          edestruct K_local_facts with (mq := m5) (i := 0%nat) (d := dX5) as (_ & NSX5 & _); try eassumption; [reflexivity|].
          assert (OXH5 : md_own dX5 = LHeap) by (eapply M_out_heapA; [exact ML5| exact NSX5| clear - NK5 IXL NY1 NYI; lia]).
          assert (LI5 : linvk (2 * (i - ny)) dX5 dY dZ dT4 i ny).
          { eapply linv_X; [| exact EAL5| exact OXH5| exact NK5|]. eapply linv_T; [exact LI| rewrite EAD4, EAD; reflexivity| exact OTH4| clear - NK3 NK4; lia].
            pose proof (y_bound (mpd_val dY) (i - ny) ny i ltac:(rewrite (mpd_val_abs dY ltac:(pose proof MLY as [_ K]; exact K)); exact YB) ltac:(clear - NY1; lia) ltac:(clear - NYI; lia) ltac:(clear; lia) INA) as TB.
            rewrite VX5, VT4, VT3. clear - TB XB. lia. }
          edestruct K_local_facts with (mq := m5) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
          pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
          ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
          assert (OPZ : aobj asegs AL (hcs asegs R HIA h5) m5 (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HH5| exact INZ]).
          assert (CWZ : client_wrange L (LB5 ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h5) (md_p dZ) (4 * md_n dZ))
            by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
          set (idx := i - ny).
          assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
          destruct (nth_error (md_limbs dZ) (Z.to_nat idx)) as [wz|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ IDX; lia].
          pose proof (munch_refl [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
          zstep. zstep. replace (4 * (i - ny)) with (4 * idx) by (subst idx; clear; lia). zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
          pose proof (u32arr_read asegs m5 (md_p dZ) (md_limbs dZ) idx wz _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
          zstep. clear RD. zstep.
          pose proof (u32arr_store_ok asegs m5 (md_p dZ) (md_limbs dZ) idx _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
          zstep.
          lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
            pose proof (u32arr_write asegs m5 (md_p dZ) (md_limbs dZ) idx vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
          store_done.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
          match goal with H : HM asegs R HIA h5 LB5 LF1 m6 |- _ => rename H into HH6 end.
          match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
          match goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
          match goal with H : rw_cells asegs m6 (sp1 + 168) _ |- _ => rename H into CZ6 end.
          destruct (limb_store_kit m5 m6 h5 LB5 _ _ _ _ 2%nat dZ idx _ CST5 eq_refl OZH IDX MU WM HH6 MI6 ST6 ltac:(rewrite EAZ; exact CZ6) UAZ' ltac:(apply upd_length)) as (CST6 & _ & UWK).
          cbn [set_nth] in CST6.
          unfold dvL5_stmt in K5.
          eapply K5 with (i := i) (ny := ny) (k := k); [exact CST6| apply linv_Z; exact LI5| exact RN| exact HK| exact (UWK UW5)| exact BPOS| exact NA98| exact HV5| exact HF5].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL4_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 (4 * (i - ny))) s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fcbc) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0140@L10432810472.13 L11327188655.1  L12691537071.1  L12861988900.11 L14820281134.11 L16000728743.6  L17076861729.0  L1855173106.11  L23524570067.17 L25095893474.12 L26845910153.2  L28442596129.0  L29956516996.0  L3001766689.0   L31525654619.9  L31527751786.6  L31813027332.6  L32284259785.0  L33176980975.294L33324104207.8  L33325904157.6  L34860304136.5  L36062169889.0  L38691415991.0  L39284637285.0  L42816623016.8  L47314679148.10 L51158826717.20 L52428691159.11 L53618266946.2  L53987612891.11 L54060460629.13 L55990716303.246L5605601736.11  L58209102511.1  L59310648043.7  L6178369912.3   L63650266843.15 L63650381673.15 L66084005463.17 L66084350309.17 L8045422791.2   L8532400182.5   L8820192273.7   L8929159528.248 L8929620893.245 L9356559676.11  L9931879857.7   Q10812129647.252Q15234549277.298Q26295627581.252Q28094096925.345Q28094326941.298Q28095821548.251Q33889765055.252Q49472925079.249Q50458135125.252Q51003780618.249Q51120983794.252Q51337909069.249Q52015217408.298Q52015510912.345Q52016735601.251Q63883819088.252Q63885703535.249Q63885753572.252Q8943555749.249 Q9876800896.298 00000^00b00f01G01h02=02>02c03^04I04O04P04Q04R04m05;05P05Q06h07A07V07j07k07l07m08K08n0:50:W0:_0;D0;n0<Z0=?0=C0=]0=g0>X0?H0@@0A70A=0AN0Ah0C70DF0E10EK0F80Fe0GD0H10H^0IK0J80Je0KD0Kn0LY0MF0N00NZ0OD0Ok0PR0Q90QX0RBS4PHIb2PF1n2dY2dT1v2HV3CN23CN33CN43VRG3PFN3MUCS2FBS2FBS1d3FRb2FF1n1f2HF3FN23FN33FN43FRGS1d3FRb2FF1n1f2HF3FN23FN33FN43FRGS2dA1i2ny3NY13NYI3INASS1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS4PHIb2PF1n2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3PFN3MUC3dT33SHCS2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK33dT43NK4S1i2nySSSS1d3FRb1n1f3FN23FN33FN43HF5S1d3FRb1n1f2HFS2dA1i2ny3NY13NYI3INASS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZCS2dA3dLX2dY1i2ny2XB2wz2TBS2dA1i2ny3dX53Q173BTPS2dT3dT33NK33dT43NK4SSSS3dLX1i2ny3NY13NYI3IXL3dX53NK5S2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK3S4PHIb2PF1n3dLX2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3PFN3MUC3dT33SHC3dT43ASCS1d3FRb2FF1n1f3FN23FN33FN43FRG3HF5S2ny3NY1S1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS4PHIb2PF1n2dY2dT1v2HV3CN23CN33CN43VRG3MUCS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS2FBS2dZ1i2ny4LENZ3idx3IDX3NTHS1i2ny3NYIS4PHIb1n3dLX2dY2dT1v1i2ny3CN23CN33CN43dT33dT43HV5S4PHIb1n3dLX2dY2dT1v1i2ny2HV3MUC3dT33SHC3dT43ASCS4PHIb2PF1n3dLX2dY2dT1v1i2ny3CN23CN33CN43VRG3dT33dT43HV5S4PHIb2PF1n2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3MUC3dT33SHCS1i2nyS2dZ1i2ny3idx3IDXS2dA1i2ny4NA983NY13NYI3INAS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2dA1i2ny4NA983NY13NYI3INAS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PZ03idx3IDXS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H SHL MULI CMPI ASM PF0 FF0"] Lemma dv_L4 : forall n, dvL5_stmt n -> dvL4c_stmt n -> dvL4_stmt n.
  Proof.
    intros n K5 K4c. unfold dvL4_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    dpose caps_nonneg as (CN1 & CN2 & CN3 & CN4). dpose frs_nonneg as (FN1 & FN2 & FN3 & FN4).
    pose proof (dvVr_ge n) as VRG. pose proof (dvFr_ge n) as FRG. pose proof pf_nonneg as (PFN & FFN).
    unfold dvVrnd in HV. unfold dvFrnd in HF.
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof (mul_cap dT dY (mpd_nr _ _ _ MLY)) as MUC.
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    set (idx := i - ny).
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
    destruct (nth_error (md_limbs dZ) (Z.to_nat idx)) as [wz|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ IDX; lia].
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. replace (4 * (i - ny)) with (4 * idx) by (subst idx; clear; lia). zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wz _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    pose proof (cs_c24 _ _ _ _ _ _ _ _ _ _ CST) as C24q.
    eapply (call_mul_ll mq hq LBq _ _ v f 3%nat 1%nat dT dY (w32 wz) 0x9fce4); try eassumption; try reflexivity; try (rewrite EAD; reflexivity); try (rewrite EAY; reflexivity).
    - discriminate.
    - rewrite EAD. clear. lia.
    - rewrite EAY. clear. lia.
    - apply w32_range.
    - rewrite w32_sx32. apply sxz_mod32. apply w32_range.
    - rewrite w32_sx32. apply sxz_zero_iff. apply w32_range.
    - clear - HV MUC CN2 CN3 CN4 VRG PFN. lia.
    - clear - HF FN2 FN3 FN4 FRG FFN. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST3) as (CH3 & SH3 & MI3 & ST3 & HH3 & HT3 & HS3 & HFL3 & HCS3 & HVQ3 & HFQ3 & OK3 & CSOK3 & SB643 & SCS3 & CFB3 & LAWS3 & KINV3).
      clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      assert (EAD3 : md_addr dT3 = FB + 96) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[(-> & VT3 & _)| ->] (_ & _ & _ & NK3)].
      2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
           - clear - HV MUC CN2 CN3 CN4 VRG PFN. lia.
           - clear - HF FN2 FN3 FN4 FRG FFN. lia. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      pose proof (shl_cap ((i - ny) * 32) dT3 ltac:(unfold MPI_MAX_LIMBS; clear - NY1 NYI INA NA98; lia) (mpd_nr _ _ _ ML3)) as SHC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. clear MU WM.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
      unfold mpi_shift_l_stmtA_c in SHL.
      eapply (M_call_xop_l A_MPI_SHIFT_L MPI_SHIFT_L_STACK_A _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3) (i := 3%nat) (dl := dT3) (c := (i - ny) * 32) (retpc := 0x9fcfc); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity).
      + rewrite EAD3. clear. lia.
      + cbv beta. clear - NY1 NYI INA NA98. lia.
      + clear - HV MUC SHC CN2 CN3 CN4 VRG PFN. lia.
      + cbv beta. clear - HF FN2 FN3 FN4 FRG FFN. lia.
      + clear. lia.
      + intros m4 h4 LB4 dT4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
        destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4 & MI4 & ST4 & HH4 & HT4 & HS4 & HFL4 & HCS4 & HVQ4 & HFQ4 & OK4 & CSOK4 & SB644 & SCS4 & CFB4 & LAWS4 & KINV4).
        clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH4.
        pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        assert (EAD4 : md_addr dT4 = FB + 96) by (rewrite EAL4; exact EAD3).
        ddestruct RR4 as [[(-> & VT4 & _ & _)| ->] (_ & _ & _ & NK4)].
        2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| exact EAX| exact EAY| exact EAZ| exact EAD4| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             - clear - HV MUC SHC CN2 CN3 CN4 VRG PFN. lia.
             - clear - HF FN2 FN3 FN4 FRG FFN. lia. }
        zstep.
        edestruct K_local_facts with (mq := m4) (i := 3%nat) (d := dT4) as (_ & NST4 & _); try eassumption; [reflexivity|].
        assert (OTH4 : md_own dT4 = LHeap) by (eapply M_out_heapA; [exact ML4| exact NST4| clear - NK4 NK3 NT INA NY1 NYI; lia]).
        edestruct K_local_facts with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (as_cap dLX dT4 (mpd_nr _ _ _ MLX4) (mpd_nr _ _ _ ML4)) as ASC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. clear MU WM.
        eapply (call_addsub_ll (-1) ASM m4 h4 LB4 _ _ _ _ 0%nat 3%nat dLX dT4 0x9fd14); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAD4; reflexivity).
        * discriminate.
        * rewrite EAX. clear. lia.
        * rewrite EAD4. clear. lia.
        * clear - HV MUC SHC ASC CN2 CN3 CN4 VRG PFN. lia.
        * clear - HF FN2 FN3 FN4 FRG FFN. lia.
        * clear. lia.
        * intros m5 h5 LB5 dX5 r y0'' y1'' y2'' ya1'' ya2'' ya3'' ya4'' ya5'' ya6'' ya7'' y3'' y4'' y5'' y6'' CST5 RR5 ML5 EAL5 UW5. cbn [set_nth] in CST5.
          assert (EAX5 : md_addr dX5 = FB + 32) by (rewrite EAL5; exact EAX).
          assert (HV5 : v + mul_int_PHI dT dY + shift_l_PHI dT3 ((i - ny) * 32) + add_sub_PHI dLX dLX dT4 + (dvcCP + dvcSHL + dvcAS) + dvVr n <= PHIb) by (clear - HV MUC SHC ASC; lia).
          assert (HF5 : f + mul_int_FR (d + 1) + shift_l_FR + add_sub_FR (d + 1) + (copy_FR 0 + shift_l_FR + add_sub_FR (d + 1)) + dvFr n <= FRb) by (clear - HF; lia).
          destruct (kit_facts _ _ _ _ _ _ _ _ CST5) as (CH5 & SH5 & MI5 & ST5 & HH5 & HT5 & HS5 & HFL5 & HCS5 & HVQ5 & HFQ5 & OK5 & CSOK5 & SB645 & SCS5 & CFB5 & LAWS5 & KINV5).
          clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH5.
          pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
          ddestruct RR5 as [[(-> & VX5)| ->] (_ & _ & _ & NK5)].
          2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST5| exact EAX5| exact EAY| exact EAZ| exact EAD4| exact UW5| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
               - clear - HV5 CN2 CN3 CN4 VRG PFN. lia.
               - clear - HF5 FN2 FN3 FN4 FRG FFN. lia. }
          zstep.
          edestruct K_local_facts with (mq := m5) (i := 0%nat) (d := dX5) as (_ & NSX5 & _); try eassumption; [reflexivity|].
          assert (OXH5 : md_own dX5 = LHeap) by (eapply M_out_heapA; [exact ML5| exact NSX5| clear - NK5 IXL NY1 NYI; lia]).
          assert (LI5 : linvk (2 * (i - ny) + 1) dX5 dY dZ dT4 i ny).
          { eapply linv_X; [| exact EAL5| exact OXH5| exact NK5|]. eapply linv_T; [exact LI| rewrite EAD4, EAD; reflexivity| exact OTH4| clear - NK3 NK4; lia].
            pose proof (t1_bound (mpd_val dY) (w32 wz) (i - ny) ny i (w32_range wz) ltac:(rewrite (mpd_val_abs dY ltac:(pose proof MLY as [_ K]; exact K)); exact YB) ltac:(clear - NY1; lia) ltac:(clear - NYI; lia) ltac:(clear; lia) INA) as TB.
            rewrite VX5, VT4, VT3. clear - TB XB. lia. }
          assert (LI5' : linvk (2 * (i - ny)) dX5 dY dZ dT4 i ny).
          { pose proof (dvBT_pos ltac:(clear - NY1 NYI INA; lia)) as BTP. ddestruct LI5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
            unfold linvk. repeat (split; [assumption|]). clear - Q17 BTP. lia. }
          (* [comment removed for export] *)
          zstep. zstep. zstep. clear MU WM.
          eapply (call_cmpint_l m5 h5 LB5 _ _ _ _ 0%nat dX5 0 0x9fd24); try eassumption; try reflexivity; try (rewrite EAX5; reflexivity); [clear; lia| clear; lia|].
          intros m6 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 CST6 UWK. pose proof (UWK UW5) as UW6.
          pose proof (munch_refl ([] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
          destruct (kit_facts _ _ _ _ _ _ _ _ CST6) as (CH6 & SH6 & MI6 & ST6 & HH6 & _).
          destruct (Z.sgn_spec (mpd_val dX5 - 0)) as [(GT & ->)|[(EQ & ->)|(LT & ->)]].
          3: { (* [comment removed for export] *)
            zstep. unfold dvL4c_stmt in K4c.
            eapply K4c with (i := i) (ny := ny) (k := k); [exact CST6| exact LI5| exact RN| exact HK| exact UW6| exact BPOS| exact NA98| exact HV5| exact HF5]. }
          -- zstep. unfold dvL5_stmt in K5.
             eapply K5 with (i := i) (ny := ny) (k := k); [exact CST6| exact LI5'| exact RN| exact HK| exact UW6| exact BPOS| exact NA98| |].
             ++ clear - HV5 CN2 CN3 CN4. lia.
             ++ clear - HF5 FN2 FN3 FN4. lia.
          -- zstep. unfold dvL5_stmt in K5.
             eapply K5 with (i := i) (ny := ny) (k := k); [exact CST6| exact LI5'| exact RN| exact HK| exact UW6| exact BPOS| exact NA98| |].
             ++ clear - HV5 CN2 CN3 CN4. lia.
             ++ clear - HF5 FN2 FN3 FN4. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDW_stmt (n Q : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z) wz
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wz -> (w32 wz - 1) mod 2^32 <= Z.of_nat Q ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 (4 * (i - ny))) s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fb5c) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L3793790120.117 L64507207096.11700000n01kS2LF2ra2sp3LFB1d3FRb2FB3sp14gapn2FF1n1f2HF3FN13FN23FN33FN43FRGS2LF2ra2sp3LFB4PHIb2FB3sp14gapn2PF1n1v2HV3CN13CN23CN33CN43VRG". (* [comment removed for export] *)
  #[using="LF ra sp LFB D0 FB sp1 gapn"] Lemma budget_err : forall n v f, v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb -> v + PF <= PHIb /\ f + FF <= FRb.
  Proof.
    intros n v f HV HF. dpose caps_nonneg as (CN1 & CN2 & CN3 & CN4). dpose frs_nonneg as (FN1 & FN2 & FN3 & FN4).
    pose proof (dvVr_ge n) as VRG. pose proof (dvFr_ge n) as FRG. unfold dvVrnd in HV. unfold dvFrnd in HF. split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDW2_stmt (n Q : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z) wq
           xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wq -> w32 wq <= Z.of_nat Q ->
    (forall j w, 1 <= j -> nth_error (md_limbs dT) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0) ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 (4 * (i - ny))) s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fb8c) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0130@C7096915042.247 D33876909647.246D63873442836.246K21870859916.248K33980871419.248K52049772347.248K66327680928.247L11327188655.1  L12469921329.0  L14447101554.5  L16000728743.6  L1685717371.0   L18351506484.5  L19133426325.6  L21868076544.5  L29162521377.0  L29832375856.1  L29956516996.0  L32321742194.6  L32477325796.2  L33982282359.5  L36571201320.0  L38691415991.0  L40066488116.5  L41811005730.8  L45099190568.0  L52051507127.5  L53550479595.0  L55990716303.236L59667784614.1  L61798049332.6  L66330468140.4  L7665232397.1   L7735389571.5   L8532400182.5   L8929159528.238 L8929620893.235 L9356559676.11  P14461423358.248P18341645496.248P40077402040.248P61800574648.248P66327680928.247P7750690063.248 Q10812129647.242Q11801279589.246Q19991027068.248Q26295627581.242Q28096359191.246Q33874924623.247Q33877164610.242Q33889765055.242Q48467890406.248Q49472925079.239Q49698585326.246Q50458135125.242Q51003780618.239Q51120983794.242Q51135677050.245Q51337909069.239Q52017248394.246Q63871233556.247Q63873185817.242Q63883819088.242Q63885703535.239Q63885753572.242Q8943555749.239 00000101F02U03U04G05905:05>05?05@05U05V05W05m05n05o06306406J06P06Q06R06S06T06o07007107207c07g07h07i07m07n08?09S0:g0;R0<c0>>0?Y0A40A50BH0C:0Ca0Cb0DF0E80Em0F_0GQ0GR0HD0I60IZ0JI0K90Ki0L[0MJ0N90Ne0OQ0P=0Pi0QMFS2LF2ra2sp3LFB2dA2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idx3SPR2F04SP1R2wv3NY13INA2NZ2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idx3SPR2F04SP1R2wv3NY12Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2FB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3PZF3IDXS2LF3LFB2FB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3PZF3IDXFS2FBFFS2dA1i2ny3NY13NYI3INASFS2dZ1i2ny3idx4LENZ3IDXFSS2dZSS2dZ1i2ny3idx4LENZ3IDXS1j2J1FSSFS2dA2dT1i2ny3NY13NYI3INA2NTSFFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idxS2dZFFS2dTFS2dZ1i2ny3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wz3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wz3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wvFS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idxS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3NY13INA2NZS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZFS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idxS1R2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3ACV3PZC3IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idxS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13PZ03IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13PZ03IDXS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF LSETNG PF0 FF0"] Lemma dv_DW1 : forall n Q, dvDW2_stmt n Q -> dvDW_stmt n Q.
  Proof.
    intros n Q K2. unfold dvDW_stmt. intros until t6. intros CST LI RN NTH QB HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    destruct (budget_err _ _ _ HV HF) as [HVE HFE].
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (CWZ : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dZ) (4 * md_n dZ))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
    set (idx := i - ny) in *.
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
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
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (sp1 + 168) _ |- _ => rename H into CZ2 end.
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 2%nat dZ idx _ CST eq_refl OZH IDX MU WM HH2 MI2 ST2 ltac:(rewrite EAZ; exact CZ2) UAZ' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2. pose proof (UWK UW) as UW2.
    assert (W32V : w32 wv = (w32 wz - 1) mod 2^32).
    { subst wv. unfold w32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
      rewrite <- (Znumtheory.Zmod_div_mod (2^32) (2^64)) by (try (clear; lia); exists (2^32); reflexivity).
      rewrite bv_unsigned_sx32. rewrite sxz_add_mod32 by (apply Z.mod_pos_bound; clear; lia). first [reflexivity | f_equal; clear; lia]. }
    clear MU WM.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    eapply (call_lset_ng_l m2 hq LBq _ _ v f 3%nat dT 0 0x9fb8c); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
    - rewrite EAD. clear. lia.
    - clear - NT INA NY1 NYI. lia.
    - clear. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      assert (EAD3 : md_addr dT3 = FB + 96) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[(-> & NT3 & OTH3 & [wl0 LT3] & _ & _)|(-> & ->)] _].
      + unfold dvDW2_stmt in K2.
        eapply K2 with (i := i) (ny := ny) (k := k) (wq := wv); [exact CST3| | exact RN| | | | exact HK| exact UW3| exact BPOS| exact NA98| exact HV| exact HF].
        * apply linv_Z. eapply linv_T; [exact LI| exact EAL3| exact OTH3| rewrite NT3; clear; lia].
        * unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_limbs]. apply nth_error_upd_same. clear - IDX LENZ. lia.
        * rewrite W32V. exact QB.
        * intros j w J1 NJ. rewrite LT3 in NJ. replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) in NJ by (clear - J1; lia). cbn [nth_error] in NJ.
          apply nth_error_In in NJ. apply repeat_spec in NJ. subst w. reflexivity.
      + pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3.
        pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep.
        eapply M_dv_ERR with (r := -16); [exact CST3| exact EAX| exact EAY| | exact EAD| exact UW3| clear; lia| exact HVE| exact HFE].
        unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_addr]. exact EAZ.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDWg (n Q : nat) (U pc : Z) (RA : mpd -> mpd -> mpd -> word -> word -> word -> Prop) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z) wq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wq -> w32 wq <= Z.of_nat Q ->
    (forall j w, U <= j -> nth_error (md_limbs dT) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0) ->
    RA dY dZ dT a0 a1 a2 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 (4 * (i - ny))) s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mq (seg_rom asegs)).
  Definition dvDW3_stmt (n Q : nat) : Prop := dvDWg n Q 1 0x9fbc4 (fun _ _ _ _ _ _ => True).
  Definition dvDW4_stmt (n Q : nat) : Prop := dvDWg n Q 1 0x9fbe4 (fun dY _ dT a0 _ a2 => a0 = Z_to_bv 64 (md_p dT) /\ a2 = Z_to_bv 64 (md_p dY)).
  Definition dvDW5_stmt (n Q : nat) : Prop := dvDWg n Q 2 0x9fc1c (fun _ dZ _ _ _ a2 => a2 = Z_to_bv 64 (md_p dZ)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11327188655.1  L12515393408.3  L13845124416.5  L16000728743.6  L25176780149.8  L2606547745.0   L26258305825.0  L29956516996.0  L39188636933.0  L47314679148.10 L53379847057.3  L5374952848.5   L59308960241.4  L59310614993.7  L8532400182.5   L8929159528.238 L8929620893.235 L9356559676.11  Q10812129647.242Q26295627581.242Q28095821548.241Q33889765055.242Q50458135125.242Q51120983794.242Q51337909069.239Q52016735601.241Q63883819088.242Q63885703535.239Q63885753572.242Q8943555749.239 00000400?00R00g01B01C01D01E01F01i02302E02S02l03=04N05_06J07907Z08I09809Y0:F0;50;a0<J0=30=\0>=S2FBS2wq3QNZ2WRS4PHIb2PF1v3HVE3PFNS2dA1i2ny3NY13NYI3INAS2dA2dT1i2ny3NY13NYI3INA2NTSSSSS2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK3S2Q'2wq2QBS3FRb2FF1f3HFE3FFNS2wq2QB3QNZ2WRS2u02u12u23dT33VZ32GT3LR2S2dZ1i2ny3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny3idxS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H MULNG CMPR slo SLO1 SLO2 SSH0 PF0 FF0"] Lemma dv_DW5 : forall n Q, dvL4_stmt n -> (forall Q', Q = S Q' -> dvDW_stmt n Q') -> dvDW5_stmt n Q.
  Proof.
    intros n Q K4 KDW. unfold dvDW5_stmt, dvDWg. intros until t6. intros CST LI RN NTH QB ZT RA HK UW BPOS NA98 HV HF. subst a2. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    destruct (budget_err _ _ _ HV HF) as [HVE HFE].
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ).
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    set (idx := i - ny) in *.
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wq _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep. zstep. clear MU WM.
    pose proof (cs_c24 _ _ _ _ _ _ _ _ _ _ CST) as C24q.
    eapply (call_mul_ng_l mq hq LBq _ _ v f 3%nat dT (w32 wq) 2 0x9fc44); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
    - rewrite EAD. clear. lia.
    - clear - NT INA NY1 NYI. lia.
    - apply w32_range.
    - rewrite w32_sx32. apply sxz_mod32. apply w32_range.
    - rewrite w32_sx32. apply sxz_zero_iff. apply w32_range.
    - pose proof pf_nonneg as [PFN _]. clear - HVE PFN. lia.
    - pose proof pf_nonneg as [_ FFN]. clear - HFE FFN. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST3) as (CH3 & SH3 & MI3 & ST3 & HH3 & HT3 & HS3 & HFL3 & HCS3 & HVQ3 & HFQ3 & OK3 & CSOK3 & SB643 & SCS3 & CFB3 & LAWS3 & KINV3).
      clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      assert (EAD3 : md_addr dT3 = FB + 96) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[(-> & VZ3 & _)| ->] (_ & _ & _ & NK3)].
      2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep. eapply M_dv_ERR with (r := -16); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| clear; lia| exact HVE| exact HFE]. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      assert (LI3 : linv dLX dY dZ dT3 i ny) by (eapply linv_T; [exact LI| exact EAL3| exact OTH3| exact NK3]).
      (* [comment removed for export] *)
      zstep. zstep. zstep. clear MU WM.
      eapply (call_cmpraw m3 h3 LB3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3%nat dT3 0x9fc54); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity); [clear; lia|].
      intros m4 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 CST4 UWK. pose proof (UWK UW3) as UW4.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4' & MI4 & ST4 & HH4 & _).
      set (cmpv := md_sg dT3 * lval (md_limbs dT3) (md_n dT3) - 1 * lval [u0; u1; u2] 3) in *.
      destruct (Z.sgn_spec cmpv) as [(GT & ->)|[(EQ & ->)|(LT & ->)]].
      + (* [comment removed for export] *)
        zstep.
        assert (QNZ : w32 wq <> 0).
        { intros Q0. specialize (VZ3 Q0). pose proof ML3 as [(_ & _ & _ & HL3 & _) SG3]. pose proof (mpd_abs_lval dT3 HL3) as AL3.
          unfold mpd_val in VZ3. fold (mpd_abs dT3) in VZ3. pose proof (lval_range [u0; u1; u2] 3 ltac:(clear; lia)) as LR2.
          subst cmpv. rewrite <- AL3 in GT. clear - GT VZ3 LR2. lia. }
        destruct Q as [|Q']; [exfalso; pose proof (w32_range wq) as WR; clear - QB QNZ WR; lia|].
        eapply (KDW Q' eq_refl) with (i := i) (ny := ny) (k := k) (wz := wq); [exact CST4| exact LI3| exact RN| exact NTH| | exact HK| exact UW4| exact BPOS| exact NA98| exact HV| exact HF].
        pose proof (w32_range wq) as WR. rewrite Z.mod_small by (clear - WR QNZ; lia). rewrite Nat2Z.inj_succ in QB. clear - QB. lia.
      + zstep. zstep. unfold dvL4_stmt in K4.
        eapply K4 with (i := i) (ny := ny) (k := k); [exact CST4| exact LI3| exact RN| exact HK| exact UW4| exact BPOS| exact NA98| exact HV| exact HF].
      + zstep. zstep. unfold dvL4_stmt in K4.
        eapply K4 with (i := i) (ny := ny) (k := k); [exact CST4| exact LI3| exact RN| exact HK| exact UW4| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma linv_Tl : forall kx dLX dY dZ dT i ny ts, linvk kx dLX dY dZ dT i ny -> linvk kx dLX dY dZ (set_limbsA dT ts) i ny.
  Proof. intros kx dLX dY dZ dT i ny ts LI. unfold linvk, A_mpi_div_mpi_M_c24.set_limbsA in *. cbn [md_addr md_own md_n]. exact LI. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@C26840107418.267D25312390013.266D40377636077.266K12141789871.266K14640611937.268K30788161014.268K32709643937.268K56623506564.267K7530080353.269 L10363041570.2  L11146238902.2  L12138107471.2  L12469921329.0  L14343865800.1  L14637060737.2  L1685717371.0   L17060135621.2  L21922122424.3  L27038155402.2  L30800338198.2  L32506788978.2  L32705896001.2  L32865176246.2  L34785933159.2  L35846324226.8  L35907695816.257L35907808182.254L41766935438.2  L55990716303.256L56636732516.1  L58133293238.3  L59321132280.6  L61997691801.2  L62830729610.1  L7517911169.2   L8929159528.254 L8929620893.251 L9356559676.11  P11150019414.268P11150019414.269P12141789871.269P17047015973.268P32852089430.268P41763277678.268P56623506564.267P58146322518.268Q11801279589.266Q24814724221.264Q25306249017.264Q25307919245.261Q25310437757.268Q25312130928.263Q25622449825.266Q25632916009.264Q26295627581.261Q26295627581.264Q37991553687.258Q38669729164.258Q40375623405.268Q40377895136.263Q42119247257.268Q49475530792.262Q50458135125.261Q50458135125.264Q51005338549.262Q54608293134.261Q55126681098.263Q58477445543.268Q59541579092.261Q64032823942.267Q66561630474.258Q66791183892.261Q66791183892.263Q66793723691.258Q8943472942.261 Q8943555749.258 Q9992779027.261 00000100_01j02W03B03m04X04Y05D05J05K05L05M05Q05R05S05T05`05f05g05n05o06006706R07d09609709b09c09d0:=0:E0:I0:J0;f0=B0=m0?70@A0@B0AD0BN0CX0CY0Dc0ED0Ee0FC0Fa0GB0G`0HB0Hd0IB0I`0JL0K30KW0L80L90Le0MC0Ma0NJ0O10OX0OY0P:0Pe0QN0R00RR0S40SR0T00TVFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny2wvS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3SPR2F04SP1R2wv2Y03PY02T03PT02T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2wv4LENY3LAP2T3S2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny2wv3PTF2T3FS2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny2wv3PTF2T3S1j2J2FFFS2dTFSFS2dT4LENT2T3S1j2J2FS2dT2T3FFS2dY2nyS2dA2dT1i2ny3NY13NYI3INA2NTS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2Y03PY02T03PT03PTC2T3S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2Y03PY02T03PT03PTC2T3FS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2nyFFS2dY2ny3NY13NYL4LENY4NTHYS2ny3NY1S2dTFS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NY13NYL2Y04NY1'3PY03PYC2T03PT0S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NY13NYL2Y04NY1'3PY03PYC2T03PT0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB4gapn1n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO2wv3PTC2T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2wvS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2wvS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL4NY1'S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2wv2T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2T3FS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL4NY1'S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL4NY1'FS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny2T3S1R2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3ACV3PTC2T3S2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NY1S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NY1S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NY1S2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NY13PY0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_DW4 : forall n Q, dvDW5_stmt n Q -> dvDW4_stmt n Q.
  Proof.
    intros n Q K5. unfold dvDW4_stmt, dvDWg. intros until t6. intros CST LI RN NTH QB ZT RA HK UW BPOS NA98 HV HF. destruct RA as [-> ->]. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & NSY & _ & _ & _ & _ & HFY & _ & Y8 & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & Y0 & LENY & NRY & OWY) SGY]. rewrite OYH in OWY. ddestruct OWY as (NY1' & INY & PY16 & UAY).
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    edestruct K_local_facts with (mq := mq) (i := 3%nat) (d := dT) as (MLT & NSTl & _ & _ & _ & _ & HFT & _ & T8 & _ & OTs); try eassumption; [reflexivity|].
    pose proof MLT as [(CT & _ & T0 & LENT & NRT & OWT) SGT]. rewrite OTH in OWT. ddestruct OWT as (NT1 & INT & PT16 & UAT). rewrite EAD in CT. unfold mpi_cells in CT.
    ddestruct (HFT OTH) as (PT0 & PTC & _ & _ & PTF & _).
    assert (OPT : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dT) (4 * md_n dT)) by (eapply hm_aobj_block; [exact HHq| exact INT]).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dT) (4 * md_n dT))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INT| clear; lia| clear; lia]).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & _); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _) _]. rewrite EAZ in CZ. unfold mpi_cells in CZ.
    destruct (M_locals_apart _ _ _ _ _ _ _ _ 3%nat 1%nat dT dY CST eq_refl eq_refl ltac:(discriminate)) as [_ LAP]. specialize (LAP OTH OYH).
    assert (T3 : 3 <= md_n dT) by (clear - NT INA NY1 NYI; lia).
    destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 1))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY NYL NY1; lia].
    pose proof (munch_refl [(md_p dT + 4, md_p dT + 4 + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. replace (md_p dY + (ny - 1) * 4) with (md_p dY + 4 * (ny - 1)) by (clear; lia). zstep. zstep. shadow_chk OPY (md_p dY + 4 * (ny - 1)) 4.
    (* [comment removed for export] *)
    pose proof (u32arr_read asegs mq (md_p dY) (md_limbs dY) (ny - 1) wy _ UAY NTHY ltac:(clear - NY1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. zstep. zstep. shadow_chk OPT (md_p dT + 4) 4. clear RD.
    (* [comment removed for export] *)
    zstep.
    pose proof (u32arr_store_ok asegs mq (md_p dT) (md_limbs dT) 1 _ UAT ltac:(clear - T3 LENT; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dT) (md_limbs dT) 1 vv UAT ltac:(clear - T3 LENT; lia)) as UAT'; change (md_p dT + 4 * 1) with (md_p dT + 4) in UAT'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (FB + 96) _ |- _ => rename H into CT2 end.
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 3%nat dT 1 _ CST eq_refl OTH ltac:(clear - T3; lia) MU WM HH2 MI2 ST2 ltac:(rewrite EAD; exact CT2) UAT' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2.
    unfold dvDW5_stmt, dvDWg in K5.
    eapply K5 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST2| apply linv_Tl; exact LI| exact RN| exact NTH| exact QB| | reflexivity| exact HK| exact (UWK UW)| exact BPOS| exact NA98| exact HV| exact HF].
    intros j w J2 NJ. unfold A_mpi_div_mpi_M_c24.set_limbsA in NJ. cbn [md_limbs] in NJ.
    rewrite nth_error_upd_other in NJ by (clear - J2; lia). apply (ZT j w ltac:(clear - J2; lia) NJ).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0100@C601670438.247  D18694488097.246D55473375817.246K1060308597.248 K13933473562.248K19239682677.248K40867192245.248K62665059445.248K63563842176.247L10642704280.3  L1073403541.2   L12469921329.0  L13937033210.2  L14343865800.1  L1685717371.0   L19227710101.2  L24084976897.2  L25858047826.2  L28862916362.2  L30981510610.2  L32407759370.2  L35846324226.8  L40091177158.1  L40853966165.2  L41663468825.238L4586513446.243 L47015188111.2  L61366595865.236L62678187157.2  L62830729610.1  L63560127072.1  L67574619286.238L67574810211.235L7131264010.3   L9356559676.11  P24081221089.248P28866574314.248P30977918258.248P32404077290.248P63563842176.247P7143400682.248 Q11801279589.246Q14331660581.242Q14342228332.242Q14344177747.239Q16858858661.248Q17064285623.239Q18696473121.247Q26295627581.242Q28096359191.239Q34674277469.241Q40258548363.248Q42816481578.246Q46283567848.239Q50458135125.242Q52017248394.239Q523213388.241  Q55471390793.247Q58748148646.239Q60412549208.242Q65860365407.242Q67246447712.242Q7411613069.245 Q8943555749.239 00000100\01]02E02m03U04=04e04f05205305405505905:05;05<05C05D05E05F05a05e05f06N07607<07d07e07i07j0920::0:;0:f0;e0<l0>30?:0?;0@B0@`0A;0AV0B10B20BP0Bn0CI0D20DP0DQ0E90EW0F20FX0G60GW0H50HS0I10IP0Io0JJFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny2wvS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3SPR2F04SP1R2wv2T03PT02T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PTF2T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PTF2T3FS2dT4LENT2T3FFFS2dTSFFS2dT2T3FFFS2dA2dT1i2ny3NY13NYI3INA2NTS2dTFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyS1j2J1S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyFS2dTFS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T3S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T3FS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB4gapn1n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny2wvS2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2nyFS2LF3LFB2FB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2ny2wvS2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dT2nyS2LF3LFB2FB4gapn1n1Q3dLX2dT2nyFS1R2LF3LFB4gapn1n1Q3dLX2dT2ny3ACV3PTC2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dT2nyS2LF3LFB2FB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2ny2wv2T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dT2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_DW3 : forall n Q, dvDW4_stmt n Q -> dvDW3_stmt n Q.
  Proof.
    intros n Q K4. unfold dvDW3_stmt, dvDWg. intros until t6. intros CST LI RN NTH QB ZT _ HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _) _]. rewrite EAY in CY. unfold mpi_cells in CY.
    edestruct K_local_facts with (mq := mq) (i := 3%nat) (d := dT) as (MLT & NSTl & _ & _ & _ & _ & HFT & _ & T8 & _ & OTs); try eassumption; [reflexivity|].
    pose proof MLT as [(CT & _ & T0 & LENT & NRT & OWT) SGT]. rewrite OTH in OWT. ddestruct OWT as (NT1 & INT & PT16 & UAT). rewrite EAD in CT. unfold mpi_cells in CT.
    ddestruct (HFT OTH) as (PT0 & PTC & _ & _ & PTF & _).
    assert (OPT : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dT) (4 * md_n dT)) by (eapply hm_aobj_block; [exact HHq| exact INT]).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dT) (4 * md_n dT))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INT| clear; lia| clear; lia]).
    assert (T3 : 3 <= md_n dT) by (clear - NT INA NY1 NYI; lia).
    pose proof (munch_refl [(md_p dT, md_p dT + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk OPT (md_p dT) 4.
    zstep.
    pose proof (u32arr_store_ok asegs mq (md_p dT) (md_limbs dT) 0 _ UAT ltac:(clear - T3 LENT; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dT) (md_limbs dT) 0 vv UAT ltac:(clear - T3 LENT; lia)) as UAT'; change (md_p dT + 4 * 0) with (md_p dT + 0) in UAT'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (FB + 96) _ |- _ => rename H into CT2 end.
    assert (MU' : munch [(md_p dT + 4 * 0, md_p dT + 4 * 0 + 4)] mq m2) by (replace (md_p dT + 4 * 0) with (md_p dT) by (clear; lia); exact MU).
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 3%nat dT 0 _ CST eq_refl OTH ltac:(clear - T3; lia) MU' WM HH2 MI2 ST2 ltac:(rewrite EAD; exact CT2) UAT' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2.
    unfold dvDW4_stmt, dvDWg in K4.
    eapply K4 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST2| apply linv_Tl; exact LI| exact RN| exact NTH| exact QB| | split; reflexivity| exact HK| exact (UWK UW)| exact BPOS| exact NA98| exact HV| exact HF].
    intros j w J1 NJ. unfold A_mpi_div_mpi_M_c24.set_limbsA in NJ. cbn [md_limbs] in NJ.
    rewrite nth_error_upd_other in NJ by (clear - J1; lia). apply (ZT j w J1 NJ).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L39172636981.0  L41663468825.234L42967148590.231L48225964310.2  L48279326478.3  L59321132280.7  L68135535093.233L8929159528.236 L8941826057.233 L9356559676.11  Q19402954634.234Q26295627581.240Q34669158962.237Q38657031704.237Q50458135125.240Q534873123.237  Q53878713367.234Q54608293134.240Q55128416958.240Q66791183892.240Q66793640608.240Q66805896383.237Q8956254001.237 Q9992779027.240 00000100Y01f01m02802Q03^05506L07707]08808V09:09U0:30:\0;@0;d0<F0<h0=J0=e0>KSS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2nyS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y03PY03PYCS2dY2nyS2ny3NY12KTS2dY2ny3NY13NYL4LENY4NTHYS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y03PY03PYCS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y04NY1'4PY163PY03PYCS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y04NY1'4PY163PY03PYCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2nyS2LF3LFB2FB4gapn1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n1Q3dLX2dY2nyS2LF3LFB2FB4gapn1n1Q3dLX2dY2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n1Q3dLX2dY2ny3NY12KTS2LF3LFB4gapn1n1Q3dLX2dY2ny3NY12KTS2LF3LFB4gapn1n1Q3dLX2dY2ny3NY12KTS2LF3LFB4gapn1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3NY13PY02KT". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M XW SP1 GAP FRSH CFB LOC CSP FN64"] Lemma dv_DW2 : forall n Q, dvDW3_stmt n Q -> dvDW2_stmt n Q.
  Proof.
    intros n Q K3. unfold dvDW2_stmt. intros until t6. intros CST LI RN NTH QB ZT HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & NSY & _ & _ & _ & _ & HFY & _ & Y8 & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & Y0 & LENY & NRY & OWY) SGY]. rewrite OYH in OWY. ddestruct OWY as (NY1' & INY & PY16 & UAY). rewrite EAY in CY. unfold mpi_cells in CY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    unfold dvDW3_stmt, dvDWg in K3.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep; if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - NY1 NYI INA NA98; lia).
    - (* [comment removed for export] *)
      zstep.
      eapply K3 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST| exact LI| exact RN| exact NTH| exact QB| exact ZT| exact I| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 2))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY NYL NY1 KT; lia].
      zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      replace (md_p dY + ny * 4 + -8) with (md_p dY + 4 * (ny - 2)) by (clear; lia).
      zstep. zstep. shadow_chk OPY (md_p dY + 4 * (ny - 2)) 4.
      pose proof (u32arr_read asegs mq (md_p dY) (md_limbs dY) (ny - 2) wy _ UAY NTHY ltac:(clear - NY1 KT; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD. zstep.
      eapply K3 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST| exact LI| exact RN| exact NTH| exact QB| exact ZT| exact I| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H LSETNG MULNG CMPR slo SLO1 SLO2 SSH0 PF0 FF0"] Lemma dv_DW : forall n, dvL4_stmt n -> forall Q, dvDW_stmt n Q.
  Proof.
    intros n K4. induction Q as [|Q IH].
    - apply dv_DW1, dv_DW2, dv_DW3, dv_DW4, dv_DW5; [exact K4| intros Q' E; discriminate E].
    - apply dv_DW1, dv_DW2, dv_DW3, dv_DW4, dv_DW5; [exact K4| intros Q' E; injection E as <-; exact IH].
  Qed.

  (* [comment removed for export] *)
  Definition dvLg (n : nat) (pc : Z)
      (RS : mpd -> mpd -> Z -> Z -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> Prop) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c16 c40 c128 c136 t2pad gb u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 c16 c40 ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    RS dLX dZ i ny c16 c40 a0 a1 a2 a3 a4 a5 t0 t3 s8v ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ny - 1)) s8v s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition dvL3f_stmt (n : nat) : Prop :=
    dvLg n 0x9fb3c (fun _ dZ i ny c16 c40 _ a1 _ _ _ _ _ _ s8v =>
      c16 = Z_to_bv 64 i /\ c40 = Z_to_bv 64 (i - ny) /\ a1 = Z_to_bv 64 (md_p dZ) /\ s8v = Z_to_bv 64 (4 * (i - ny))).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@C7096915042.242 D33876909647.241D63873442836.241K21870859916.243K33980871419.243K52049772347.243K66327680928.242L12469921329.0  L14447101554.5  L16000728743.6  L1685717371.0   L18351506484.5  L19133426325.6  L21868076544.5  L29832375856.1  L32321742194.6  L33982282359.5  L36571201320.0  L40066488116.5  L41807682882.3  L52051507127.5  L59310648043.7  L59667784614.1  L61798049332.6  L66330468140.4  L7735389571.5   L8532400182.5   L8929159528.233 L8929620893.230 L9356559676.11  P14461423358.243P18341645496.243P40077402040.243P61800574648.243P66327680928.242P7750690063.243 Q10812129647.237Q11801279589.241Q19991027068.243Q26295627581.237Q33874924623.242Q33877164610.237Q33889765055.237Q48467890406.243Q49698585326.241Q50458135125.237Q51120983794.237Q51135677050.240Q51337909069.234Q63871233556.242Q63873185817.237Q63883819088.237Q63885703535.234Q63885753572.237Q8943555749.234 00000101A02K03F04304`04a04b04c05805905:05P05Q05U05k05l05m05n06506606P06T06U06V06W06h08709F0:10;=0<S0=i0??0?@0@N0A;0A]0A^0B=0Bm0CZ0DG0DH0E50ET0F?0Fj0GW0HA0Hh0IO0J60J]0K<FS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY13INA2NZ2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY12Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2wv3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2wv3PZF3IDXFFFS2dA1i2ny3NY13NYI3INASFS2dZ1i2ny3idx4LENZ3IDXFS2dZS2dZ1i2ny3idx4LENZ3IDXFSFS2wv2MBFS2dZ1i2ny3idx4LENZ3IDX3NTHS2dZFFFS2dZ1i2ny3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wvFS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZFS1R2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3ACV3PZC3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_L3f : forall n, (forall Q, dvDW_stmt n Q) -> dvL3f_stmt n.
  Proof.
    intros n KDW. unfold dvL3f_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (CWZ : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dZ) (4 * md_n dZ))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
    set (idx := i - ny) in *.
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
    destruct (nth_error (md_limbs dZ) (Z.to_nat idx)) as [wz|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ IDX; lia].
    pose proof (munch_refl [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wz _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep.
    pose proof (u32arr_store_ok asegs mq (md_p dZ) (md_limbs dZ) idx _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dZ) (md_limbs dZ) idx vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (sp1 + 168) _ |- _ => rename H into CZ2 end.
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 2%nat dZ idx _ CST eq_refl OZH IDX MU WM HH2 MI2 ST2 ltac:(rewrite EAZ; exact CZ2) UAZ' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2.
    eapply (KDW (Z.to_nat (2^32))) with (i := i) (ny := ny) (k := k) (wz := wv); [exact CST2| apply linv_Z; exact LI| exact RN| | | exact HK| exact (UWK UW)| exact BPOS| exact NA98| exact HV| exact HF].
    - unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_limbs]. apply nth_error_upd_same. clear - IDX LENZ. lia.
    - rewrite Z2Nat.id by (clear; lia). pose proof (Z.mod_pos_bound (w32 wv - 1) (2^32) ltac:(clear; lia)) as MB. clear - MB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3e_stmt (n : nat) : Prop :=
    dvLg n 0x9fb34 (fun _ dZ i ny c16 c40 _ a1 a2 _ _ a5 _ _ _ =>
      c16 = Z_to_bv 64 i /\ c40 = Z_to_bv 64 (i - ny) /\ a1 = Z_to_bv 64 (md_p dZ) /\ a2 = Z_to_bv 64 (i - ny) /\ a5 = Z_to_bv 64 (FB + 128)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0@D16160648224.215D21608135327.215L11330210333.1  L11553410088.1  L12469921329.0  L13763573786.12 L14447004729.2  L1651366350.211 L1685717371.0   L18351345279.2  L21866712442.1  L26543722394.211L33179143781.210L36923507618.11 L39172636981.0  L40066129279.2  L47410864422.1  L49508988902.1  L52054009037.1  L55348327217.2  L58078104602.12 L60450734269.12 L61799984162.3  L62119455258.12 L7738195705.2   L9356559676.11  P14461423358.216P18341645496.216P40077402040.216P61800574648.216P7750690063.216 Q11801279589.215Q33677842214.212Q49698585326.214Q50587737655.213Q52744951088.215Q52747231024.216Q57618637969.215Q57620590225.216Q6324920119.212 00000e01Z01^01b01c01g01h02K02L02M02Q03404904b04c04d04h04l05005605:05c05d05h05i06T07d0940:D0;T0<\0=G0=`0>B0>a0?L0@70@b0AM0AfS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2FBS2FBFS2FBFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nySFS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX1i2ny4NA983SPR2F04SP1R3NY13NYI3INAS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1SFS2FBS2FBS2FBS1i2nyS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a03ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a03ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a03ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a03ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2ny2a03ALO2F12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2ny2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2ny2F02HBS2LF3LFB2FB4gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a02HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 F64 FRSH CFB ESF"] Lemma dv_L3e : forall n, dvL3f_stmt n -> dvL3e_stmt n.
  Proof.
    intros n KF. unfold dvL3e_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWTP : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 128) 12) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 128, FB + 140)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. replace ((i - ny) * 4) with (4 * (i - ny)) by (clear; lia).
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 a0 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := FB + 128) (b := FB + 140); try eassumption.
      - clear; lia.
      - right. clear. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2).
    { eapply M_uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    unfold dvL3f_stmt, dvLg in KF.
    eapply KF with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L11601619207.104L22502704494.104L35497640934.103L35497640934.104L56087813952.105L56093676630.104L8929208426.104 L9068841147.105 00000J00f01@01Z02;02Z03903XS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn1xS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn1x2Hx1nS2LF2ra2sp3LFB2FB3sp14gapn1x2HxS2LF2ra2sp3LFB2FB3sp14gapn1x2HxS2LF2ra2sp3LFB2FB3sp14gapn1x2Hx". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
  Proof.
    intros x Hx. change 18446744073709551615 with (Z.ones 64).
    rewrite <- Z.ldiff_ones_l_low; [| lia | ].
    2:{ destruct (Z.eq_dec x 0) as [->|]. cbn; lia. apply Z.log2_lt_pow2; lia. }
    rewrite Z.ldiff_land, Z.land_comm, Z.land_ones by lia. unfold Z.lnot.
    rewrite <- (Z.mod_add _ 1) by lia. change (Z.ones 64) with (2^64 - 1). rewrite Z.mod_small; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L33279436385.10500000OS2LF2ra2sp3LFB2FB3sp14gapn1i2ny". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma idx_word : forall i ny, 0 <= ny < 2^64 -> Z_to_bv 64 (i + 1 + Z.lxor ny 18446744073709551615) = Z_to_bv 64 (i - ny).
  Proof.
    intros i ny Hn. rewrite lxor_ones64 by exact Hn. rewrite <- (P_mpi_div_mpi.zbv_add_modulus sp (i - ny)). f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3d_stmt (n : nat) : Prop :=
    dvLg n 0x9fb18 (fun dLX _ i ny c16 _ a0 _ a2 _ _ a5 _ t3 _ =>
      c16 = Z_to_bv 64 i /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a5 = Z_to_bv 64 (FB + 128) /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00h0@D35300034347.237D60189065437.237L10353723466.4  L11144352574.3  L12469921329.0  L1685717371.0   L26988105723.2  L28632618922.2  L32418217581.2  L36757749421.12 L38060875949.12 L42888674241.1  L48700858022.1  L49304025233.2  L49442955282.12 L52258283942.1  L53577728712.1  L55990716303.231L57698627611.2  L59321132283.8  L66426995373.12 L67372926033.2  L68145906413.7  L8929159528.231 L9356559676.11  P28627113325.238P32425075329.237P32425075329.238P49296947798.238P57713046236.238P67365848726.238Q11968186855.238Q15236175980.234Q15902372977.234Q16827575549.238Q22537500579.235Q25954107624.238Q26295627581.235Q28465177121.235Q30354477985.235Q31760482915.235Q31762679511.235Q31762760540.232Q3421936230.237 Q44276068355.232Q49473433708.234Q50458135125.235Q51003241457.234Q5265442331.236 Q55535214433.235Q57228775306.237Q60189065437.238Q67148242924.234Q68235297648.237Q8943555749.232 Q9875315697.234 00001N02l03:03F03G03H03R03S03T04=04f04k05005105605;05@05c05d06D06m06n07H08V09A0:P0;b0=50>D0?60@E0AT0B80BY0BZ0C>0C?0CU0D70DW0E70EW0F70Fl0GL0H00HH0Hi0IL0Il0J^0Kc0LG0M20MH0MiS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n2hq3dLX1i2ny3SPR2F04SP1R3HTq2X03PX02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3SPR2F04SP1R2X03PX02HB5Ha_st5Hl_stS1i2ny3NY13NYIS2sp3sp13SP1FSS3sp14gapnFFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S3sp1FS3sp1S3sp1S3sp1S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyFS3dLX1i2ny3NY13NYI3IXL4LENX4NTHXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2dA1i2ny4NA983NY13NYI3INAS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX1i2ny3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F13EAX2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyFS2LF3LFB4gapn1n3dLX1i2ny3NY13NYI3PX0FS2LF3LFB4gapn1n3dLX2nyS2LF3LFB3sp14gapn1n3dLX2ny4SP1R2HBS2LF3LFB4gapn1n3dLX1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX1i2ny3NY13IXLS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB4gapn1n3dLX1i2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF3LFB3sp14gapn1n3dLX2ny2HB5Ha_stS2LF3LFB4gapn1n3dLX1i2ny3NY13IXLS2LF2lo3LFB3sp14gapn3LOC1n3dLX1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB3sp14gapn1n3dLX1i2ny2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64"] Lemma dv_L3d : forall n, dvL3e_stmt n -> dvL3d_stmt n.
  Proof.
    intros n KE. unfold dvL3d_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX).
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & _); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _) _]. rewrite EAZ in CZ. unfold mpi_cells in CZ.
    destruct (nth_error (md_limbs dLX) (Z.to_nat i)) as [wx|] eqn:NTHX; [| apply nth_error_None in NTHX; exfalso; clear - NTHX LENX IXL NY1 NYI; lia].
    pose proof (munch_refl [(sp1, sp1 + 152)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    shadow_chk OPX (md_p dLX + 4 * i) 4.
    pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) i wx _ UAX NTHX ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep. rewrite (idx_word i ny) by (clear - NY1 NYI INA NA98; lia).
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    unfold dvL3e_stmt, dvLg in KE.
    eapply KE with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3c_stmt (n : nat) : Prop :=
    dvLg n 0x9faf8 (fun dLX _ i ny c16 _ a0 _ a2 a3 a4 a5 _ t3 _ =>
      c16 = Z_to_bv 64 i /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (4 * (i + 1)) /\ a5 = Z_to_bv 64 (FB + 128) /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@D16160648224.235D21608135327.235K45774582958.235L11330210333.1  L11553410088.1  L12469921329.0  L13763573786.12 L14447004729.2  L1685717371.0   L18351345279.2  L20062927322.229L21866712442.1  L32992563726.229L36923507618.11 L40066129279.2  L41247884433.4  L42624411411.2  L45777250370.2  L47410864422.1  L49508988902.1  L52054009037.1  L58078104602.12 L59321132283.8  L60450734269.12 L61799984162.3  L62119455258.12 L7738195705.2   L8929159528.229 L8929620893.226 L9356559676.11  P14461423358.236P18341645496.236P40077402040.236P45774582958.236P61800574648.236P7750690063.236 Q11801279589.235Q26295627581.233Q27494214828.233Q30354477985.233Q44276068355.230Q44831811468.232Q49698585326.234Q50160634539.230Q50160717600.233Q50162387860.233Q50458135125.233Q50587737655.233Q52744951088.235Q52747231024.236Q55535214433.233Q57618637969.235Q57620590225.236Q65027834781.232Q8943555749.230 00000e01Z02N02R02V02W02[02\02]02^03A03E03h04Q04R04`04g04h04l05005405805X06A06B06F06G07U08c09N0:^0;n0=>0=m0?=0@E0A00AF0Aj0BF0Bb0C;0C]0D=0D]0E=0EU0F40F_0GJ0Gf0HQ0I<0IU0IkS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2wx4LENX3PXF2HB5Ha_st5Hl_stS2FBS2FBFS2FBFSFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1i2ny3NY13NYIS3dLX1iFS2FBS2FBS2FBS2FBS3dLX1i2ny3NY13NYI3IXL4LENX4NTHXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBFS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXCS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny3ALO2F12wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2wx3EAX2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2ny3ALO2F12wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2nyS2LF3LFB4gapn1n3dLX1i2ny3NY13NYI3PX0S2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB2FB4gapn1n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2ny2HB5Ha_stS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX1i2nyS2LF3LFB2FB4gapn1n3dLX2ny2F02HBS2LF3LFB2FB4gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB2FB4gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2nyS2LF3LFB4gapn1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 F64 FRSH CFB ESF LOC CSP FN64"] Lemma dv_L3c : forall n, dvL3d_stmt n -> dvL3c_stmt n.
  Proof.
    intros n KD. unfold dvL3c_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX).
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 1))) as [wx|] eqn:NTHX; [| apply nth_error_None in NTHX; exfalso; clear - NTHX LENX IXL NY1 NYI; lia].
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWTP : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 128) 12) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 128, FB + 140)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. replace (md_p dLX + 4 * (i + 1) + -8) with (md_p dLX + 4 * (i - 1)) by (clear; lia).
    zstep. zstep. shadow_chk OPX (md_p dLX + 4 * (i - 1)) 4.
    pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) (i - 1) wx _ UAX NTHX ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) c40 ny k c128 c136 t2pad gb u0 (sx32 wx) u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := FB + 128) (b := FB + 140); try eassumption.
      - clear; lia.
      - right. clear. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2).
    { eapply M_uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    unfold dvL3d_stmt, dvLg in KD.
    eapply KD with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3b_stmt (n : nat) : Prop :=
    dvLg n 0x9faf0 (fun dLX _ i ny c16 _ a0 _ a2 a3 a4 _ _ t3 _ =>
      c16 = Z_to_bv 64 i /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (4 * (i + 1)) /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@D21608135327.214D4163361427.214 L11330210333.1  L11553410088.1  L12469921329.0  L13763573786.12 L14447004729.2  L1685717371.0   L18351345279.2  L21866712442.1  L36923507618.11 L40066129279.2  L47410864422.1  L49508988902.1  L52054009037.1  L58078104602.12 L60450734269.12 L61799984162.3  L62119455258.12 L63852571929.210L67354423519.210L7738195705.2   L9356559676.11  P14461423358.215P18341645496.215P40077402040.215P61800574648.215P7750690063.215 Q11801279589.214Q15022709143.211Q27650778534.211Q29016610020.214Q29018595044.215Q31636558775.211Q49698585326.213Q52744951088.214Q52747231024.215Q58026207754.211Q66164858198.21200000e01Z01^01b01c01g01h01i01j01n02W02X02\02`02d02h03Q03R03V04904\04]05H06X07h0980:H0;P0<;0<_0=80=c0>N0>g0?I0@40@_0A@0A_S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2FBS2FBFS2FBFSFS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBS2FBS2FBS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2nyFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2ny2a13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2ny2a13ALO2F12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2ny2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2ny2a12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF3LFB2FB4gapn1n3dLX2ny2F02HB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC"] Lemma dv_L3b : forall n, dvL3c_stmt n -> dvL3b_stmt n.
  Proof.
    intros n KC. unfold dvL3b_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWTP : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 128) 12) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 128, FB + 140)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) c40 ny k c128 c136 t2pad gb a1 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := FB + 128) (b := FB + 140); try eassumption.
      - clear; lia.
      - right. clear. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2).
    { eapply M_uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    unfold dvL3c_stmt, dvLg in KC.
    eapply KC with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3a2_stmt (n : nat) : Prop :=
    dvLg n 0x9fac8 (fun dLX _ i ny c16 _ a0 a1 a2 a3 a4 _ t0 t3 _ =>
      c16 = Z_to_bv 64 i /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a1 = Z_to_bv 64 2 /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (4 * (i + 1)) /\ t0 = Z_to_bv 64 i /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L5259210451.2   L54968207265.2  L59321132283.6  L66253707781.222L8929159528.227 L8941826058.224 L9356559676.11  Q26295627581.231Q27494214828.231Q30354477985.231Q44288275348.228Q50147674428.228Q50160717600.231Q50162387860.231Q50458135125.231Q55535214433.231Q8956254002.228 00000700=00U01c03004=04h05>05a06=06Y07807W08608N08j09@S3dLX1iS1i2KIS3dLX1i3IXL4LENX2KI4NTHXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13IXL2X03PX03PXC2KIS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13IXL2X03PX03PXC2KIS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB4gapn1n3dLX2nyS2LF3LFB4gapn1n3dLX1i2ny3NY13PX02KIS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2nyS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M XW SP1 FRSH CFB LOC CSP FN64"] Lemma dv_L3a2 : forall n, dvL3b_stmt n -> dvL3a2_stmt n.
  Proof.
    intros n KB. unfold dvL3a2_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX).
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    unfold dvL3b_stmt, dvLg in KB.
    (* [comment removed for export] *)
    zstep; if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by (clear - NY1 NYI INA NA98; lia).
    - (* [comment removed for export] *)
      destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 2))) as [wx|] eqn:NTHX; [| apply nth_error_None in NTHX; exfalso; clear - NTHX LENX IXL KI; lia].
      zstep. zstep. replace (md_p dLX + 4 * (i + 1) + -12) with (md_p dLX + 4 * (i - 2)) by (clear; lia).
      zstep. zstep. shadow_chk OPX (md_p dLX + 4 * (i - 2)) 4.
      pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) (i - 2) wx _ UAX NTHX ltac:(clear - KI; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      eapply KB with (i := i) (ny := ny) (k := k); [exact CST| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply KB with (i := i) (ny := ny) (k := k); [exact CST| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3a_stmt (n : nat) : Prop :=
    dvLg n 0x9fac0 (fun dLX _ i ny _ _ a0 _ a2 a3 a4 _ t0 t3 _ =>
      a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (4 * (i + 1)) /\ t0 = Z_to_bv 64 i /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@D35300034347.212D60189065437.212L11144352574.3  L12469921329.0  L1685717371.0   L26988105723.2  L28632618922.2  L36757749421.12 L38060875949.12 L42888674241.1  L48700858022.1  L49304025233.2  L49442955282.12 L52258283942.1  L53577728712.1  L57698627611.2  L66426995373.12 L67372926033.2  L9356559676.11  P28627113325.213P49296947798.213P57713046236.213P67365848726.213Q11968186855.213Q16827575549.213Q25954107624.213Q27938377354.209Q28465177121.210Q3421936230.212 Q35291925783.209Q5265442331.211 Q57228775306.212Q60189065437.213Q68235297648.21200001G02^02j02k02l03603703`04I04N04S04T04Y04^04c04d05M05N06907H08W09I0:X0;g0;h0;i0<J0<l0=a0>E0>h0?Z0@_0AJS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n2hq3dLX1i2ny3SPR2F04SP1R3HTq2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3SPR2F04SP1R2HB5Ha_st5Hl_stS2sp3sp13SP1FSS3sp14gapnFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S3sp1FS3sp1S3sp1S3sp1FS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX1i2ny3ALO2F12HB5Ha_st5Hl_stFFS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF3LFB3sp14gapn1n3dLX2ny4SP1R2HBS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB3sp14gapn1n3dLX2ny2HB5Ha_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX1i2ny2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX1i2ny2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC"] Lemma dv_L3a : forall n, dvL3a2_stmt n -> dvL3a_stmt n.
  Proof.
    intros n KA. unfold dvL3a_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    pose proof (munch_refl [(sp1, sp1 + 152)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSO c0 (Z_to_bv 64 i) c40 ny k c128 c136 t2pad gb u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    unfold dvL3a2_stmt, dvLg in KA.
    eapply KA with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L18932531241.10400000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma zbv_add_k : forall x k, Z_to_bv 64 (x + k * 18446744073709551616) = Z_to_bv 64 x.
  Proof.
    intros x k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL2_stmt (n : nat) : Prop :=
    dvLg n 0x9fa9c (fun dLX _ i ny _ _ a0 _ a2 a3 a4 _ t0 t3 _ =>
      a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a2 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL)
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (4 * (i + 1)) /\ t0 = Z_to_bv 64 i /\ t3 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@C7096915042.238 D33876909647.237D63873442836.237K21870859916.239K33980871419.239K52049772347.239K66327680928.238L12469921329.0  L14447101554.5  L16000728743.6  L1685717371.0   L18351506484.5  L19122243928.3  L19133426325.6  L21868076544.5  L29832375856.1  L33982282359.5  L40066488116.5  L52051507127.5  L55990716303.227L59667784614.1  L61798049332.6  L66330468140.4  L68145906413.7  L7735389571.5   L8929159528.229 L8929620893.226 L9356559676.11  P14461423358.239P18341645496.239P40077402040.239P61800574648.239P66327680928.238P7750690063.239 Q10812129647.233Q11801279589.237Q19991027068.239Q21912640266.230Q26295627581.233Q33874924623.238Q33877164610.233Q48467890406.239Q49472925079.230Q49698585326.237Q50458135125.233Q51003780618.230Q51120983794.233Q51135677050.236Q51337909069.230Q63871233556.238Q63873185817.233Q63883819088.233Q63885703535.230Q7526228119.230 Q8943555749.230 00000101A02K03F04304`04a04b04c05805905:05C05Y05Z05^05_05`05a06M06Q06R06S06m06n08=09L0:70;C0<Y0=o0?E0?F0@T0AA0Ac0Ad0BN0Bm0C]0DJ0DK0E80Ee0FD0Fn0GY0HD0I10I[0JB0Ji0KP0L=0L\FS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY13INA2NZ2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY12Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2wv3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2wv3PZF3IDXFFFS2dA1i2ny3NY13NYI3INASFS2dZ1i2nyS2dZ1i2ny3idx4LENZ3IDXFS2dZFFFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2dZFFS2dA1i2ny4NA983NY13NYI3INAFS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wvFS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZFS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS1R2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3ACV3PZC3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDXS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_L2 : forall n, dvL3a_stmt n -> dvL2_stmt n.
  Proof.
    intros n KA. unfold dvL2_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (CWZ : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dZ) (4 * md_n dZ))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
    set (idx := i - ny) in *.
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
    pose proof (munch_refl [(md_p dZ + 4 * idx, md_p dZ + 4 * idx + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (md_p dZ + (4 * (i + 1) + Z.lxor ny 18446744073709551615 * 4))) with (Z_to_bv 64 (md_p dZ + 4 * idx))
      by (rewrite lxor_ones64 by (clear - NY1 NYI INA NA98; lia); rewrite <- (zbv_add_k (md_p dZ + 4 * idx) 4); f_equal; subst idx; clear; lia).
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_store_ok asegs mq (md_p dZ) (md_limbs dZ) idx _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dZ) (md_limbs dZ) idx vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (sp1 + 168) _ |- _ => rename H into CZ2 end.
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 2%nat dZ idx _ CST eq_refl OZH IDX MU WM HH2 MI2 ST2 ltac:(rewrite EAZ; exact CZ2) UAZ' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2.
    unfold dvL3a_stmt, dvLg in KA.
    eapply KA with (i := i) (ny := ny) (k := k); [exact CST2| apply linv_Z; exact LI| exact RN| repeat split; reflexivity| exact HK| exact (UWK UW)| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0100@L10169803483.2  L10353723466.4  L12376170316.5  L23890265425.1  L2591472616.263 L32876037132.6  L34785933159.2  L35203387009.257L39172636981.0  L41247884433.4  L41663468825.253L42624411411.2  L48774854378.254L576250137.251  L59321132280.6  L59323229416.8  L59323229417.8  L61997691801.2  L63436913239.4  L66253248513.250L8700593567.263 L8929111654.252 L8929159528.253 L8929159528.256 L8929159528.258 L8929162512.255 L8929620893.250 L9356559676.11  Q10596710310.256Q15686330807.256Q22537500579.259Q26295627581.259Q26295627581.262Q26295627581.264Q27494214828.264Q30354477985.259Q30354477985.264Q31760482915.259Q31760482915.261Q31762760540.256Q34674277469.258Q37991040876.258Q38669678599.259Q44275611278.261Q44276068355.256Q50160307238.261Q50160717600.264Q50162387860.264Q50458135125.259Q50458135125.262Q50458135125.264Q523213388.258  Q54608293134.262Q55128416958.261Q55533542357.261Q55535214433.264Q66562145521.258Q66791183892.262Q66793640608.259Q66793640608.261Q8943472942.259 Q8943555749.256 Q8943620648.261 Q9992779027.262 00000700E00R00U01;01G01N01O01P01^02D02K03c04I04b05C05d05l06707O07P08g0:?0;V0<n0>F0?^0@I0@e0AA0Ah0BA0BZ0C30CZ0D=0D\0E?0Eb0FE0Fa0GH0Gj0HI0Hl0IO0J20JU0K00KI0Kd0L@0Lb0MD0Mg0NF0Nj0OG0Od0PA0PZ0Q30QL0QmS3dLX1iS1i2ny3NY13NYIS4PHIb1n1v2HVS1iS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2nyS3FRb1n1f2HFS2dY2nyFSS1i2ny3NY13NYIS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2nyS3dLX1iS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2nyS2dY2ny3NY13NYL4LENY4NTHYS3dLX1i2ny3NY13NYI3IXL4LENX5NTHXIS3dLX1i2ny3NY13NYI3IXL4LENX5NTHXJS2ny3NY1S1n1i2ny2RNS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0FS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2X03PX02Y04NY1'3PY03PYCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2X03PX02Y04NY1'3PY03PYCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXC2Y03PY0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB2FB4gapn1n3dLX2dY2nyS2LF3LFB2FB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYI3PX0S2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYI3PX0S2LF3LFB4gapn1n3dLX2dY1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY1i2ny3IXLS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB2FB4gapn1n3dLX2dY2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n3dLX2dY1i2ny3IXLS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY1i2nyS2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY1i2nyS2LF3LFB2FB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n3dLX2dY2ny3NYL4NY1'S2LF3LFB4gapn1n3dLX2dY1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY1i2ny3IXLS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2ny3NY1S2LF3LFB4gapn1n3dLX2dY2ny3NY1S2LF3LFB4gapn1n3dLX2dY2ny3NY1S2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2nyS2LF3LFB4gapn1n3dLX2dY2ny3NY13PY0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M XW SP1 GAP FRSH CFB LOC CSP FN64"] Lemma dv_L1 : forall n, dvL2_stmt n -> dvLH_stmt (S n).
  Proof.
    intros n K2. unfold dvLH_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    rewrite dvVr_S in HV. rewrite dvFr_S in HF. rewrite Nat2Z.inj_succ in RN.
    assert (HV' : v + dvVrnd + dvVr n <= PHIb) by (clear - HV; lia). assert (HF' : f + dvFrnd + dvFr n <= FRb) by (clear - HF; lia).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX). rewrite EAX in CX. unfold mpi_cells in CX.
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & NSY & _ & _ & _ & _ & HFY & _ & Y8 & _ & OYs); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _ & Y0 & LENY & NRY & OWY) SGY]. rewrite OYH in OWY. ddestruct OWY as (NY1' & INY & PY16 & UAY). rewrite EAY in CY. unfold mpi_cells in CY.
    ddestruct (HFY OYH) as (PY0 & PYC & _ & _ & PYF & _).
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HHq| exact INY]).
    destruct (nth_error (md_limbs dLX) (Z.to_nat i)) as [wxi|] eqn:NTHXI; [| apply nth_error_None in NTHXI; exfalso; clear - NTHXI LENX IXL NY1 NYI; lia].
    destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 1))) as [wxj|] eqn:NTHXJ; [| apply nth_error_None in NTHXJ; exfalso; clear - NTHXJ LENX IXL NY1 NYI; lia].
    destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 1))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY NYL NY1; lia].
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    unfold dvL2_stmt, dvLg in K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    replace (md_p dLX + i * 4) with (md_p dLX + 4 * i) by (clear; lia).
    zstep. zstep. shadow_chk OPX (md_p dLX + 4 * i) 4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. replace (md_p dY + (ny - 1) * 4) with (md_p dY + 4 * (ny - 1)) by (clear; lia).
    zstep. zstep.
    pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) i wxi _ UAX NTHXI ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    shadow_chk OPY (md_p dY + 4 * (ny - 1)) 4. clear RD.
    (* [comment removed for export] *)
    pose proof (u32arr_read asegs mq (md_p dY) (md_limbs dY) (ny - 1) wy _ UAY NTHY ltac:(clear - NY1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. replace ((i + 1) * 4) with (4 * (i + 1)) by (clear; lia).
    zstep; if_cases KB.
    - (* [comment removed for export] *)
      zstep.
      eapply K2 with (i := i) (ny := ny) (k := k); [exact CST| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV'| exact HF'].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. replace (md_p dLX + 4 * (i + 1) + -8) with (md_p dLX + 4 * (i - 1)) by (clear; lia).
      zstep. zstep. shadow_chk OPX (md_p dLX + 4 * (i - 1)) 4.
      pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) (i - 1) wxj _ UAX NTHXJ ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD. zstep. zstep. zstep. zstep. zstep.
      zstep; if_cases KC.
      + zstep. zstep.
        eapply K2 with (i := i) (ny := ny) (k := k); [exact CST| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV'| exact HF'].
      + zstep. zstep. zstep.
        eapply K2 with (i := i) (ny := ny) (k := k); [exact CST| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV'| exact HF'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59309008877.400000=S1i2ny3NYI2RN". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SHL LSETNG MULNG MULI CMPR CMPI ASM ASP slo SLO1 SLO2 SSH0 PF0 FF0 KFIN"] Lemma dv_LH : forall n, dvLH_stmt n.
  Proof.
    induction n as [|n IH].
    - unfold dvLH_stmt. intros until t6. intros CST LI RN. exfalso.
      ddestruct LI as (_ & _ & _ & _ & _ & _ & _ & _ & NY1 & NYI & _). clear - RN NYI. lia.
    - apply dv_L1, dv_L2, dv_L3a, dv_L3a2, dv_L3b, dv_L3c, dv_L3d, dv_L3e, dv_L3f. intros Q. apply dv_DW.
      apply dv_L4; [apply dv_L5; exact IH| apply dv_L4c, dv_L5; exact IH].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L14808106792.1 L31813111044.6 L33324003609.10L54583660252.10L56496830848.10L56545230362.10L58192282731.6 L59757927748.1000000400J00K00V00`00l01>01IS2nxS2dA2nx2ny3NY13NYX3NXAFS2nx2ny3NYXS2dA2dT2NTS3dLX2nx3NXLS2dA2nx2ny3NY13NXAS2dA2nx3NXA". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SHL LSETNG MULNG MULI CMPR CMPI ASM ASP slo SLO1 SLO2 SSH0 PF0 FF0 KFIN"] Lemma dv_LOOP_ok : A_mpi_div_mpi_M_c24.dvLOOP_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn
                       (md_n dA * dvVrnd + PF) (md_n dA * dvFrnd + FF).
  Proof.
    unfold A_mpi_div_mpi_M_c24.dvLOOP_stmt. intros until t6. intros CST EAX EAY EAZ EAD OXH OYH OZH OTH NY1 NYX NXA NXL NYL NZ NT HK UW BPOS NA98 HV HF XBD YBD.
    replace (Z_to_bv 64 nx) with (Z_to_bv 64 (nx - 1 + 1)) by (f_equal; clear; lia).
    eapply (dv_LH (Z.to_nat (md_n dA))) with (i := nx - 1) (ny := ny) (k := k); [exact CST| | | exact HK| exact UW| exact BPOS| exact NA98| |].
    - pose proof (dvBT_pos ltac:(clear - NY1 NYX NXA; lia)) as BTP. unfold linvk. repeat split; try assumption; try (clear - NY1 NYX NXA NXL NT; lia).
      clear - XBD BTP NY1 NYX NXA. nia.
    - rewrite Z2Nat.id by (clear - NY1 NYX NXA; lia). clear - NY1 NYX NXA. lia.
    - unfold dvVr. rewrite Z2Nat.id by (clear - NY1 NYX NXA; lia). exact HV.
    - unfold dvFr. rewrite Z2Nat.id by (clear - NY1 NYX NXA; lia). exact HF.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Fr.
  End Call.
End WalkL.
