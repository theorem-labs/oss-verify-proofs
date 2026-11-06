(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_div_stmtA A_mpi_div_mpi_P A_mpi_div_mpi_C.
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


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L45529543036.600000@S1a1b1K2H12H22H3". (* [comment removed for export] *)
Lemma dv_c24_arith : forall a b (n : nat) K, a <= b + Z.of_nat n + 1 -> n = 4%nat -> b + C24_DIV_MPI <= C24MAX -> K <= 2 -> a + K <= C24MAX.
Proof. intros a b n K H1 -> H2 H3. unfold C24_DIV_MPI in H2. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Ltac dv_c24 R HIA HNDk C24H :=
  lazymatch goal with |- cnt24 ?LBx + _ <= C24MAX =>
    match goal with CSx : _ |- _ =>
      eapply (dv_c24_arith _ _ _ _ (A_mpi_client2.cs_cnt24 asegs R HIA HNDk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CSx));
        [ first [reflexivity | eassumption] | exact C24H | first [eassumption | (vm_compute; discriminate)] ]
    end end.


Section WalkS.
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

  Local Notation SHB := (Z_to_bv 64 (Z.shiftr B 3 + al_sb AL)).
  Local Notation SHA10 := (Z_to_bv 64 (Z.shiftr (A + 10) 3 + al_sb AL)).
  Local Notation SHB8 := (Z_to_bv 64 (Z.shiftr (B + 8) 3 + al_sb AL)).
  Local Notation SHA := (Z_to_bv 64 (Z.shiftr A 3 + al_sb AL)).
  (* [comment removed for export] *)
  Local Notation RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6 :=
    (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
         (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6).



  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L12806154935.4  L12806161768.4  L21041645149.3  L23970764156.129L36571201320.0  L48827096264.2  L54425651213.3  L59308583409.4  L59310648043.5  L8929159528.124 L8929620893.121 Q18402213789.125Q18402295455.122Q18402376468.127Q26295627581.125Q28760468501.122Q32303523866.125Q326359207.127  Q41280089850.125Q50458135125.125Q8943555749.122 00000<00=00E01>01?01E01N01Z01l03B04X05205L05f06=06W07507O07i08@08WS2dB1r2HR2K2FS1k1r2HkS2LF2ra2sp3LFB2dB2FB3sp14gapn1k1r2Hk4LENZ3EP02HR3SPR2EB1wSS2dB1rS2dB1r2HRS2dB1r2Hk2HRS2dB1r4LENZ2HR3NTHS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2HkS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk3EP02HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2HkS2LF3LFB2dB4gapn1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO LFB gapn SP1"] Lemma dv_SCANB1 : forall (k : nat) (hc : HST asegs R HIA) (mc : mem) (r : Z) xra t0 a7 t3 t4 t5 t6,
    r <= Z.of_nat k ->
    bytes_at asegs mc (md_p dB) (u32s (md_limbs dB)) -> Z.of_nat (length (md_limbs dB)) = md_n dB -> 0 < md_p dB -> md_n dB <= 10000 ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_p dB) (4 * md_n dB) ->
    1 <= r <= md_n dB ->
    (forall xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s5v s6v s7v s8v s10v,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v SH4 s5v s6v s7v s8v (Z_to_bv 64 FB) s10v (Z_to_bv 64 (-12)) t3 t4 t5 t6)
             F (Z_to_bv 64 0x9f790) fc None mc (seg_rom asegs))) ->
    (forall r', 1 <= r' <= md_n dB -> limb32 (md_limbs dB) (Z.to_nat (r' - 1)) <> 0 -> forall t0 a1 a6 a7,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 (Z_to_bv 64 (md_n dB)) SHB
                  (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 r') a6 a7
                  (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 B)
                  (Z_to_bv 64 (-12)) t3 t4 t5 t6)
             F (Z_to_bv 64 0x9f2b8) fc None mc (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB)
               (Z_to_bv 64 (md_p dB + 4 * (r - 1))) (Z_to_bv 64 (md_n dB)) SHB (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 r) (Z_to_bv 64 (md_p dB + 4 * (r - 1))) a7
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 B)
               (Z_to_bv 64 (-12)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f278) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until t6; intros Hk EBY LENZ EP0 NB OEL HR KZ KNZ; [exfalso; clear - Hk HR; lia|].
    rt_facts. pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64c.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OEL (md_p dB + 4 * (r - 1)) 4.
    destruct (nth_error (md_limbs dB) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dB) (md_limbs dB) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_of_read (md_limbs dB) r w NTH) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as By.
    zstep. if_cases K0; zify_cond K0; rewrite ?bv_unsigned_sx32 in K0.
    - assert (NZ : limb32 (md_limbs dB) (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K0; rewrite E; reflexivity).
      eapply (KNZ r); [exact HR| exact NZ].
    - zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NB; lia).
      + replace (Z_to_bv 64 (md_p dB + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dB + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH hc mc (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia].
      + zstep. eapply KZ.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L11014214210.3  L21041645149.3  L21774718167.2  L22690221216.4  L22690243455.4  L23120643753.4  L23120701814.4  L23970764156.127L31326834835.4  L35162014678.3  L36571201320.0  L42787892550.3  L4622677642.3   L54425651213.3  L59308583409.4  L59310648043.5  L64930767917.4  L8929159528.122 L8929620893.119 Q26295627581.123Q34291222827.120Q34291305632.125Q34291402793.123Q42131479398.125Q48338484555.123Q49424719380.120Q50458135125.123Q53360483131.123Q8943555749.120 00000900A00G00H00I00J00V01O01[01d01e01n01o02802D02V02b04805N05e06?06Y07307M07k08E08\09609MS2dA1r2HRS1k1r2HkS2dA1rFFFS2dA1r2HR2K2S2LF2ra2sp3LFB2dA2FB3sp14gapn1k1r2Hk4LENZ3EP02HR3SPR2EB1wS2dA1r2HR2K2S2dA1r2HRSS2dA1r2HRFS2dA1r2HRS2dA1r2Hk2HRS2dA1r4LENZ2HR3NTHS2dA1r2HR2K2S1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS2LF3LFB2dA4gapn1k1r2HkS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2Hk3EP02HRS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2HkS2LF3LFB2dA4gapn1k1r2Hk2HRS2LF3LFB2dA4gapn1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO LFB gapn SP1"] Lemma dv_SCANA : forall (k : nat) (hc : HST asegs R HIA) (mc : mem) (r : Z) xra t0 a7 t5 t6,
    r <= Z.of_nat k ->
    bytes_at asegs mc (md_p dA) (u32s (md_limbs dA)) -> Z.of_nat (length (md_limbs dA)) = md_n dA -> 0 < md_p dA -> md_n dA <= 10000 ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_p dA) (4 * md_n dA) ->
    1 <= r <= md_n dA -> lval (md_limbs dA) (md_n dA) = lval (md_limbs dA) r ->
    (forall i, SIGF (md_limbs dA) (md_n dA) i -> forall t0 a1 a6 a7,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 (Z_to_bv 64 (md_n dB)) SHB
                  (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 i) a6 a7
                  (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
                  (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
             F (Z_to_bv 64 0x9f3a0) fc None mc (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB)
               (Z_to_bv 64 (md_p dA + 4 * (r - 1))) (Z_to_bv 64 (md_n dB)) SHB (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 r) (Z_to_bv 64 (md_p dA + 4 * (r - 1))) a7
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
               (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
          F (Z_to_bv 64 0x9f360) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until t6; intros Hk EBY LENZ EP0 NB OEL HR INV KX; [exfalso; clear - Hk HR; lia|].
    rt_facts. pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64c.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. zstep. shadow_chk OEL (md_p dA + 4 * (r - 1)) 4.
    destruct (nth_error (md_limbs dA) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dA) (md_limbs dA) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_of_read (md_limbs dA) r w NTH) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as By.
    zstep. if_cases K0; zify_cond K0; rewrite ?bv_unsigned_sx32 in K0.
    - assert (NZ : limb32 (md_limbs dA) (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K0; rewrite E; reflexivity).
      eapply (KX r). split; [clear - HR; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - HR; lia| exact NZ].
    - apply (proj1 (sxz_zero_iff _ By)) in K0.
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NB; lia).
      + replace (Z_to_bv 64 (md_p dA + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dA + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH hc mc (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia| idtac].
        rewrite INV. apply lval_drop_zero; [clear - HR; lia| rewrite LYr; exact K0].
      + zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 HR; lia).
        eapply (KX 0). split; [clear - HR; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero (md_limbs dA) r) by (try (clear - HR; lia); rewrite LYr; exact K0). replace (r - 1) with 0 by (clear - K2 HR; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L11014214210.3  L12806154935.4  L12806161768.4  L21032719895.3  L21041645149.3  L23970764156.129L3120206871.3   L31326834835.4  L32584089863.3  L36571201320.0  L48827096264.2  L54425651213.3  L59308583409.4  L59310648043.5  L60102106463.4  L60102128256.4  L64930767917.4  L8929159528.124 L8929620893.121 Q18402213789.125Q18402295455.122Q18402376468.127Q26295627581.125Q28760468501.122Q32303523866.125Q326359207.127  Q41280089850.125Q50458135125.125Q8943555749.122 00000900E00F00G00O01H01Q01]01f01g01m02602B02T02U02V02b04805N05h06B06\07307M07k08E08_09609MS2dB1r2HRS2dB1r2HR2K2FFS1k1r2HkS2LF2ra2sp3LFB2dB2FB3sp14gapn1k1r2Hk4LENZ3EP02HR3SPR2EB1wS2dB1r2HRS2dB1r2HR2K2S2dB1r2HRSS2dB1rS2dB1r2HRS2dB1r2Hk2HRS2dB1r4LENZ2HR3NTHFFS2dB1r2HR2K2S1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP11k1r2Hk4LENZ3EP02HR3ALO3ACV3SPR2EBS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2HkS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk3EP02HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2Hk2HRS2LF3LFB2dB4gapn1k1r2HkS2LF3LFB2dB4gapn1k1r2Hk". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO LFB gapn SP1"] Lemma dv_SCANB2 : forall (k : nat) (hc : HST asegs R HIA) (mc : mem) (r i : Z) xra t0 a6 a7 t5 t6,
    r <= Z.of_nat k ->
    bytes_at asegs mc (md_p dB) (u32s (md_limbs dB)) -> Z.of_nat (length (md_limbs dB)) = md_n dB -> 0 < md_p dB -> md_n dB <= 10000 ->
    aobj asegs AL (hcs asegs R HIA hc) mc (md_p dB) (4 * md_n dB) ->
    1 <= r <= md_n dB -> lval (md_limbs dB) (md_n dB) = lval (md_limbs dB) r ->
    (forall j, SIGF (md_limbs dB) (md_n dB) j -> forall a1 a4 a6 a7,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 (Z_to_bv 64 j) SHB
                  a4 (Z_to_bv 64 i) a6 a7
                  (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
                  (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
             F (Z_to_bv 64 0x9f3f8) fc None mc (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB)
               (Z_to_bv 64 (md_p dB + 4 * (r - 1))) (Z_to_bv 64 r) SHB (Z_to_bv 64 (md_p dB + 4 * (r - 1))) (Z_to_bv 64 i) a6 a7
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
               (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
          F (Z_to_bv 64 0x9f3b8) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until t6; intros Hk EBY LENZ EP0 NB OEL HR INV KX; [exfalso; clear - Hk HR; lia|].
    rt_facts. pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64c.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    zstep. zstep. shadow_chk OEL (md_p dB + 4 * (r - 1)) 4.
    destruct (nth_error (md_limbs dB) (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read asegs mc (md_p dB) (md_limbs dB) (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_of_read (md_limbs dB) r w NTH) as LYr.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as By.
    zstep. if_cases K0; zify_cond K0; rewrite ?bv_unsigned_sx32 in K0.
    - assert (NZ : limb32 (md_limbs dB) (Z.to_nat (r - 1)) <> 0) by (rewrite LYr; intros E; apply K0; rewrite E; reflexivity).
      eapply (KX r). split; [clear - HR; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - HR; lia| exact NZ].
    - apply (proj1 (sxz_zero_iff _ By)) in K0.
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - HR NB; lia).
      + replace (Z_to_bv 64 (md_p dB + 4 * (r - 1) + -4)) with (Z_to_bv 64 (md_p dB + 4 * (r - 1 - 1))) by (f_equal; clear; lia).
        eapply (IH hc mc (r - 1)); try eassumption; first [clear - Hk; lia| clear - HR K2; lia| idtac].
        rewrite INV. apply lval_drop_zero; [clear - HR; lia| rewrite LYr; exact K0].
      + zstep. replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 HR; lia).
        eapply (KX 0). split; [clear - HR; lia|]. split; [| left; reflexivity].
        rewrite INV, (lval_drop_zero (md_limbs dB) r) by (try (clear - HR; lia); rewrite LYr; exact K0). replace (r - 1) with 0 by (clear - K2 HR; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0140@L11014202208.4  L21041645149.3  L27126084869.4  L29010565666.143L29532144176.6  L29797090679.5  L30163643142.227L32195670001.157L33377451076.1  L35254139924.2  L36571201320.0  L37116573683.6  L37116926125.6  L39245721523.4  L39245873389.4  L42608597650.1  L43767829327.5  L44196099187.159L53897658059.6  L54425499820.2  L57857825604.164L58487066637.164L59308551419.8  L59308551544.8  L66151410442.4  L66151422504.4  L67686497038.2  L8927475209.156 L8929111654.158 L8929159528.159 L8929159528.161 Q1173500124.159 Q18401780580.161Q18402213789.164Q18403877664.163Q21042218976.160Q23022923204.159Q26295627581.162Q26295627581.164Q28760977902.161Q31289377519.160Q31954582050.160Q32303523866.164Q324714643.163  Q34069183529.160Q34289208511.159Q34291402793.162Q34291402793.163Q37708009648.160Q37710113435.159Q39402952415.161Q41280089850.164Q42131644399.163Q45124942924.160Q47860023380.162Q48338484555.162Q49422539648.159Q50458135125.162Q50458135125.164Q50845955027.162Q53360483131.162Q61916722222.161Q61917304426.162Q63070022717.162Q63396246492.162Q65903420605.161Q8944060766.161 Q8945570097.159 00000;00C00P01P01a01n01o02\02_02e02f02g02h02i03403703D04104B04H04I04J04c05<05G05R05X07H0980:h0<X0=60=Y0><0>_0>`0?>0?Z0@60@\0@]0A;0Ab0BH0BI0Bl0CO0D20DP0Dn0EL0F20FX0GR0H00HW0I=0IY0J50Jl0KR0L00LN0LO0LP0Ln0MJ0MfS1r1i2HR2K0S1k1r2HkS2wx2wy2K12K2S2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1k1r1i2Hk2AR2BR2NA2HR3SPR2I1S2dA1r1i2HR2I12R1S2dA2dB1i3INVFS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1k1r1i2HkS1rS2dB1rSFFFS1r1i2HR2R1S1rS2dA2dB1i3INVS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1k1r1i2HkS2dB1r1i2HR2J12R1S1r2R1FFS2dA1r1i4LENA2HR2I12R12NXS2dB1r1i4LENB2HR2J12R12NYS1r1i2HR2K0S1r1i2Hk2HRS2dA1rS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dA2dB2FB3sp14gapn3SP11k1r1i2Hk2AR2BR4LENA2HR3INV3ALO3ACV3SPR2I12R13PA03EBaS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dA2dB2FB3sp14gapn3SP11k1r1i2Hk2AR2BR4LENB2HR3INV3ALO3ACV3SPR2J12R13PB03EBbS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dA2dB2FB3sp14gapn3SP11k1r1i2Hk2AR2BR4LENA2HR3INV3ALO3ACV3SPR2I12R13PA03EBaS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dA2dB2FB3sp14gapn3SP11k1r1i2Hk2AR2BR4LENB2HR3INV3ALO3ACV3SPR2J12R13PB03EBbS2LF1A3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1S2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1S2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1FS2LF1A3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2J1FS2LF1A3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R13PB0S2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2J1FS2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1S2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1S2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R1S2LF1A3LFB2dA2dB4gapn1k1r1i2HkS2LF1A3LFB2dA2dB4gapn1k1r1i2HkS2LF1B3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2J1S2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2I1S2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1k1r1i2Hk2AR2BR2A83SPRS2LF1B3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk3INV2R13PA0S2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2I1S2LF3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2HkS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1k1r1i2Hk2BR2B83SPRS2LF3LFB2dA2dB4gapn1k1r1i2Hk2HR3INV2I1S2LF1B3LFB2dA2dB4gapn1k1r1i2HkS2LF1B3LFB2dA2dB4gapn1k1r1i2HkFFS2LF1B3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2HkS2LF3LFB2dA2dB4gapn1k1r1i2Hk". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO LFB gapn SP1"] Lemma dv_CMPLOOP : forall (k : nat) (hc : HST asegs R HIA) (mc : mem) (r i : Z) xra t0 t1 t2 a0 a1 a2 a7 t5 t6,
    r <= Z.of_nat k ->
    rw_cells asegs mc A (mpi_cells (md_p dA) (Z_to_bv 64 (md_sg dA)) (md_n dA) (md_pad dA)) -> aobj asegs AL (hcs asegs R HIA hc) mc A 16 ->
    rw_cells asegs mc B (mpi_cells (md_p dB) (Z_to_bv 64 (md_sg dB)) (md_n dB) (md_pad dB)) -> aobj asegs AL (hcs asegs R HIA hc) mc B 16 ->
    0 <= A /\ A + 16 <= 2^64 -> 0 <= B /\ B + 16 <= 2^64 -> A mod 8 = 0 -> B mod 8 = 0 ->
    bytes_at asegs mc (md_p dA) (u32s (md_limbs dA)) -> Z.of_nat (length (md_limbs dA)) = md_n dA -> md_n dA <= 10000 ->
    (1 <= md_n dA -> 0 < md_p dA /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_p dA) (4 * md_n dA)) ->
    bytes_at asegs mc (md_p dB) (u32s (md_limbs dB)) -> Z.of_nat (length (md_limbs dB)) = md_n dB -> md_n dB <= 10000 ->
    (1 <= md_n dB -> 0 < md_p dB /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_p dB) (4 * md_n dB)) ->
    0 <= r <= i -> SIGF (md_limbs dA) (md_n dA) i -> SIGF (md_limbs dB) (md_n dB) i ->
    Z.sgn (lval (md_limbs dA) i - lval (md_limbs dB) i) = Z.sgn (lval (md_limbs dA) r - lval (md_limbs dB) r) ->
    (lval (md_limbs dB) (md_n dB) <= lval (md_limbs dA) (md_n dA) -> forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f404) fc None mc (seg_rom asegs))) ->
    (lval (md_limbs dA) (md_n dA) < lval (md_limbs dB) (md_n dB) -> forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7,
       aevtA asegs (KF asegs R HIA hc mo0) POSTD (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f5bc) fc None mc (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hc mo0) POSTD
      (MS (RG xra t0 t1 t2 a0 a1 a2 SHB (Z_to_bv 64 (4 * r - 4)) (Z_to_bv 64 (r + 1)) SHA a7 t5 t6) F (Z_to_bv 64 0x9f8fc) fc None mc (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until t6; intros Hk CA OA CB OB AR BR A8 B8 EBA LENA NA FA EBB LENB NB FB' HR SX SY INV KMAIN KEARLY.
    all: unfold mpi_cells in CA, CB; rt_facts; pose proof (hcs_ok asegs R HIA hc) as CSOKc; pose proof (cs_ok_sb _ _ CSOKc) as SB64c;
      pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo0) as KINV;
      pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl asegs mc) as WM;
      dpose SX as (I1 & I2 & I3); dpose SY as (J1 & J2 & J3).
    - assert (r = 0) as -> by (clear - Hk HR; lia).
      zstep. zstep.
      apply KMAIN. rewrite I2, J2. rewrite !lval_0 in INV. cbn in INV. pose proof (Z.sgn_spec (lval (md_limbs dA) i - lval (md_limbs dB) i)). clear - INV H. lia.
    - zstep. zstep; if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - HR I1 NA; lia).
      + assert (r = 0) as -> by (clear - K0 HR; lia).
        apply KMAIN. rewrite I2, J2. rewrite !lval_0 in INV. cbn in INV. pose proof (Z.sgn_spec (lval (md_limbs dA) i - lval (md_limbs dB) i)). clear - INV H. lia.
      + assert (R1 : 1 <= r) by (clear - K0 HR; lia).
        destruct (FA ltac:(clear - R1 HR I1; lia)) as [PA0 OAL]. destruct (FB' ltac:(clear - R1 HR J1; lia)) as [PB0 OBL].
        pose proof (u32ro_bound _ _ _ _ EBA) as EBa. pose proof (u32ro_bound _ _ _ _ EBB) as EBb.
        destruct (nth_error (md_limbs dA) (Z.to_nat (r - 1))) as [wx|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX LENA HR I1 R1; lia].
        destruct (nth_error (md_limbs dB) (Z.to_nat (r - 1))) as [wy|] eqn:NY; [| apply nth_error_None in NY; exfalso; clear - NY LENB HR J1 R1; lia].
        pose proof (u32ro_read asegs mc (md_p dA) (md_limbs dA) (r - 1) wx _ EBA NX ltac:(clear - R1; lia) eq_refl) as RDX.
        pose proof (u32ro_read asegs mc (md_p dB) (md_limbs dB) (r - 1) wy _ EBB NY ltac:(clear - R1; lia) eq_refl) as RDY.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        replace (md_p dA + (4 * r - 4)) with (md_p dA + 4 * (r - 1)) by (clear; lia).
        (* [comment removed for export] *)
        zstep. zstep. shadow_chk OAL (md_p dA + 4 * (r - 1)) 4.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        replace (md_p dB + (4 * r - 4)) with (md_p dB + 4 * (r - 1)) by (clear; lia).
        (* [comment removed for export] *)
        zstep. zstep. shadow_chk OBL (md_p dB + 4 * (r - 1)) 4.
        (* [comment removed for export] *)
        zstep. clear RDX RDY.
        pose proof (limb32_of_read (md_limbs dA) r wx NX) as LXr. pose proof (limb32_of_read (md_limbs dB) r wy NY) as LYr.
        pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(clear; lia)) as Bx.
        pose proof (Z.mod_pos_bound (bv_unsigned wy) (2^32) ltac:(clear; lia)) as By.
        (* [comment removed for export] *)
        zstep; if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
        * apply (proj1 (sxz_lt_iff _ _ By Bx)) in K1.
          apply KMAIN. rewrite I2, J2. rewrite (cmp_step_gt (md_limbs dA) (md_limbs dB) r) in INV by (first [exact R1| rewrite LXr, LYr; exact K1]).
          pose proof (Z.sgn_spec (lval (md_limbs dA) i - lval (md_limbs dB) i)). clear - INV H. lia.
        * apply (proj1 (sxz_le_iff _ _ Bx By)) in K1.
          zstep. zstep; if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
          -- apply (proj1 (sxz_le_iff _ _ By Bx)) in K2.
             replace (Z_to_bv 64 (4 * r - 4 + -4)) with (Z_to_bv 64 (4 * (r - 1) - 4)) by (f_equal; clear; lia).
             replace (Z_to_bv 64 r) with (Z_to_bv 64 (r - 1 + 1)) by (f_equal; clear; lia).
             eapply (IH hc mc (r - 1) i); try eassumption; first [clear - Hk; lia| clear - HR R1; lia| idtac].
             rewrite INV. apply cmp_step_eq; [exact R1| rewrite LXr, LYr; clear - K1 K2; lia].
          -- apply (proj1 (sxz_lt_iff _ _ Bx By)) in K2.
             zstep. apply KEARLY. rewrite I2, J2. rewrite (cmp_step_lt (md_limbs dA) (md_limbs dB) r) in INV by (first [exact R1| rewrite LXr, LYr; exact K2]).
             pose proof (Z.sgn_spec (lval (md_limbs dA) i - lval (md_limbs dB) i)). clear - INV H. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis IA2 : md_own dA = LStatic -> (forall i, 0 <= i < 4 * md_n dA -> ro_addr asegs (wa (md_p dA + i)) = true) -> img_norz (md_p dA) (4 * md_n dA) = true.
  Hypothesis IB2 : md_own dB = LStatic -> (forall i, 0 <= i < 4 * md_n dB -> ro_addr asegs (wa (md_p dB + i)) = true) -> img_norz (md_p dB) (4 * md_n dB) = true.
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Hypothesis ESB : In dB es.
  (* [comment removed for export] *)
  Hypothesis BE_PHI : copy_PHI dA + 4 * AVOL_CALL <= PHIb.
  Hypothesis BE_FR : copy_FR d + 4 * fr_charge (d + 1) <= FRb.

  (* [comment removed for export] *)
  Definition opv (hc : HST asegs R HIA) (mc : mem) (e : mpd) : Prop :=
    rw_cells asegs mc (md_addr e) (mpi_cells (md_p e) (Z_to_bv 64 (md_sg e)) (md_n e) (md_pad e))
    /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_addr e) 16
    /\ (0 <= md_addr e /\ md_addr e + 16 <= 2^64) /\ md_addr e mod 8 = 0
    /\ bytes_at asegs mc (md_p e) (u32s (md_limbs e)) /\ Z.of_nat (length (md_limbs e)) = md_n e /\ 0 <= md_n e <= 10000
    /\ (1 <= md_n e -> 0 < md_p e /\ aobj asegs AL (hcs asegs R HIA hc) mc (md_p e) (4 * md_n e))
    /\ (md_sg e = 1 \/ md_sg e = -1).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L22961942245.0L33534655380.3L39280637297.0L59308546259.4L59308586248.2L59314923118.300000100;00<00H00N00VSS1e2A03B16SS1e1l3LEN2N0S1i2HiS1e2N01K". (* [comment removed for export] *)
  #[using="IMG"] Lemma opv_of_mpd : forall (hc : HST asegs R HIA) LBc LFc mc e,
    HM asegs R HIA hc LBc LFc mc -> mpd_at asegs mc LBc e -> aobj asegs AL (hcs asegs R HIA hc) mc (md_addr e) 16 ->
    (md_own e = LStatic -> (forall i, 0 <= i < 4 * md_n e -> ro_addr asegs (wa (md_p e + i)) = true) -> img_norz (md_p e) (4 * md_n e) = true) ->
    opv hc mc e.
  Proof.
    intros hc LBc LFc mc e HHc ME OE IE. pose proof ME as [(CE & A8 & A0 & LEN & NR & OWN) SG]. unfold MPI_MAX_LIMBS in NR.
    pose proof (rw_cells_bound _ _ _ _ CE) as B16. cbn [cells_size csize Nat.add mpi_cells] in B16.
    unfold opv. split; [exact CE|]. split; [exact OE|]. split; [clear - B16 A0; lia|]. split; [exact A8|].
    destruct (md_own e) eqn:EO.
    - destruct OWN as [P0 N0]. split; [| split; [exact LEN| split; [exact NR| split; [intros K; exfalso; clear - K N0; lia| exact SG]]]].
      assert (EL : md_limbs e = []) by (destruct (md_limbs e); [reflexivity| exfalso; cbn in LEN; clear - LEN N0; lia]).
      rewrite EL, P0. split; [clear; lia|]. split; [cbn; clear; lia|]. intros i Hi. cbn in Hi. exfalso. clear - Hi. lia.
    - ddestruct OWN as (N1 & IN & P16 & UA). split; [exact (u32arr_ro _ _ _ _ UA)|]. split; [exact LEN|]. split; [exact NR|]. split; [| exact SG].
      intros _. pose proof (u32ro_bound _ _ _ _ (u32arr_ro _ _ _ _ UA)) as [P0 _].
      split; [| eapply hm_aobj_block; [exact HHc| exact IN]].
      destruct (hm_apart asegs R HIA hc LBc LFc mc HHc) as [HBR _]. rewrite Forall_forall in HBR.
      destruct (HBR (md_p e, 4 * md_n e) ltac:(apply in_app_iff; left; exact IN)) as (B0 & _). exact B0.
    - ddestruct OWN as (N1 & P4 & P0 & BY & RO). split; [exact BY|]. split; [exact LEN|]. split; [exact NR|]. split; [| exact SG].
      intros _. split; [exact P0|].
      eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| exact (IE eq_refl RO)].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR ra LOS SLO LFB XW gapn SP1 FRSH ESF LOC CSP FN64"] Lemma cs_opv_ext : forall mq hq LBq ls dW CS v f e, CSTA mq hq LBq ls dW CS DV_FSH v f -> In e es ->
    (md_own e = LStatic -> (forall i, 0 <= i < 4 * md_n e -> ro_addr asegs (wa (md_p e + i)) = true) -> img_norz (md_p e) (4 * md_n e) = true) ->
    opv hq mq e.
  Proof.
    intros mq hq LBq ls dW CS0 v f e CST He IE.
    edestruct (A_mpi_client2.cs_ext_facts asegs R HIA) with (e := e) as (ME & OEs & _); try eassumption.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (_ & _ & _ & _ & HHq).
    eapply opv_of_mpd; [exact HHq| exact ME| exact OEs| exact IE].
  Qed.

  #[using="IMG NEEDR ra LOS SLO LFB XW W0AS gapn SP1 FRSH LOC CSP FN64"] Lemma cs_opv_w : forall mq hq LBq ls dW CS v f, CSTA mq hq LBq ls dW CS DV_FSH v f -> opv hq mq dW.
  Proof.
    intros mq hq LBq ls dW CS0 v f CST.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWq & NSW & EAW & _ & _ & _ & _ & _ & _ & _ & OWq); try eassumption.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (_ & _ & _ & _ & HHq).
    eapply opv_of_mpd; [exact HHq| exact MWq| rewrite EAW; exact OWq| intros EO; exfalso; exact (NSW EO)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59314923118.400000;S2dX2dA1E1K". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO LFB XW W0AS gapn SP1 FRSH ESF LOC CSP FN64 SXA IA2 ESA"] Lemma cs_opv_A : forall mq hq LBq ls CS v f, CSTA mq hq LBq ls dX CS DV_FSH v f -> opv hq mq dA.
  Proof.
    intros mq hq LBq ls CS0 v f CST.
    destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
    - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
      rewrite EQA. eapply cs_opv_w; exact CST.
    - eapply cs_opv_ext; [exact CST| exact (ESA NE)| exact IA2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR ra LOS SLO LFB XW gapn SP1 FRSH ESF LOC CSP FN64 IB2 ESB"] Lemma cs_opv_B : forall mq hq LBq ls dW CS v f, CSTA mq hq LBq ls dW CS DV_FSH v f -> opv hq mq dB.
  Proof. intros mq hq LBq ls dW CS0 v f CST. eapply cs_opv_ext; [exact CST| exact ESB| exact IB2]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma keep0_sub_w : forall mq hq LBq ls CS SHC v f, CSTA mq hq LBq ls dX CS SHC v f ->
    forall b, In b (mpd_keep LB dX) -> In b (mpd_keep LBq dX).
  Proof.
    intros mq hq LBq ls CS0 SHC v f CST b Hb. unfold A_mpi_client2.cstateA in CST.
    ddestruct CST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SUB & _).
    apply In_mpd_keep_intro; [apply SUB; [eapply In_mpd_keep; exact Hb| exact (A_mpi_client2.In_mpd_keep_not_blk_w _ _ _ Hb)]| exact (A_mpi_client2.In_mpd_keep_not_blk_w _ _ _ Hb)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L1540877545.3 L67028235242.800000<00[S2sp3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP1". (* [comment removed for export] *)
  #[using="NEEDR ra LOS SLO LFB XW W0AS gapn SP1 FRSH LOC CSP FN64"] Lemma w_aobj_step : forall mq hq LBq ls CS SHC v f m2 (h2 : HST asegs R HIA) WX,
    CSTA mq hq LBq ls dX CS SHC v f ->
    presA asegs R (mpd_keep LBq dX) LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) WX mq m2 ->
    (forall x, hcs asegs R HIA hq x -> hcs asegs R HIA h2 x) ->
    aobj asegs AL (hcs asegs R HIA h2) m2 (md_addr dX) 16.
  Proof.
    intros mq hq LBq ls CS0 SHC v f m2 h2 WX CST HP HCS2.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OWq); try eassumption.
    eapply (aobj_cs_mono asegs AL); [exact HCS2|].
    eapply (presA_aobj asegs R); [exact (hcs_ok asegs R HIA hq)| exact HP| exact OWq| | clear - LOS SLO SP1 NEEDR; lia| intros x Hx; eapply hcs_below_top; exact Hx].
    eapply (A_mpi_client2.w0_client_step asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 256 dX LOC CSP XW W0AS (mpd_keep LBq dX) sp1); [| clear - SP1; lia].
    eapply keep0_sub_w; exact CST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L56765667309.113L6667563486.113 00000]01LS2LF2ra2sp3LFB2FB3sp14gapn4TOPx2Fx2HF2HT1a2HaS2LF2ra2sp3LFB2FB3sp14gapn3SPx4TOPx2Fx3HSP1a2Ha". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma uwc_presA_s : forall LBx LFx SPx SSPx TOPx Wx mx mx' vv Fx dd,
    presA asegs R LBx LFx SPx SSPx TOPx Wx mx mx' -> uwc asegs mx (arl_stklo R) TOPx vv Fx dd -> SPx <= Fx ->
    (forall a, Fx <= a < TOPx -> outside Wx a) -> 0 <= Fx -> TOPx <= 2^64 -> uwc asegs mx' (arl_stklo R) TOPx vv Fx dd.
  Proof.
    intros LBx LFx SPx SSPx TOPx Wx mx mx' vv Fx dd [P _] UW HSP HW HF HT.
    eapply uwc_transport; [exact UW|]. intros a Ha. apply (proj1 (P a ltac:(lia) ltac:(left; lia) (HW a Ha))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation C_CLEAN_X := (A_mpi_div_mpi_C.dv_CLEAN_X R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB APF ESF PZ ZF BUD BUDF).
  Local Notation C_EXIT0 := (A_mpi_div_mpi_C.dv_EXIT0 R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP LFB dX dA dB es PHIb FRb H0M XW FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB APF).
  (* [comment removed for export] *)
  Local Notation DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2c gb u0 u1 u2 jq :=
    (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 FB) c128 c136 (Z_to_bv 64 FB))
         t2c [] gb [C4 u0; C4 u1; C4 u2] jq).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L10864128136.5  L15170693011.10 L17130068715.6  L19980016842.7  L21063630438.5  L2397676628.0   L25082674492.41 L25498419105.2  L26983617546.4  L27632495159.244L27692466477.3  L29956516996.0  L35663928186.7  L36762852034.4  L43003029338.7  L45155411430.1  L49037504437.6  L50102073030.3  L52045659405.3  L52101693566.14 L5259999888.194 L53577728712.1  L55690173965.5  L55738333094.1  L59308632561.3  L59314923118.1  L59314923118.4  L60098763854.3  L60135355119.8  L61868843.1     L6203415987.3   L62037211595.7  L6203936179.1   L65614147016.1  L66151427842.16 L7132061466.9   L8931608776.1   L9321644808.3   L9323345550.5   L9356559676.11  L9838743115.2   Q1356123914.197 Q20013594135.197Q39029445783.197Q64054320522.19700000A00f01601N01^01_01`01g02402a02n02o03D03Q03R03V03k04;04G05806>06C06T06X06c06f07107;07<07@07E07`07e07j08F08i08n09909:09e09o0:W0;B0;m0<US2dX2dA2dB3dX32K1S1R3HIA1h1d3FRb2D04BUDF5BE_FR2hq4HFRqS1d3FRb2D05BE_FRS1R3HIA1h2sp3TOP3sp13SP1S2dA4PHIb6BE_PHISFS1d3CAPS2dA3ARq1a2HaS2LF2ra2sp3LFB2dX2dA2FB3sp14gapn3t2c3SZ24XB16S1d3FRb5BE_FRSS1R3HIA1h2sp2lo3TOP1HS2dA1d2D03NRAFS2FBS1R2sp2lo3SLO3sp13SP1S2dA4PHIb6BE_PHIS2sp3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12hq2XS1a2HaS2LF2ra2sp1X3LFB2dX2dA2XE2FB3sp14gapn3t2c3SZ23SPR2F04SP1R3ARq3X0q4XB16S3sp1S2sp2dA3sp13SP11KS2FBS2dX3X0q2KRS1KS2dX2dA1E1KS1R2lo3LOSFS2FBS3sp1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R3HIA1h2dA4PHIb3BUD6BE_PHI2hq3HVqS3sp1S2dX3dX32K1FS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1RS2LF2lo3LFB2dX3sp14gapn3LOC3t2c3SZ24XB16S2LF2sp2lo3LFB2dX3sp14gapn3SP13t2c3SZ24XB16S2LF2sp2lo3LFB2dX3sp14gapn3SP13t2c3SZ24XB16S2LF2lo3LFB2dX3sp14gapn3LOC3t2c3SZ24XB16". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 ESA BE_PHI BE_FR"] Lemma dv_EARLY : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2c gb u0 u1 u2 jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2c gb u0 u1 u2 jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    cells_size t2c = 16%nat -> UWCD mq -> 0 < mpd_abs dB ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f5bc) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 SZ2 UW BPOS. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof CHq as CHq'. unfold A_mpi_div_mpi_C.DCS in CHq'. apply Forall_cons_iff in CHq'. destruct CHq' as [SPC _]. cbn [fst snd] in SPC. unfold A_mpi_div_mpi_C.dv_sp in SPC.
    edestruct (A_mpi_client2.cs_w_facts asegs R HIA) as (MWq & _ & _ & XWq & XLSq & CRWq & CRWLq & HFW & ASW & WFB & OWq); try eassumption.
    pose proof (cs_opv_A _ _ _ _ _ _ _ CST) as (CAq & OAq & ARq & A8q & _).
    pose proof MWq as [(CXq & X8q & X0q & _) _].
    pose proof (rw_cells_bound _ _ _ _ CXq) as XB16. cbn [cells_size csize Nat.add mpi_cells] in XB16.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by (rewrite XE; clear - XB16 X0q; lia); [exfalso; rewrite XE in KR; clear - KR X0q; lia|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    assert (AF : mpd_at asegs mq LBq dA /\ client_range L (LBq ++ fdata LF1) lo (md_addr dA) 16
                 /\ (md_own dA = LHeap -> client_range L (LBq ++ fdata LF1) lo (md_p dA) (4 * md_n dA))).
    { destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
      - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
        rewrite EQA. split; [exact MWq|]. split; [exact CRWq| exact CRWLq].
      - edestruct (A_mpi_client2.cs_ext_facts asegs R HIA) with (e := dA) as (ME & _ & CRE & CREL & _); try eassumption; [exact (ESA NE)|].
        split; [exact ME|]. split; [exact CRE| exact CREL]. }
    ddestruct AF as (MAq & CRAq & CRALq).
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5).
    pose proof COPY as CPY. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_gen_c, A_MPI_COPY in CPY.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CPY with (h := hq) (LB := LBq) (LF := LF1) (dX := dX) (dY := dA) (lo := lo) (d := d);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HHq | exact HK1 | exact MWq | exact NST | exact MAq | exact SXA | exact XWq | exact STq | exact LOS | exact MIq | exact TPV | exact OWq | exact CRAq | exact CRALq | exact UWX | reflexivity
              | exact OAq
              | lazymatch goal with
                | |- copy_sep dX dA _ _ =>
                    split; [exact OA1|]; split; [exact OA2|]; split; [exact OA3|];
                    split; [destruct OA4 as [K|K]; [left; exact K| right; clear - K SP1; lia]|];
                    split; [intros NN; destruct (OA5 NN) as [K|K]; [left; exact K| right; clear - K SP1; lia]| intros a Ha; clear - Ha ARq; lia]
                | |- lo <= sp1 - 112 - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- md_own dA = LStatic -> _ => intros EO; apply (IA2 EO); pose proof MAq as [(_ & _ & _ & _ & _ & OWA) _]; rewrite EO in OWA; exact (proj2 (proj2 (proj2 (proj2 OWA))))
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD BE_PHI; unfold AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF BE_FR D0; unfold fr_charge in *; lia
                | |- _ = Z_to_bv 64 (md_addr dX) => rewrite XE; reflexivity
                | |- _ = Z_to_bv 64 (md_addr dA) => rewrite AE; reflexivity
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dX3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    ddestruct RR3 as (RV & EA3 & PD3 & FRP3).
    assert (CST3 : CSTA m3 h3 LB3 [dLX; dY; dZ; dT] dX3 (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2c gb u0 u1 u2 jq) DV_FSH (0 + copy_PHI dA) (0 + copy_FR d)).
    { eapply (A_mpi_client2.cs_binop_w asegs R HIA) with (mq := mq) (hq := hq) (SPx := sp1); try eassumption; try (clear - SP1; lia).
      - eapply w_aobj_step; [exact CST| exact HP3| exact HCS3].
      - destruct RV as [(_ & _ & K1 & _)|(_ & K1 & _)]; clear - K1; lia.
      - unfold A_mpi_div_mpi_C.DCS. repeat (apply Forall_cons; [cbn [fst snd]|]); [left; clear; lia| left; clear; lia| left; clear; lia| left; clear; lia| left; clear - SP1; lia| right; clear; lia| right; clear; lia| right; clear; lia| apply Forall_nil].
      - apply Forall_forall. intros d0 _ K. exact K. }
    assert (UW3 : UWCD m3).
    { destruct UWX as [[XS _]|CAP]; [| apply uwc_cap; clear - CAP; lia].
      rewrite <- HSq. eapply uwc_presA_s; [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [clear - Ha XS LOS SLO SP1 NEEDR; lia| exact I]. }
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3. clear LAWS KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    assert (CP0 : 0 <= copy_PHI dA /\ 0 <= copy_FR d).
    { pose proof MAq as [(_ & _ & _ & _ & NRA & _) _]. unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge; unfold AVOL_CALL. clear - NRA D0. lia. }
    assert (HSZ3 : md_n dX3 <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB)) by (unfold div_mpi_nz; destruct RV as [(_ & _ & K1)|(_ & K1 & _)]; clear - K1; lia).
    destruct RV as [(-> & _)|(-> & _)].
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply C_EXIT0 with (r := 0); [exact CST3| exact EAZ| exact OX0| exact OY0| exact OZ0| exact OT0| exact SZ2| reflexivity| clear; lia| intros _; exact BPOS| exact HSZ3| |].
      + clear - BE_PHI CP0. unfold AVOL_CALL in *. lia.
      + clear - BE_FR CP0 D0. unfold fr_charge in *. lia.
    - (* [comment removed for export] *)
      zstep. zstep.
      eapply C_CLEAN_X with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| exact SZ2| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| intros K; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; clear - K; lia| exact HSZ3| |].
      + clear - BE_PHI. lia.
      + clear - BE_FR. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation COK := (A_mpi_client2.chunk_okA (bv_unsigned sp) sp1 FB 256).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L12834952178.6L17377900485.4L2617442223.4 L33486410124.3L35663928186.7L59654567629.9L60098763854.3L62018535662.100000>00I00S00\01101Q01[01^S2sp2lo1a1b2K2S2FB1a1b2K2S2FB1a1b1KS2FB1a2K1S1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3SLO3sp13SP11a2K1S1R2lo3LOSS1R". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma cs_store : forall mq hq LBq ls dW CS0 CS' SHC v f m2 a b,
    CSTA mq hq LBq ls dW CS0 SHC v f ->
    HM asegs R HIA hq LBq LF1 m2 -> munch [(a, b)] mq m2 -> wmono asegs mq m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 ->
    a <= b -> ((sp1 <= a /\ b <= bv_unsigned sp) \/ (FB + 32 <= a /\ b <= FB + 248)) ->
    (forall d0, In d0 ls -> b <= md_addr d0 \/ md_addr d0 + 16 <= a) ->
    Forall (fun ac => rw_cells asegs m2 (fst ac) (snd ac)) CS' -> Forall (COK ls) CS' ->
    CSTA m2 hq LBq ls dW CS' SHC v f.
  Proof.
    intros mq hq LBq ls dW CS0 CS' SHC v f m2 a b CST HH2 MU WM MI2 ST2 HAB HLOC HLS CH2 OK2. rt_facts.
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(a, b)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
      destruct HLOC as [[K1 K2]|[K1 K2]]; [eapply crange_sub; [exact SCSq| clear - K1 SP1 SLO NEEDR; lia| clear - K2 HAB; lia]| eapply crange_sub; [exact CFBq| clear - K1; lia| clear - K2; lia]]. }
    assert (CST1 : CSTA mq hq LBq ls dW [] SHC v f).
    { eapply (A_mpi_client2.cs_set_cells asegs R HIA); [exact CST| apply Forall_nil| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq ls dW [] SHC v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(a, b)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [exact HAB|]. split; [| exact HLS].
        destruct HLOC as [K|K]; [left; exact K| right; clear - K; lia].
      - apply Forall_nil. }
    eapply (A_mpi_client2.cs_set_cells asegs R HIA); [exact CST2| exact CH2| exact OK2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma dcs_ok : forall ls spc t2c zc gb tpc jq spc' t2c' zc' gb' tpc' jq',
    Forall (COK ls) (DCS spc t2c zc gb tpc jq) ->
    cells_size spc' = cells_size spc -> cells_size t2c' = cells_size t2c -> cells_size zc' = cells_size zc -> cells_size tpc' = cells_size tpc ->
    Forall (COK ls) (DCS spc' t2c' zc' gb' tpc' jq').
  Proof.
    intros ls spc t2c zc gb tpc jq spc' t2c' zc' gb' tpc' jq' OK E1 E2 E3 E4. unfold A_mpi_div_mpi_C.DCS in *.
    repeat (apply Forall_cons_iff in OK; destruct OK as [?K OK]).
    unfold A_mpi_client2.chunk_okA in *. cbn [fst snd cells_size csize Nat.add] in *.
    repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; rewrite ?E1, ?E2, ?E3, ?E4; assumption|]). apply Forall_nil.
  Qed.
  #[using="Type"] Lemma uwc_raise_s : forall mx LO' TOP' vv F0' F1' dd, uwc asegs mx LO' TOP' vv F0' dd -> F1' + 16 <= vv -> uwc asegs mx LO' TOP' vv F1' dd.
  Proof.
    intros mx LO' TOP' vv F0' F1' dd HU HF. inversion HU; subst; [apply uwc_stop; assumption| eapply uwc_link; eassumption| apply uwc_cap; assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L26496199141.3L55454580985.9L62037211595.7L8931608776.1 L9366540546.1000000<00V01101601]S2sp3sp13SP1S1R3HIA1h3sp11a1b2HB2a02HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACP". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO SP1"] Lemma uwcd_store : forall mq m2 a b, UWCD mq -> munch [(a, b)] mq m2 -> b <= sp1 + 184 -> UWCD m2.
  Proof.
    intros mq m2 a b UW MU HB. rt_facts.
    eapply uwc_floor with (F := sp1 + 184); [| clear; lia].
    eapply uwc_munch; [eapply uwc_raise_s; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
    intros a0 Ha. cbn [outside]. split; [clear - Ha HB; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Notation T2C t2pad := [C8 (Z_to_bv 64 (FB + 128)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 3); C4 t2pad].

  (* [comment removed for export] *)
  Definition dv_MAIN_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 t2pad gb u0 u1 u2 jq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 (T2C t2pad) gb u0 u1 u2 jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB -> mpd_abs dB <= mpd_abs dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f404) fc None mq (seg_rom asegs)).

  #[using="Type"] Lemma lval_abs : forall e, Z.of_nat (length (md_limbs e)) = md_n e -> lval (md_limbs e) (md_n e) = mpd_abs e.
  Proof. intros e LEN. unfold lval, mpd_abs. rewrite <- LEN, Nat2Z.id, firstn_all. reflexivity. Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@D35300034347.191D35300034347.192D60189065437.191D60189065437.192L10907031934.3  L11144352574.3  L2151281629.4   L25949580181.3  L26988105723.2  L27601760898.4  L28632618922.2  L28814043710.211L29155856809.3  L32156412573.3  L32954672833.212L32954672962.211L35184871669.1  L35663928186.7  L36757749421.12 L37116549293.4  L38060875949.12 L39172636981.0  L42888674241.1  L44602390348.3  L44872450959.3  L48700858022.1  L49304025233.2  L49442955282.12 L52258283942.1  L53577728712.1  L57698627611.2  L60098763854.3  L66253710909.212L66253711294.211L66426995373.12 L67372926033.2  L9356559676.11  P28627113325.192P49296947798.192P57713046236.192P67365848726.192Q11968186855.192Q15022709143.188Q16827575549.192Q25954107624.192Q28465177121.189Q3375676648.192 Q3421936230.191 Q45057547415.192Q45987633792.188Q5265442331.190 Q57228775306.191Q58026207754.188Q58205651829.192Q60189065437.192Q67302478109.188Q68235297648.191Q68235297648.19200001<02H03T04`04h05405505>05H05S05T06<06E06H07H08H08K08`09I09R0:;0:<0:A0:B0:J0:O0:P0:U0:Z0:_0:`0:j0;j0<j0=S0=T0>?0?C0@G0A10B50C90CT0CU0CV0Co0D00D]0D^0E60EP0F:0FR0FS0GP0Gk0HN0I1S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS1i1j2K1S2sp3sp13SP1FS2dA1i2I1S3sp14gapnS1i1j2K02K1FS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn3ARvS2dA2dB1KS1iS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1j3SPR2F04SP1R2J13ARv3BRv2NBS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1j3SPR2F04SP1R2J13ARv3BRv2NBS1iS1R3HIA1h2sp2lo3TOP1HS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2dA2dB1iS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1SS3sp1FS1i1j2K0S3sp1FS3sp1S3sp1S3sp1FS1R2lo3LOSS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1i3SPR2F04SP1R2I13ARv2NA3BRvS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn1i3SPR2F04SP1R2I13ARv2NA3BRvS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF2sp3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1FFS2LF3LFB3sp14gapn4SP1R2HBFS2LF2sp2lo3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stFS2LF2lo3LFB3sp14gapn3LOCS2LF3LFB3sp14gapn2HB5Ha_stS2LF2lo3LFB2FB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1S2LF3LFB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE BE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR"] Lemma dv_DISPATCH : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c104 c120 c128 c136 t2pad gb u0 u1 u2 jq (i j : Z)
      xra t0 a1 a4 a6 a7 t5 t6,
    dv_MAIN_stmt ->
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 (Z_to_bv 64 X) (Z_to_bv 64 0) c104 (Z_to_bv 64 (FB + 96)) c120 c128 c136 (Z_to_bv 64 FB))
              (T2C t2pad) [] gb [C4 u0; C4 u1; C4 u2] jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 32 -> md_addr dY = FB + 64 -> md_addr dZ = sp1 + 168 -> md_addr dT = FB + 96 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB ->
    SIGF (md_limbs dA) (md_n dA) i -> SIGF (md_limbs dB) (md_n dB) j ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RG xra t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) (Z_to_bv 64 FB) a1 (Z_to_bv 64 j) SHB a4 (Z_to_bv 64 i) a6 a7 t5 t6)
          F (Z_to_bv 64 0x9f3f8) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros KMAIN CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 UW BPOS SX SY. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
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
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c128 c136 (T2C t2pad) gb u0 u1 u2 jq) DV_FSH 0 0).
    { eapply cs_store with (mq := mq) (a := sp1) (b := sp1 + 152); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM.
    dpose SX as (I1 & I2 & I3). dpose SY as (J1 & J2 & J3).
    pose proof (cs_opv_A _ _ _ _ _ _ _ CST2) as (CAv & OAv & ARv & A8v & EBA & LENA & NA & FAv & _).
    pose proof (cs_opv_B _ _ _ _ _ _ _ _ CST2) as (CBv & OBv & BRv & B8v & EBB & LENB & NB & FBv & _).
    rewrite <- AE in CAv, OAv, ARv, A8v. rewrite <- BE in CBv, OBv, BRv, B8v.
    assert (KM : lval (md_limbs dB) (md_n dB) <= lval (md_limbs dA) (md_n dA) -> forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7,
       aevtA asegs (KF asegs R HIA hq mo0) POSTD (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f404) fc None m2 (seg_rom asegs))).
    { intros LE; intros. rewrite (lval_abs dA LENA), (lval_abs dB LENB) in LE.
      eapply KMAIN; [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OX0| exact OY0| exact OZ0| exact OT0| exact UW2| exact BPOS| exact LE]. }
    assert (KE : lval (md_limbs dA) (md_n dA) < lval (md_limbs dB) (md_n dB) -> forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7,
       aevtA asegs (KF asegs R HIA hq mo0) POSTD (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t5 t6) F (Z_to_bv 64 0x9f5bc) fc None m2 (seg_rom asegs))).
    { intros _; intros.
      eapply dv_EARLY; [exact CST2| exact EAX| exact EAY| exact EAZ| exact EAD| exact OX0| exact OY0| exact OZ0| exact OT0| reflexivity| exact UW2| exact BPOS]. }
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - I1 J1 NA NB; lia).
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - I1 J1 NA NB; lia).
      + (* [comment removed for export] *)
        assert (j = i) as -> by (clear - K0 K1; lia).
        zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep. zstep.
        replace (Z_to_bv 64 (i * 4 + -4)) with (Z_to_bv 64 (4 * i - 4)) by (f_equal; clear; lia).
        eapply (dv_CMPLOOP (Z.to_nat i) hq m2 i i); try eassumption; first [clear - I1; lia| reflexivity| exact (proj2 NA)| exact (proj2 NB)| idtac].
      + apply KE. exact (SIGF_lt (md_limbs dB) (md_n dB) j (md_limbs dA) (md_n dA) i SY SX ltac:(clear - K1; lia)).
    - apply KM. pose proof (SIGF_lt (md_limbs dA) (md_n dA) i (md_limbs dB) (md_n dB) j SX SY ltac:(clear - K0; lia)) as K. clear - K. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac cb8_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L29784547046.108L35362536170.108L491026790.108  00000Y01B01mS2LF2ra2sp3LFB2FB3sp14gapn3shi2B01k2H22H0S2LF2ra2sp3LFB2FB3sp14gapn3shi2B01k2H22H0S1R2LF2ra2sp3LFB2FB3sp14gapn3shi2B01k2H22H0". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma aobj_of_sshad_s : forall (CSx : Z -> Prop) mX slo' shi B0 (k : nat),
    cs_ok AL CSx -> sshad asegs AL mX slo' shi -> slo' <= B0 -> B0 + 8 * Z.of_nat (S k) <= shi -> B0 mod 8 = 0 -> 0 <= B0 ->
    crange CSx B0 (8 * Z.of_nat (S k)) -> aobj asegs AL CSx mX B0 (8 * Z.of_nat (S k)).
  Proof.
    intros CSx mX slo' shi B0 k OK SS H1 H2 HB H0 HC.
    pose proof (sshad_chunk asegs AL mX slo' shi k B0 SS H1 H2 HB) as SH.
    replace (shadow_of AL B0) with (Z.shiftr B0 3 + al_sb AL) in SH by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
    eapply (aobj_of_zero_shadow_sh asegs AL CSx mX B0 (zcells (S k)) B0 0 (S k) OK SH HC HB H0 ltac:(lia)).
    intros i Hi. apply cell_at_zcells. exact Hi.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Variables (slo : Z).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO2 : slo <= lo.
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis OXs0 : aobj asegs AL CS m (md_addr dX) 16.
  Hypothesis ESM : Forall (fun e => mpd_at asegs m LB e /\ aobj asegs AL CS m (md_addr e) 16) es.
  Hypothesis SSH0 : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis MI0 : mem_inv asegs m.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L14714406535.1L31034375991.6L31102187327.1L50790580594.600000300F00I00`S1eS1R3HIA1h2sp3TOP2HTS1eS1R5NEEDR2sp2lo3LOS3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO TOP H0M XW ESF SLO1 MX0 OXs0 ESM SSH0 MI0"] Lemma dv_TR : forall (h1 : HST asegs R HIA) m1, hcs asegs R HIA h1 = CS -> mem_inv asegs m1 ->
    presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [] m m1 ->
    (mpd_at asegs m1 LB dX /\ aobj asegs AL (hcs asegs R HIA h1) m1 (md_addr dX) 16)
    /\ Forall (fun e => mpd_at asegs m1 LB e /\ aobj asegs AL (hcs asegs R HIA h1) m1 (md_addr e) 16) es
    /\ sshad asegs AL m1 slo (bv_unsigned sp).
  Proof.
    intros h1 m1 Ehcs MI1 HP01. rt_facts.
    assert (TR : forall e, mpd_at asegs m LB e -> aobj asegs AL CS m (md_addr e) 16 -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr e) 16 ->
                 mpd_at asegs m1 LB e /\ aobj asegs AL (hcs asegs R HIA h1) m1 (md_addr e) 16).
    { intros e ME OE CRE. rewrite Ehcs. split.
      - eapply (mpd_at_heap_presx asegs L) with (LBp := LB ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
          [exact ME| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI0| exact MI1| exact CRE| | exact I| intros _; exact I| intros b Hb; destruct (mpd_blk_heap _ _ Hb) as [O ->]; exact (proj1 (A_mpi_client2.mpd_heap_in asegs _ _ _ ME O))].
        intros O. destruct (A_mpi_client2.mpd_heap_in asegs _ _ _ ME O) as [IN N1]. eapply client_range_block; [apply in_app_iff; left; exact IN| clear; lia| clear; lia].
      - eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OE| exact CRE| clear - LOS SLO NEEDR; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    assert (XCR : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dX) 16).
    { destruct XW as [CW _]. intros x Hx. destruct (CW x Hx) as [K|[K|K]]; [left; exact (proj1 K)| right; left; exact K| right; right; exact K]. }
    split; [exact (TR dX MX0 OXs0 XCR)|]. split.
    - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) ESM e He) as [ME OE].
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & _ & ASE & _).
      apply (TR e ME OE). eapply client_range_raise; [exact CRE| exact ASE].
    - eapply (presA_sshad asegs R); [exact HP01| exact SSH0| exact SLO1|].
      pose proof (hm_top asegs R HIA h LB LF m H0M) as HT. clear - HT TOP. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L34106173077.2L4363196017.2 L54736999191.3L6618771420.3 00000700>00E00LS2A02HAS2A02HAS2mx2A0S2mx2A0". (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_nil_s : forall mx A0, 0 <= A0 <= 2^64 -> rw_cells asegs mx A0 [].
  Proof.
    intros mx A0 HA. unfold rw_cells, cells_at, bytes_at, wr_at. cbn [cells_bytes cells_size length cells_wf Z.of_nat].
    repeat split; try (clear - HA; lia); intros i Hi; exfalso; clear - Hi; cbn in Hi; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06C0@D1017889312.242 D11138851872.242D1162412691.242 D12596279903.242D17183699282.242D27336594514.244D29720839482.242D29720839482.244D30256622227.242D3349449248.242 D37734952083.242D37894705033.244D39565106411.241D39565106411.242D43080244883.242D48084872841.242D49412573216.242D53578774111.242D58165489299.242D60189065437.241D60189065437.242D62011970312.242D64280614944.242D67430489183.242D8640742547.242 D8792611872.242 L10569128703.2  L10743610235.12 L10982838897.10 L11879002598.1  L13157033923.1  L14424556008.1  L14447004729.1  L14447004729.2  L15791392034.10 L15822417165.1  L15824827452.2  L16684788220.4  L16697175330.10 L1685717371.0   L16900494803.12 L17092503979.1  L17220136577.2  L17507800040.1  L17743130737.10 L1792017228.12  L1792017228.13  L18351345279.1  L18351345279.2  L1865578451.12  L18881200083.12 L19614928416.43 L19614928416.44 L19954847564.12 L19954847564.13 L1998609380.12  L20624505793.2  L20803010848.12 L21407994921.0  L2149059419.2   L21653069077.243L21772258342.1  L21866712442.1  L21868500043.2  L22937440672.1  L22939159100.2  L22941438733.1  L23459141290.260L23461302312.258L23513658539.2  L24257721380.12 L2458215594.4   L25190023391.235L25204003039.235L25257820271.237L25333246874.235L2545017055.235 L25539268895.12 L25722247176.12 L26496199141.3  L26529568682.2  L26530157006.235L26700538540.12 L26892418956.1  L27019463589.2  L27817938348.241L2803942888.1   L28632618922.2  L28811875202.260L29093793529.10 L29532535949.3  L30399176481.0  L31145622673.2  L32195670001.261L32269442061.5  L32354394574.235L32454903270.1  L32596543859.5  L32716226850.10 L33595343993.6  L33695580575.12 L33695580575.13 L33970682146.10 L33982705724.2  L33985112333.1  L34590671346.13 L34915349256.1  L35161918279.2  L35663928186.7  L36191212873.183L36191408060.186L36332261457.1  L372066202.235  L38259954321.2  L3835339001.10  L3862499300.12  L38636143827.12 L38919470161.1  L3909764896.12  L39172636981.0  L39513730120.1  L39759912248.5  L40066129279.1  L40066129279.2  L40201237073.1  L40281191306.3  L40604528339.12 L40853807686.2  L40855808609.3  L41096910396.2  L41099742989.1  L41663468825.235L42091889404.6  L42194629587.12 L42326616548.12 L43677542767.234L43677759120.237L44107246460.235L44196099187.263L44283392864.12 L44602462076.2  L45223603532.12 L45223603532.13 L45305596371.12 L45440926951.12 L46148236401.10 L46238398351.237L46655470320.237L46839732335.235L46957106919.12 L47277099470.235L48161827075.1  L48307978015.12 L48700858022.1  L48825353400.1  L49118974339.4  L49304025233.2  L4993987500.12  L50548354875.12 L50794195360.5  L51005809078.7  L51977863340.12 L52051607036.2  L52054009037.1  L52258283942.1  L52357278375.6  L52649141796.12 L53530622874.235L53772548128.2  L53776234111.3  L53897481834.3  L54388190457.10 L54513076772.12 L54532887840.12 L55060699367.12 L55565403447.2  L55565452218.3  L55879915635.5  L55884196193.12 L55990716303.235L56386624752.235L56418360977.2  L56523586534.1  L57588980433.2  L576250137.235  L57698627611.2  L58012725026.10 L58127621921.0  L59308586248.2  L59308628820.4  L59314923118.4  L60098763854.3  L60156137250.10 L61366595865.235L61968151637.1  L62018535662.1  L62037211595.7  L62340157907.12 L62564602536.2  L63104194423.2  L64345861656.3  L64850595401.0  L66038874368.2  L66151427842.16 L66151427842.17 L66925225621.242L67028678867.12 L67372926033.2  L67806095031.9  L67883417576.3  L68664817267.5  L6961803708.6   L7735748552.2   L7738195705.2   L7964892447.12  L8004647292.237 L881835912.0    L8931608776.1   L8932519465.186 L9356559676.11  L9373133312.2   P14461423358.242P15835051771.242P15835051771.244P18341645496.242P21870859916.242P21870859916.244P22945712379.242P22945712379.244P23511823980.243P26535597421.242P28627113325.241P28627113325.242P31146933846.241P31146933846.242P33980871419.242P33980871419.244P38261788758.241P38261788758.242P40077402040.242P41095599355.242P41095599355.244P49296947798.241P49296947798.242P52049772347.242P52049772347.244P53787491047.243P53787491047.245P56407612502.241P56407612502.242P57713046236.241P57713046236.242P67365848726.241P67365848726.242P7750690063.242 P7750690063.244 Q10592467228.241Q10592581176.238Q10752139055.242Q1107808484.241 Q1109727972.242 Q11233448396.189Q11707909693.238Q1173713739.264 Q1343606420.238 Q14273469813.241Q15673813033.238Q16603059094.242Q16623688748.238Q17000624785.242Q17002805393.241Q17064467242.238Q17356042893.261Q17757173815.239Q18397797912.241Q18524760367.242Q19056309629.241Q19546702550.241Q19561563759.243Q19561564143.242Q20013594135.239Q20131870581.242Q21042218976.265Q21538057956.241Q21540267236.242Q21883652981.244Q21885665653.243Q22137999078.243Q22712450012.242Q22712450012.244Q23022710355.264Q2303095517.189 Q2303323684.190 Q2303602470.187 Q24064611734.242Q24471895157.239Q25511591557.242Q25511591557.244Q25513505925.241Q25513505925.243Q26130604464.241Q26132851632.242Q28096376349.238Q28465177121.239Q28465177121.240Q30802955094.239Q31289377519.265Q31954582050.265Q34069183529.265Q3419689062.241 Q3419689062.242 Q3421936230.241 Q3421936230.242 Q34330878721.190Q34671241765.242Q34673583276.238Q37325288593.242Q37327240849.241Q37708009648.265Q37710326028.264Q38272766294.239Q38853616431.242Q39033705737.238Q39085863854.239Q39180574961.241Q39180574961.242Q39212284437.190Q39212284437.241Q39402408740.266Q40701482540.238Q44583781046.242Q44992639511.238Q45124942924.265Q46491644298.238Q46632019970.187Q477629637.190  Q47860023380.267Q48117823211.242Q49249246894.241Q49413559012.241Q49415575780.242Q49473087645.238Q49698585326.240Q49698585326.242Q50845955027.267Q51003550464.238Q52017298816.238Q522453693.238  Q5265442331.240 Q5265442331.241 Q52744951088.241Q52747231024.242Q55415036769.241Q55415036769.242Q5652373087.241 Q5694720405.240 Q57031356183.240Q57228775306.241Q57228775306.242Q57230951818.241Q57230951818.242Q58230639221.244Q58368740407.239Q58694915926.239Q58746442149.243Q58748228923.238Q58985395338.240Q59321350679.241Q59321350679.242Q59321350679.244Q60085152698.238Q60133849205.241Q60136059509.242Q60511567613.190Q60511567613.241Q61917260245.266Q61917304426.267Q63043846664.240Q6329277366.244 Q63396246492.267Q63566450772.261Q63566501214.238Q63566565718.241Q64054320522.239Q64231755440.244Q64233669808.243Q64765693112.238Q64908775830.242Q65424847505.241Q65426765969.242Q65903933766.266Q7757652326.242 Q7845954958.241 Q7845954958.242 Q7845954958.244 Q9072980029.238 Q9380753577.238 Q9538787269.187 Q9538802383.238 Q9634016784.242 Q9634017168.243 Q9644649257.241 Q9961343543.239 00000100a01Q02A03\05706R07m07n07o08009K0:f0<C0=30>N0?>0?n0@^0B90CV0DH0E80Eh0Ei0Ej0En0FV0G90G=0GA0GE0GJ0GK0GO0GS0GT0Ge0Gi0Gj0HR0HV0HW0H[0I>0I?0I@0IE0IF0In0JV0JW0JX0JY0JZ0Jc0Jg0KG0KH0KP0L10L50L90L:0L?0L@0LD0Lk0MR0MS0M\0Mm0NN0No0OP0P10PR0Q:0Qb0Qn0Qo0RP0RZ0R^0Re0SF0SJ0SK0T30TV0T`0Ta0Tb0UF0UW0V80V<0VM0VQ0VR0VS0VT0VX0VY0V]0WL0WM0WT0Wi0XS0Y=0YA0Yb0Yc0ZF0ZO0[70[;0[[0[\0[]0\20\70\80\<0\E0\m0\n0]80]90]=0]^0]_0^G0^P0_50_Z0`;0`_0`i0a00a10a20aZ0ac0bF0bg0cH0ci0d20dS0dW0e?0eD0eH0eW0eX0eb0fJ0f[0g60g@0gA0gE0gJ0g]0gf0hG0hH0hI0hS0i60i?0i_0ih0ii0j30jD0jU0k60kW0kX0k\0k`0lA0lB0lF0lG0lM0lZ0le0lo0m30mT0mX0m[0n60n^0nb0ni0o50o60o@0oc0od10E10m10n11R11^11o12012112212Z13;13<13A14@14k1551661771881991::1;;1<<1==1=>1=?1>@1?C1@D1AG1BH1CI1DJ1EM1FN1GO1HP1IQ1JT1KU1LV1LW1LX1MY1N\1OF1P51Q61R91S:1Sg1T:1TM1TN1U01UR1Uk1V>1VS1Vn1WJ1W]1W^1X11XS1Y51YH1Y]1Z61ZL1ZM1Z_1[K1\71\c1]A1^B1^C1^e1_G1`11`[1`n1aX1bE1bZ1c31cL1ce1cf1dB1do1e_1fL1g<1gf1hP1hn1iJ1if1j?1j@1jU1jV1kC1l51lg1mT1mm1n@1nS1o51oW1ol20A20Z20[21921U22V23\24524G24\24o26026K27G27e28>28[29029l2:H2:j2;L2;j2<J2<g2=_2>:2>U2>h2?E2?b2@D2@f2AP2B?2BR2C02CK2D:2Dd2EN2F=2GA2GZ2H32HF2HY2I72I82I92I:2IL2J62J`2K72KG2K\2L12LL2MM2MN2Mc2N52NG2Nb2OO2P<2PO2PP2Q22QT2Qi2R<2Rb2SJ2T02TC2TV2Tm2U=2US2Ui2V?2VXFS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A1B3TOP3LFB2dB2FB3sp14gapn3GAP2h13ET13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A1B3TOP3LFB2dB2FB3sp14gapn3GAP2h13ET13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stFFFS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1A1B3TOP3LFB2dB2FB3sp14gapn3GAP2h13ET13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp1X1A1B3TOP3LFB2dB2FB3sp14gapn3GAP2h13ET13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1X1A1B2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13SPR2F04SP1R3BRv3ARv2HB5Ha_st5Hl_stS1R2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stFFS2dBS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOS2FBS2FBS2FBS3sp1FS2FBS2FBFS2sp3sp14gapn3GAPS2FBSS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2FBFS2FBS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOFFS3sp1FS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOFFFFS2FB4gapnS2dBS1R5NEEDR2sp2lo3SLO2FB4gapn4FBLOSS2dB3NB3S2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2dAS2FBFS3sp1FS2FBS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn2NAS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn2NAFS2FB4gapnS2sp3sp14gapn3GAPS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2sp3sp13SP1FS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS3sp14gapnS2spS2dA2NAS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2FBFS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn3ARvS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOS2dA2NA2KNSFS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapnS2sp3sp14gapn3SP1S2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2FBS2sp3sp14gapn3SP1S2FBFFFS2FBFS2FBS1R3HIA5NEEDR1h2sp2lo3SLO2FB3sp13SP14FBLO2a02HaFS2dA2NAS1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp1B3LFB2dB2FB3sp14gapn2sl3LSL3BRvS2LF2ra2sp1B3LFB2dB2FB3sp14gapn2sl3LSL3BRvS2FBS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnFS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOS2FB4gapnS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2FBS1R5NEEDR2sp2lo3SLO2FB4gapn4FBLOSFS2sp3sp13SP13SPR4SP1RS3sp1FS2FBS1R3HIA1hS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOFS2dB2r'2HRFS2FBS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnFS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2FB4gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn3ARvS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn3ARvS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapnS3sp14gapnS2dA2NAFFS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2FB4gapnS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2FB4gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2FBS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS3sp1S2dBS2sp2lo3sp13SP1FS3sp14gapnS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2sp3sp14gapn3SP1S1R5NEEDR2sp2lo3SLO3sp13SP1S3sp14gapnFS2FBS3sp1S1R3HIA1h3sp12a02HaS2FB4gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnFFS2dB2r'2HRS1R5NEEDR2sp2lo3SLO2FB3sp13SP14FBLOS2FB4gapnS1R5NEEDR2sp2lo3SLO2FB4gapn4FBLOS2FB4gapnFS2dA2NA2KNS2sp3sp14gapn3SP1S2sp3sp14gapn3SP1S2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnFS2FBS2dAS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnFS2FBSS1i2HiS2dB2r'2HR2K5S2dX2dA1E1KS1R2lo3LOSS2FBS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS2FBS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2dAS2dA2KNS2sp3sp13SP1SS3sp14SP1RS3sp12r04SP1M1q1r1H2H02q02H42FB3FB8FS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOFS1R5NEEDR2sp2lo3SLO3sp13SP13slo4SLO2S2sp3sp13SP1S2sp3sp14gapn3GAPFFFS1R5NEEDR2sp2lo3SLO2FB3sp14gapn3SP14FBLOS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapnSS3sp1S2LF2ra2sp1B3LFB2dB2FB3sp14gapn2r'2sl3LSL2HR3SPR2F04SP1R3BRv2NBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1RS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stFFS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stFFS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS2LF2sp3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp1X3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_st2FBS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3SLO3LFB2dB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2dB2FB4gapn4FBLO2HB5Ha_st5Hl_st3sp13SP1S2LF2sp3LFB2dB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapnFS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF1B3LFB2dB4gapn2sl3LSLS2LF3LFB2dB2FB4gapnS2LF1A3LFB2dA2dB4gapnS2LF2lo3LFB2dB3sp14gapn3LOCS2LF3LFB2dB3sp14gapn4SP1R2HBS2LF3LFB2dB2FB4gapnFS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapnS2LF1A3LFB2dA2dB4gapnS2LF3LFB2dB2FB4gapn2F02HBS2LF1A3LFB2dB4gapn3ARvFS2LF1A3LFB2dB4gapnS2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn3FB83SPR2F0S2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn3FB83SPR2F0S2LF2ra2sp1A1B3LFB2dB2FB3sp14gapn3FB83SPR2F0S2LF2sp2lo3LFB2dB3sp14gapn3SP1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stFS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapnS2LF2sp3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp3LFB2dB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF1A3LFB2dA2dB4gapnS2LF1B3LFB2dB4gapn2sl3LSLS2LF1B3LFB2dB4gapn2sl3LSLS2LF1B3LFB2dB4gapn2sl3LSLFS2LF3LFB2dB3sp14gapn4SP1R2HBS2LF2sp2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dB3sp14gapn3SP1S2LF3LFB2dB3sp14gapn4SP1R2HBS2LF3LFB2dB3sp14gapn4SP1R2HBS2LF3LFB2dB2FB4gapn2F02HBFS2LF1A3LFB2dA2dB4gapnFS2LF2sp2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp1X2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_st2FBS2LF2sp1X2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_st2FBS2LF2sp2lo3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF1B3LFB2dB4gapn2sl3LSLS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF1A3LFB2dA2dB4gapnS2LF1A3LFB2dA2dB4gapnS2LF3LFB2dB2FB4gapn2F02HBFS2LF2sp2lo3LFB2dB3sp14gapn3SP1S2LF3LFB2dB3sp14gapn4SP1R2HBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1X2lo3LOS3SLO3LFB2dB3sp14gapn3SP13ALO2HB5Ha_st5Hl_st2FBS2LF1B3LFB2dB4gapn2sl3LSLS2LF1A3LFB2dB4gapnS2LF1B3LFB2dA2dB4gapnS2LF3LFB2dB2FB4gapnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOCS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn3SPR2F04SP1R3BRv3ARv3A8vS2LF2sp2lo3LFB2dB3sp14gapn3SP1S2LF1B3LFB2dB4gapn2sl3LSLS2LF1B3LFB2dB4gapn2sl3LSL3BRvS2LF1B3LFB2dA2dB4gapnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB2FB4gapn3ALO2HB5Ha_st5Hl_stS2LF3LFB2dB3sp14gapn4SP1R2HBS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dB3sp14gapn3SP1S2LF3LFB2dB2FB4gapn2HB5Ha_st3sp1S2LF3LFB2dB3sp14gapn2HB5Ha_stS2LF2ra2sp1A1B3LFB2dA2dB2FB3sp14gapn3SPR2F04SP1R3BRv3B8vS2LF2lo3LFB2dB3sp14gapn3LOCS2LF2lo3LFB2dB3sp14gapn3LOCS2LF3LFB2dB2FB4gapnS2LF3LFB2dB3sp14gapn2HB5Ha_stS2LF3LFB2dB3sp14gapn2HB5Ha_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF2sp3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp1X3LFB2dB3sp14gapn3SP12HB5Ha_st5Hl_st2FBS2LF3LFB2dB2FB4gapnS2LF2sp2lo3LFB2dB3sp14gapn3SP1S2LF2lo3LFB2dB3sp14gapn3LOCS2LF1X2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_st2FBS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF1X2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_st2FBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB2FB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2F02HBS2LF3LFB2dB2FB4gapn2F02HBS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapnS2LF2sp2lo3LFB2dB3sp14gapn3SP1FFFS2LF1A3LFB2dB4gapnS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF3LFB2dB4gapn2sl3LSLS2LF3LFB2dB4gapnS2LF1B3LFB2dA2dB4gapnS2LF1B3LFB2dA2dB4gapnS2LF2lo3LFB2dB3sp14gapn3LOCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stFS2LF1A3LFB2dA2dB4gapnS2LF1A3LFB2dB4gapnS2LF1A3LFB2dB4gapnS2LF2lo3LFB2dB3sp14gapn3LOCS2LF2lo3LFB2dB2FB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dB2FB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapnFS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapn2HB5Ha_st5Hl_stS2LF1B3LFB2dA2dB4gapnS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF1X3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF3LFB2dB2FB4gapnS2LF3LFB2dB2FB4gapnS2LF3LFB2dB4gapn2sl3LSLS2LF3LFB2dB4gapnS2LF3LFB2dB2FB4gapn2F0S2LF3LFB2dB2FB4gapn2F0S2LF3LFB2dB2FB4gapn2F0S2LF3LFB2dB2FB4gapn2F02HB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE BE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR slo SLO1 SLO2 MX0 OXs0 ESM SSH0 MI0"] Lemma dv_INIT : forall (h1 : HST asegs R HIA) (m2 : mem) (r' : Z) (jx jy jt jp jq : list byte) (sl : list word)
      xra t0 a1 a6 a7 t3 t4 t5 t6,
    dv_MAIN_stmt ->
    HM asegs R HIA h1 LB LF1 m2 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h ->
    havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    rw_cells asegs m2 FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs m2 (FB + 32) [CB 16 jx] -> rw_cells asegs m2 (FB + 64) [CB 16 jy] -> rw_cells asegs m2 (FB + 96) [CB 16 jt] ->
    rw_cells asegs m2 (FB + 128) [CB 12 jp; CB 4 jq] ->
    rw_cells asegs m2 (Z.shiftr FB 3 + al_sb AL) DV_FSH ->
    rw_cells asegs m2 (bv_unsigned sp + -104) SAVEL ->
    rw_cells asegs m2 sp1 (map C8 sl) -> length sl = 23%nat -> nth 18 sl (Z_to_bv 64 0) = Z_to_bv 64 FB ->
    stk asegs m2 (sp1 + 184) (bv_unsigned sp + -104) -> stk asegs m2 lo sp1 -> mem_inv asegs m2 ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m2 ->
    mpd_at asegs m2 LB dX -> aobj asegs AL (hcs asegs R HIA h1) m2 (md_addr dX) 16 ->
    Forall (fun e => mpd_at asegs m2 LB e /\ aobj asegs AL (hcs asegs R HIA h1) m2 (md_addr e) 16) es ->
    UWCD m2 ->
    1 <= r' <= md_n dB -> 0 < mpd_abs dB ->
    aevtA asegs (KF asegs R HIA h1 mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 (Z_to_bv 64 (md_n dB)) SHB
               (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 r') a6 a7
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 B)
               (Z_to_bv 64 (-12)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f2b8) fc None m2 (seg_rom asegs)).
  Proof.
    intros until t6. intros KMAIN HH1 Ehcs ET1 ES1 EF1 EV1 EFR1 FHD XC YC TC TPC FSH SAVE SPILL LSL S144 SThi STlo MI2 PRES MX2 OX2 EXT2 UW HR BPOS.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    ddestruct (frame_factsA R HIA CS h1 LB LF m2 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (_ & _ & _ & _ & _ & _ & _ & FBLO & SBND & APS).
    change (256 / 8) with 32 in SBND, APS. unfold DV_FSH in FSH. cbn [zcells app] in FSH.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (hcs_stack asegs R HIA h1) as SCS01.
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| rewrite ES1; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (rewrite <- Ehcs; exact SCS1).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 256) by (rewrite Ehcs; exact CFB).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) EXT2 dB ESB) as [MB2 OB2].
    dpose (opv_of_mpd h1 LB LF1 m2 dB HH1 MB2 OB2 IB2) as (CBv & OBv & BRv & B8v & EBB & LENB & NB & FBv & SGB).
    rewrite <- BE in CBv, OBv, BRv, B8v. unfold mpi_cells in CBv.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OBv (B + 8) 2.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by (clear - HR NB; lia); [exfalso; clear - K5 HR; lia|].
    zstep. if_cases KS; zify_cond KS; [| exfalso; destruct SGB as [SGB|SGB]; rewrite SGB in KS; vm_compute in KS; discriminate KS].
    (* [comment removed for export] *)
    destruct sl as [|k0 sl]; [discriminate LSL|]. destruct sl as [|k1 sl]; [discriminate LSL|]. destruct sl as [|k2 sl]; [discriminate LSL|]. destruct sl as [|k3 sl]; [discriminate LSL|]. destruct sl as [|k4 sl]; [discriminate LSL|]. destruct sl as [|k5 sl]; [discriminate LSL|]. destruct sl as [|k6 sl]; [discriminate LSL|]. destruct sl as [|k7 sl]; [discriminate LSL|]. destruct sl as [|k8 sl]; [discriminate LSL|]. destruct sl as [|k9 sl]; [discriminate LSL|]. destruct sl as [|k10 sl]; [discriminate LSL|]. destruct sl as [|k11 sl]; [discriminate LSL|]. destruct sl as [|k12 sl]; [discriminate LSL|]. destruct sl as [|k13 sl]; [discriminate LSL|]. destruct sl as [|k14 sl]; [discriminate LSL|]. destruct sl as [|k15 sl]; [discriminate LSL|]. destruct sl as [|k16 sl]; [discriminate LSL|]. destruct sl as [|k17 sl]; [discriminate LSL|]. destruct sl as [|k18 sl]; [discriminate LSL|]. destruct sl as [|k19 sl]; [discriminate LSL|]. destruct sl as [|k20 sl]; [discriminate LSL|]. destruct sl as [|k21 sl]; [discriminate LSL|]. destruct sl as [|k22 sl]; [discriminate LSL|]. 
    destruct sl; [| discriminate LSL]. cbn [map] in SPILL. cbn [nth] in S144. subst k18. clear LSL.
    chunk_split SPILL 19%nat SPLO SPHI.
    apply rw_cells_CB_of in SPHI; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in SPHI.
    lazymatch type of SPHI with rw_cells _ _ _ [CB 32 ?j] => set (jh := j) in SPHI; clearbody jh end.
    apply (rw_cells_split_CB asegs m2 _ [] 32 _ [] [8; 4; 4; 8; 4; 4]%nat) in SPHI; [| reflexivity]. cbn [mk_CB_cells app] in SPHI. cb8_all SPHI.
    lazymatch type of SPHI with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c; C8 ?d; CB 4 ?e; CB 4 ?f] =>
      set (h0 := a) in SPHI; set (h1b := b) in SPHI; set (t2pad := c) in SPHI; set (h3 := d) in SPHI; set (h4 := e) in SPHI; set (zpad := f) in SPHI; clearbody h0 h1b t2pad h3 h4 zpad end.
    chunk_split SPHI 3%nat T2R ZR. replace (sp1 + 152 + 16) with (sp1 + 168) in ZR by (clear; lia).
    apply (rw_cells_split_CB asegs m2 _ [] 16 jx [] [8; 4; 4]%nat) in XC; [| reflexivity]. cbn [mk_CB_cells app] in XC. cb8_all XC.
    lazymatch type of XC with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c] => set (xp0 := a) in XC; set (xs0 := b) in XC; set (xpad := c) in XC; clearbody xp0 xs0 xpad end.
    apply (rw_cells_split_CB asegs m2 _ [] 16 jy [] [8; 4; 4]%nat) in YC; [| reflexivity]. cbn [mk_CB_cells app] in YC. cb8_all YC.
    lazymatch type of YC with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c] => set (yp0 := a) in YC; set (ys0 := b) in YC; set (ypad := c) in YC; clearbody yp0 ys0 ypad end.
    apply (rw_cells_split_CB asegs m2 _ [] 16 jt [] [8; 4; 4]%nat) in TC; [| reflexivity]. cbn [mk_CB_cells app] in TC. cb8_all TC.
    lazymatch type of TC with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c] => set (tp0 := a) in TC; set (ts0 := b) in TC; set (tpad := c) in TC; clearbody tp0 ts0 tpad end.
    apply (rw_cells_split_CB asegs m2 _ [] 12 jp [CB 4 jq] [4; 4; 4]%nat) in TPC; [| reflexivity]. cbn [mk_CB_cells app] in TPC.
    lazymatch type of TPC with rw_cells _ _ _ [CB 4 ?a; CB 4 ?b; CB 4 ?c; CB 4 jq] => set (ub0 := a) in TPC; set (ub1 := b) in TPC; set (ub2 := c) in TPC; clearbody ub0 ub1 ub2 end.
    apply (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m2 _ [] ub0 _) in TPC. cbn [app] in TPC.
    apply (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m2 _ [C4 (le_bytes_to_word ub0)] ub1 _) in TPC. cbn [app] in TPC.
    apply (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m2 _ [C4 (le_bytes_to_word ub0); C4 (le_bytes_to_word ub1)] ub2 _) in TPC. cbn [app] in TPC.
    chunk_split TPC 3%nat TPC3 JQC. replace (FB + 128 + 12) with (FB + 140) in JQC by (clear; lia).
    assert (IND : In (FB + 32, 216) (LB ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWX : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 32) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWY : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 64) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWT : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 96) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (AV : opv h1 m2 dA).
    { destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
      - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]).
        rewrite EQA. eapply opv_of_mpd; [exact HH1| exact MX2| exact OX2| intros EO; exfalso; exact (NST EO)].
      - pose proof (proj1 (Forall_forall _ _) EXT2 dA (ESA NE)) as [MA2 OA2']. eapply opv_of_mpd; [exact HH1| exact MA2| exact OA2'| exact IA2]. }
    ddestruct AV as (CAv & OAv & ARv & A8v & _). rewrite <- AE in CAv, OAv, ARv, A8v. clear CAv.
    clear MU WM.
    pose proof (munch_refl [(sp1, sp1 + 184); (FB + 32, FB + 112)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    do 15 zstep.
    (* [comment removed for export] *)
    lazymatch goal with OAc : aobj asegs AL (hcs asegs R HIA h1) _ A 16 |- _ => shadow_chk OAc (A + 10) 2 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA h1 LB LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : stk asegs m3 (sp1 + 184) _ |- _ => rename H into SThi3 end.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HP01.
    ddestruct (dv_TR h1 m3 Ehcs MI3 HP01) as ([MX3 OX3] & EXT3 & SSH3).
    assert (UW3 : UWCD m3).
    { eapply uwc_floor with (F := sp1 + 184); [| clear; lia].
      eapply uwc_munch; [eapply uwc_raise_s; [exact UW| clear - SP1; lia]| exact MU| clear - SP1R; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a0 Ha. cbn [outside]. split; [clear - Ha; lia| split; [clear - Ha FBLO SLO SP1 NEEDR; lia| exact I]]. }
    clear MU WM MX2 OX2 EXT2 UW.
    (* [comment removed for export] *)
    assert (E16 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16) = Z_to_bv 64 0) by (rewrite unsigned_lit by (clear; lia); reflexivity).
    pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ XC) as XC2. cbn [app] in XC2. rewrite E16 in XC2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 0)] xpad [] XC2) as XC3. cbn [app] in XC3.
    pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ YC) as YC2. cbn [app] in YC2. rewrite E16 in YC2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 0)] ypad [] YC2) as YC3. cbn [app] in YC3.
    pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ TC) as TC2. cbn [app] in TC2. rewrite E16 in TC2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 0)] tpad [] TC2) as TC3. cbn [app] in TC3.
    pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ ZR) as ZR2. cbn [app] in ZR2. rewrite E16 in ZR2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 0)] zpad [] ZR2) as ZR3. cbn [app] in ZR3.
    assert (T2R3 : rw_cells asegs m3 (sp1 + 152) (T2C (le_bytes_to_word t2pad))).
    { pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 (FB + 128))] (Z_to_bv 64 196609) _ T2R) as T22. cbn [app] in T22.
      pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 (FB + 128)); C2 (Z_to_bv 64 196609); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 196609) / 2 ^ 16))] t2pad [] T22) as T23. cbn [app] in T23.
      assert (E2 : le2 (Z_to_bv 64 196609) = le2 (Z_to_bv 64 1)) by (rewrite !le2_of_Z; rewrite <- (CellsX.Z_to_le_bytes_mod 2 196609); reflexivity).
      assert (E3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 196609) / 2 ^ 16) = Z_to_bv 64 3) by (rewrite unsigned_lit by (clear; lia); reflexivity).
      rewrite E3 in T23.
      eapply rw_cells_reshape; [exact T23| |].
      - cbn -[le2 le4 le8]. repeat split; try (rewrite ?length_le2, ?length_le4, ?length_le8; reflexivity).
      - cbn -[le2 le4 le8]. rewrite E2. reflexivity. }
    clear XC XC2 YC YC2 TC TC2 ZR ZR2 T2R.
    (* [comment removed for export] *)
    frame_aobj FSH (FB + 32) 2%nat as OXL. frame_aobj FSH (FB + 64) 2%nat as OYL. frame_aobj FSH (FB + 96) 2%nat as OTL.
    assert (OZL : aobj asegs AL (hcs asegs R HIA h1) m3 (sp1 + 168) 16).
    { apply (aobj_of_sshad_s (hcs asegs R HIA h1) m3 slo (bv_unsigned sp) (sp1 + 168) 1 CSOK1 SSH3);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCS1| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    destruct (stk_carve asegs m3 (sp1 + 184) (bv_unsigned sp + -104) gapn SThi3 ltac:(clear - GAP; lia)) as [_ [gb GAPC]].
    replace (bv_unsigned sp + -104 - Z.of_nat gapn) with (sp1 + 184) in GAPC by (clear - GAP; lia).
    set (dX0 := mkMPD (FB + 32) 1 0 0 [] (le_bytes_to_word xpad) LNull). set (dY0 := mkMPD (FB + 64) 1 0 0 [] (le_bytes_to_word ypad) LNull).
    set (dZ0 := mkMPD (sp1 + 168) 1 0 0 [] (le_bytes_to_word zpad) LNull). set (dT0 := mkMPD (FB + 96) 1 0 0 [] (le_bytes_to_word tpad) LNull).
    fold DV_FSH in FSH.
    pose proof (rw_cells_nil_s m3 (sp1 + 168) ltac:(clear - SP1R SP1 SPR; lia)) as ZNIL.
    assert (CST0 : CSTA m3 h1 LB [dX0; dY0; dZ0; dT0] dX
                     (DCS (dv_sp k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 (Z_to_bv 64 X) (Z_to_bv 64 0) k13 (Z_to_bv 64 (FB + 96)) k15 k16 k17 (Z_to_bv 64 FB))
                          (T2C (le_bytes_to_word t2pad)) [] gb [C4 (le_bytes_to_word ub0); C4 (le_bytes_to_word ub1); C4 (le_bytes_to_word ub2)] jq) DV_FSH 0 0).
    { eapply (A_mpi_client2.cs_init asegs R HIA); try eassumption.
      - rewrite EV1. clear. lia.
      - rewrite EFR1. clear. lia.
      - eapply presA_weaken; [exact HP01| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I].
      - repeat (apply Forall_cons; [unfold dX0, dY0, dZ0, dT0; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; unfold mpi_cells;
                  repeat (split; [first [assumption| reflexivity| (left; clear; lia)| (right; clear - SP1; lia)| (clear - FB8; Z.div_mod_to_equations; lia)| (clear - SP1M; Z.div_mod_to_equations; lia)]|]); assumption|]). apply Forall_nil.
      - intros a b da db Ha Hb NE. destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; cbn in Ha, Hb; try (destruct a; discriminate); try (destruct b; discriminate);
          try (exfalso; apply NE; reflexivity).
        all: injection Ha as <-; injection Hb as <-; unfold dX0, dY0, dZ0, dT0; cbn [md_addr]; clear - F1 FBLO SLO SP1 NEEDR; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp, A_mpi_client2.chunk_okA, dX0, dY0, dZ0, dT0.
        repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; split; [| intros d0 Hd; cbn [In] in Hd; destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [md_addr]; clear - F1 FBLO SLO SP1 NEEDR GAP; lia]|]).
        all: try apply Forall_nil.
        all: first [left; clear - SP1 GAP; lia| right; left; clear; lia| right; right; clear; lia].
      - unfold DV_FSH. cbn. clear. lia. }
    clear XC3 YC3 TC3 ZR3 T2R3 SPLO TPC3 JQC GAPC ZNIL FHD SAVE FSH.
    pose proof (cs_opv_A _ _ _ _ _ _ _ CST0) as (CAv & OAv3 & ARv3 & A8v3 & EBA & LENA & NA & FAv & _).
    pose proof (cs_opv_B _ _ _ _ _ _ _ _ CST0) as (CBv3 & OBv3 & BRv3 & B8v3 & EBB3 & LENB3 & NB3 & FBv3 & _).
    rewrite <- AE in CAv, OAv3, ARv3, A8v3. rewrite <- BE in CBv3, OBv3, BRv3, B8v3. unfold mpi_cells in CAv, CBv3.
    destruct (FBv3 ltac:(clear - HR; lia)) as [PB0 OBL].
    (* [comment removed for export] *)
    assert (KA : forall i, SIGF (md_limbs dA) (md_n dA) i -> forall t0 a1 a6 a7,
       aevtA asegs (KF asegs R HIA h1 mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 (Z_to_bv 64 (FB + 96)) (Z_to_bv 64 (FB + 128)) sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 (Z_to_bv 64 (md_n dB)) SHB
                  (Z_to_bv 64 (4 * md_n dB)) (Z_to_bv 64 i) a6 a7
                  (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (A + 10)) SHA10 (Z_to_bv 64 FB) (Z_to_bv 64 B)
                  (Z_to_bv 64 (-12)) (Z_to_bv 64 (B + 8)) SHB8 t5 t6)
             F (Z_to_bv 64 0x9f3a0) fc None m3 (seg_rom asegs))).
    { intros i SX y0 y1 y6 y7.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 (md_p dB + 4 * md_n dB + -4)) with (Z_to_bv 64 (md_p dB + 4 * (md_n dB - 1))) by (f_equal; clear; lia).
      eapply (dv_SCANB2 (Z.to_nat (md_n dB)) h1 m3 (md_n dB) i); try eassumption; first [clear - NB3; lia| exact (proj2 NB3)| clear - HR; lia| reflexivity| idtac].
      intros j SY z1 z4 z6 z7.
      eapply dv_DISPATCH with (dLX := dX0) (dY := dY0) (dZ := dZ0) (dT := dT0); [exact KMAIN| exact CST0| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact UW3| exact BPOS| exact SX| exact SY]. }
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dA)) by (clear - NA; lia).
    zstep. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NA; lia).
    - replace (Z_to_bv 64 (md_n dA)) with (Z_to_bv 64 0) by (f_equal; clear - KN; lia).
      eapply (KA 0). split; [clear - NA; lia|]. split; [rewrite KN; reflexivity| left; reflexivity].
    - destruct (FAv ltac:(clear - KN NA; lia)) as [PA0 OAL].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
      replace (Z_to_bv 64 (md_p dA + md_n dA * 4 + -4)) with (Z_to_bv 64 (md_p dA + 4 * (md_n dA - 1))) by (f_equal; clear; lia).
      eapply (dv_SCANA (Z.to_nat (md_n dA)) h1 m3 (md_n dA)); try eassumption; first [clear - NA; lia| exact (proj2 NA)| clear - KN NA; lia| reflexivity| idtac].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis PHI0 : 0 <= PHIb.
  Hypothesis FR0 : 0 <= FRb.
  Local Notation C_EPI0 := (A_mpi_div_mpi_C.dv_EPI0 R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP LFB dX dA dB PHIb FRb NST XW W0BLK).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@D39565106411.214D60189065437.214L123035966.5    L1499732917.5   L1685717371.0   L19615232286.45 L19615315730.44 L20626602998.2  L2151156588.2   L21855412948.10 L23048752870.3  L26529568682.2  L26892418956.1  L28632618922.2  L31145622673.2  L35646262821.3  L35663928186.7  L35753279338.5  L36811459522.1  L38259954321.2  L39172636981.0  L40346281194.3  L40855856253.3  L40855904881.2  L42628481726.220L44196099187.221L46434418113.1  L4680390712.3   L48825353400.1  L49304025233.2  L49799904432.3  L53897494646.3  L56418360977.2  L56658999053.1  L57698627611.2  L5936160828.209 L60098763854.3  L61714677124.0  L62037211595.7  L63434192922.2  L64850595401.0  L66151427842.16 L66988715284.220L66990877462.218L6753902243.3   L696052593.2    L9356559676.11  P26535597421.215P28627113325.214P31146933846.214P38261788758.214P49296947798.214P56407612502.214P57713046236.214Q17507758561.212Q28465177121.212Q33346114581.211Q3419689062.214 Q3421936230.214 Q352286600.211  Q39180574961.214Q39212284437.212Q39404899751.223Q4397970789.212 Q47860023380.224Q50845955027.224Q5265442331.213 Q55415036769.214Q57228775306.214Q57230951818.214Q59321350679.214Q60511567613.212Q61917304426.224Q61918965590.223Q6227507588.212 Q6228015238.209 Q6228015238.220 Q63396246492.224Q65429948823.220Q65901445061.223Q66096743522.209Q68235297648.214Q9538787269.209 00001B02T02g03303403503603:03A03`03k03l04004104204=04R04S04W04X04Y04d04n04o05R06106606A06E06F06R06\06]06a06b07B07L07M07h07o08008J08l09N09Y09a0:L0:M0;K0<I0=G0>E0?C0?m0@<0@U0A00A]0BJ0Bb0Cc0D20DD0DW0Di0E\0F60F`0GJ0H40H50HB0HT0Hf0I50ID0IV0IW0Ii0J;0JJ0Jm0K:S1R3HIA1h2LF2ra2sp1B3TOP3LFB2FB3sp14gapn3GAP2h13ET13SPR2F04SP1R3BRv2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp1B2lo3LOS3SLO3LFB2FB3sp14gapn3SP13SPR2F04SP1R3BRv2HB5Ha_st5Hl_stS2sp2lo3sp13SP13LOCS2lo3sp13LOCSFFS2dBS2dB2NBS1R3HIA1h2sp2lo3sp13LOC3CSP1x1KS2dB2r'3HR'FS2spFFS2dB2r'3HR'S1R3HIA1h2sp2lo3TOP1HFS2dBFSS2dB2r'3HR'S2dB2NB2KNFS2LF2ra2sp1B3LFB2dB2FB3sp14gapn3BRvS2LF2ra2sp1B3LFB2dB2FB3sp14gapnS3sp1S2dB2r'3HR'S2dBFS2sp3sp13SP1S2dB2NB2KNFS2spFS2LF2ra2sp1B3LFB2FB3sp14gapn3BRvS1R2lo3LOSSS1R5NEEDR2sp2lo3LOS3SLO3SPRS2dB2NBSS2sp2r03SPA1q1r1H2H02q02H4S2LF2ra2sp1B3LFB2dB2FB3sp14gapn2NBS2LF2ra2sp1B3LFB2dB2FB3sp14gapn2NBS2dB2r'3HR'S2sp3SPRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14gapn3SP14FBLO2HB5Ha_st5Hl_stS2LF2sp3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF1B3LFB4gapnS2LF3LFB3sp14gapn4SP1R2HBS2LF2sp2lo3LFB3sp14gapn3SP1S2LF2sp2lo3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP13ALO2HB5Ha_st5Hl_stS2LF1B3LFB4gapnS2LF1B3LFB2dB4gapnS2LF1B3LFB4gapn3BRvS2LF1B3LFB2dB4gapnS2LF2ra2sp1B3LFB2dB2FB3sp14gapn3SPR2F04SP1R3BRv3B8vS2LF3LFB3sp14gapn2HB5Ha_stS2LF2sp3LFB2FB3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2lo3LFB2FB3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2FB3sp14gapn3LOC2HB5Ha_st5Hl_stFS2LF3LFB4gapnS2LF1B3LFB2dB4gapnS2LF1B3LFB2dB4gapnS2LF1B3LFB4gapnS2LF1B3LFB4gapnS2LF1B3LFB2dB4gapnFS2LF1B3LFB2dB4gapnS2LF1B3LFB2dB4gapnS2LF1B3LFB4gapnS2LF3LFB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF3LFB4gapn". (* [comment removed for export] *)
  #[using="IMG NS1 NEEDR LOS SLO SLOS TOP SPA TPV LFB XE AE BE HNDk DIMG H0M NST XW W0AS W0BLK D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR slo SLO1 SLO2 MX0 OXs0 ESM SSH0 MI0 PHI0 FR0"] Lemma dv_S : forall (h1 : HST asegs R HIA) (m1 : mem) (jx jy jt jp jq : list byte) (sl : list word)
      xra t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6,
    dv_MAIN_stmt ->
    HM asegs R HIA h1 LB LF1 m1 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h ->
    havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) ->
    rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs m1 (FB + 32) [CB 16 jx] -> rw_cells asegs m1 (FB + 64) [CB 16 jy] -> rw_cells asegs m1 (FB + 96) [CB 16 jt] ->
    rw_cells asegs m1 (FB + 128) [CB 12 jp; CB 4 jq] ->
    rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) DV_FSH ->
    rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL ->
    rw_cells asegs m1 sp1 (map C8 sl) -> length sl = 23%nat ->
    stk asegs m1 (sp1 + 184) (bv_unsigned sp + -104) -> stk asegs m1 lo sp1 -> mem_inv asegs m1 ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtA asegs (KF asegs R HIA h1 mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) (Z_to_bv 64 (B + 10)) a2 (Z_to_bv 64 (Z.shiftr (B + 10) 3 + al_sb AL)) a4 a5 a6 a7
               (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 A) SH4 s5 s6 (Z_to_bv 64 X) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 B) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f228) fc None m1 (seg_rom asegs)).
  Proof.
    intros until t6. intros KMAIN HH1 Ehcs ET1 ES1 EF1 EV1 EFR1 HKI FHD XC YC TC TPC FSH SAVE SPILL LSL SThi STlo MI1 PRES UW.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    ddestruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (_ & _ & _ & _ & _ & _ & _ & FBLO & SBND & APS).
    change (256 / 8) with 32 in SBND, APS. unfold DV_FSH in FSH. cbn [zcells app] in FSH.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (hcs_stack asegs R HIA h1) as SCS01.
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| rewrite ES1; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (rewrite <- Ehcs; exact SCS1).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 256) by (rewrite Ehcs; exact CFB).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HP01.
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
    assert (UWF : UWCD m1).
    { pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    (* [comment removed for export] *)
    ddestruct (dv_TR h1 m1 Ehcs MI1 HP01) as ([MX1 OX1] & EXT1 & _).
    pose proof (proj1 (Forall_forall _ _) EXT1 dB ESB) as [MB1 OB1].
    dpose (opv_of_mpd h1 LB LF1 m1 dB HH1 MB1 OB1 IB2) as (CBv & OBv & BRv & B8v & _).
    rewrite <- BE in CBv, OBv, BRv, B8v. unfold mpi_cells in CBv.
    destruct sl as [|k0 sl]; [discriminate LSL|]. destruct sl as [|k1 sl]; [discriminate LSL|]. destruct sl as [|k2 sl]; [discriminate LSL|]. destruct sl as [|k3 sl]; [discriminate LSL|]. destruct sl as [|k4 sl]; [discriminate LSL|]. destruct sl as [|k5 sl]; [discriminate LSL|]. destruct sl as [|k6 sl]; [discriminate LSL|]. destruct sl as [|k7 sl]; [discriminate LSL|]. destruct sl as [|k8 sl]; [discriminate LSL|]. destruct sl as [|k9 sl]; [discriminate LSL|]. destruct sl as [|k10 sl]; [discriminate LSL|]. destruct sl as [|k11 sl]; [discriminate LSL|]. destruct sl as [|k12 sl]; [discriminate LSL|]. destruct sl as [|k13 sl]; [discriminate LSL|]. destruct sl as [|k14 sl]; [discriminate LSL|]. destruct sl as [|k15 sl]; [discriminate LSL|]. destruct sl as [|k16 sl]; [discriminate LSL|]. destruct sl as [|k17 sl]; [discriminate LSL|]. destruct sl as [|k18 sl]; [discriminate LSL|]. destruct sl as [|k19 sl]; [discriminate LSL|]. destruct sl as [|k20 sl]; [discriminate LSL|]. destruct sl as [|k21 sl]; [discriminate LSL|]. destruct sl as [|k22 sl]; [discriminate LSL|]. 
    destruct sl; [| discriminate LSL]. cbn [map] in SPILL. clear LSL.
    pose proof (munch_refl [(sp1, sp1 + 184)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    shadow_chk OBv (B + 10) 2.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA h1 LB LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : stk asegs m2 (sp1 + 184) _ |- _ => rename H into SThi2 end.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HP02.
    ddestruct (dv_TR h1 m2 Ehcs MI2 HP02) as ([MX2 OX2] & EXT2 & _).
    assert (UW2 : UWCD m2) by (eapply uwcd_store; [exact UWF| exact MU| clear; lia]).
    clear MU WM MX1 OX1 EXT1 MB1 OB1 UW1 UWF HP01.
    pose proof (proj1 (Forall_forall _ _) EXT2 dB ESB) as [MB2 OB2].
    dpose (opv_of_mpd h1 LB LF1 m2 dB HH2 MB2 OB2 IB2) as (_ & _ & _ & _ & EBB & LENB & NB & FBv & _).
    fold DV_FSH in FSH.
    (* [comment removed for export] *)
    assert (KZ : forall xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s3v s5v s6v s7v s8v s10v,
       aevtA asegs (KF asegs R HIA h1 mo0) POSTD
         (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v SH4 s5v s6v s7v s8v (Z_to_bv 64 FB) s10v (Z_to_bv 64 (-12)) t3 t4 t5 t6)
             F (Z_to_bv 64 0x9f790) fc None m2 (seg_rom asegs))).
    { intros until s10v.
      assert (STall : stk asegs m2 lo (bv_unsigned sp + -104)).
      { pose proof (stk_of_rw_cells asegs m2 _ _ SPILL) as K1. cbn [cells_size csize Nat.add] in K1. change (Z.of_nat 184) with 184 in K1.
        eapply (stk_merge asegs); [| exact SThi2| clear - SP1 LOC; lia]. eapply (stk_merge asegs); [exact ST2| exact K1| clear - SP1 LOC; lia]. }
      eapply C_EPI0 with (r := -12); try eassumption; try (clear; lia).
      destruct XW as [CW _]. intros x Hx. destruct (CW x Hx) as [K|[K|K]]; [left; clear - K LOC CSP; lia| right; left; exact K| right; right; exact K]. }
    pose proof (proj1 (Forall_forall _ _) EXT2 dB ESB) as [_ OB2'].
    dpose (opv_of_mpd h1 LB LF1 m2 dB HH2 MB2 OB2 IB2) as (CBv2 & OBv2 & BRv2 & B8v2 & _).
    rewrite <- BE in CBv2, OBv2, BRv2, B8v2. unfold mpi_cells in CBv2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. rewrite (zx16_small (md_n dB)) by (clear - NB; lia). zstep.
    zstep. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by (clear - NB; lia); [eapply KZ|].
    destruct (FBv ltac:(clear - KN NB; lia)) as [PB0 OBL].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (md_p dB + md_n dB * 4 + -4)) with (Z_to_bv 64 (md_p dB + 4 * (md_n dB - 1))) by (f_equal; clear; lia).
    replace (Z_to_bv 64 (md_n dB * 4)) with (Z_to_bv 64 (4 * md_n dB)) by (f_equal; clear; lia).
    eapply (dv_SCANB1 (Z.to_nat (md_n dB)) h1 m2 (md_n dB)); try eassumption; first [clear - NB; lia| exact (proj2 NB)| clear - KN NB; lia| idtac].
    intros r' HR' NZ y0 y1 y6 y7.
    assert (VB : 0 < mpd_abs dB).
    { rewrite (mpd_abs_lval dB LENB). clear - HR' NZ LENB (* [comment removed for export] *). pose proof (lval_top_nonzero (md_limbs dB) r' ltac:(clear - HR'; lia) NZ). pose proof (pow32_pos (r' - 1) ltac:(clear - HR'; lia)).
      pose proof (lval_split (md_limbs dB) r' (md_n dB) ltac:(clear - HR'; lia)). pose proof (lval_range (skipn (Z.to_nat r') (md_limbs dB)) (md_n dB - r') ltac:(clear - HR'; lia)).
      unfold lseg in *. pose proof (pow32_pos r' ltac:(clear - HR'; lia)). nia. }
    eapply (dv_INIT h1 m2 r' jx jy jt jp jq [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14; k15; k16; k17; Z_to_bv 64 FB; k19; k20; k21; k22]); try eassumption; try reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Fr.
  End Call.
End WalkS.
