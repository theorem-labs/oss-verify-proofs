(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_div_stmtA A_mpi_div_mpi_P A_mpi_div_mpi_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_shift_l_c24 A_mpi_add_sub_sz_c24 A_mpi_add_sub_o_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_cmp_mpi A_mpi_cmp_mpi_raw BX_mpi_cmp_abs_stmt A_mpi_cmp_int.
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
  Local Notation RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) (Z_to_bv 64 (FB + 80))
         (Z_to_bv 64 A) SH4 (Z_to_bv 64 B) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6).



  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CMPR : A_mpi_cmp_mpi_raw.mpi_cmp_mpi_raw_stmtA asegs AL A_mpi_cmp_mpi.A_MPI_CMP_MPI_E.
  Hypothesis CABS : BX_mpi_cmp_abs_stmt.mpi_cmp_abs_stmtA asegs AL BX_mpi_cmp_abs_stmt.BX_MPI_CMP_ABS.
  Local Notation hcs_img_cs_cp := A_mpi_copy.hcs_img_cs_cp (only parsing).

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
  Local Notation T2C t2pad := [C8 (Z_to_bv 64 (FB + 176)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 3); C4 t2pad].
  Local Notation CZC czpad := [C8 (Z_to_bv 64 (FB + 64)); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 1); C4 czpad].
  Local Notation DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 t2c czc gb z32 z48 z64 u0 u1 u2 jq :=
    (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 (Z_to_bv 64 X) (Z_to_bv 64 (FB + 176)) (Z_to_bv 64 0) (Z_to_bv 64 FB))
         t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB XE AE HNDk DIMG H0M NST XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 ESA BE_PHI BE_FR"] Lemma dv_EARLY : forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
      (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 (T2C t2pad) (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9f88c) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST EAX EAY EAZ EAD OX0 OY0 OZ0 OT0 UW BPOS. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
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
    zstep. zstep. try (if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear; lia); [| exfalso; first [ (clear - KQ; lia) | (vm_compute in KQ; first [discriminate KQ | exact (KQ eq_refl) | lia]) ]]).
    zstep. zstep. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by (rewrite XE; clear - XB16 X0q; lia); [exfalso; rewrite XE in KR; clear - KR X0q; lia|].
    (* [comment removed for export] *)
    zstep. zstep. clear MU WM.
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
    assert (CST3 : CSTA m3 h3 LB3 [dLX; dY; dZ; dT] dX3 (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 (T2C t2pad) (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (0 + copy_PHI dA) (0 + copy_FR d)).
    { eapply (A_mpi_client2.cs_binop_w asegs R HIA) with (mq := mq) (hq := hq) (SPx := sp1); try eassumption; try (clear - SP1; lia).
      - eapply w_aobj_step; [exact CST| exact HP3| exact HCS3].
      - destruct RV as [(_ & _ & K1 & _)|(_ & K1 & _)]; clear - K1; lia.
      - unfold A_mpi_div_mpi_C.DCS. repeat (apply Forall_cons; [cbn [fst snd]|]). all: first [apply Forall_nil| left; clear - SP1; lia| right; clear; lia].
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
      zstep. try (if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear; lia); [| exfalso; first [ (clear - KC; lia) | (vm_compute in KC; first [discriminate KC | exact (KC eq_refl) | lia]) ]]).
      eapply C_EXIT0; [exact CST3| exact EAZ| exact OX0| exact OY0| exact OZ0| exact OT0| reflexivity| reflexivity| reflexivity| exact BPOS| exact HSZ3| |].
      + clear - BE_PHI CP0. unfold AVOL_CALL in *. lia.
      + clear - BE_FR CP0 D0. unfold fr_charge in *. lia.
    - (* [comment removed for export] *)
      zstep. try (if_cases KC; zify_cond KC; [exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KC; first [ (rewrite ?unsigned_lit in KC by (clear; lia); clear - KC; lia) | (vm_compute in KC; first [discriminate KC | lia]) ]|]).
      zstep.
      eapply C_CLEAN_X with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAX| exact EAY| exact EAZ| exact EAD| reflexivity| reflexivity| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| intros K; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; clear - K; lia| exact HSZ3| |].
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
  #[using="Type"] Lemma dcs_ok : forall ls spc t2c zc czc gb z32 z48 z64 tpc jq spc' t2c' zc' czc' gb' z32' z48' z64' tpc' jq',
    Forall (COK ls) (DCS spc t2c zc czc gb z32 z48 z64 tpc jq) ->
    cells_size spc' = cells_size spc -> cells_size t2c' = cells_size t2c -> cells_size zc' = cells_size zc -> cells_size czc' = cells_size czc ->
    cells_size tpc' = cells_size tpc ->
    Forall (COK ls) (DCS spc' t2c' zc' czc' gb' z32' z48' z64' tpc' jq').
  Proof.
    intros ls spc t2c zc czc gb z32 z48 z64 tpc jq spc' t2c' zc' czc' gb' z32' z48' z64' tpc' jq' OK E1 E2 E3 E5 E4. unfold A_mpi_div_mpi_C.DCS in *.
    repeat (apply Forall_cons_iff in OK; destruct OK as [?K OK]).
    unfold A_mpi_client2.chunk_okA in *. cbn [fst snd cells_size csize Nat.add] in *.
    repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; rewrite ?E1, ?E2, ?E3, ?E5, ?E4; assumption|]). apply Forall_nil.
  Qed.
  #[using="Type"] Lemma uwc_raise_s : forall mx LO' TOP' vv F0' F1' dd, uwc asegs mx LO' TOP' vv F0' dd -> F1' + 16 <= vv -> uwc asegs mx LO' TOP' vv F1' dd.
  Proof.
    intros mx LO' TOP' vv F0' F1' dd HU HF. inversion HU; subst; [apply uwc_stop; assumption| eapply uwc_link; eassumption| apply uwc_cap; assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L26496199141.3L55454580985.9L62037211595.7L8931608776.1 L9366540546.1000000<00V01101601]S2sp3sp13SP1S1R3HIA1h3sp11a1b2HB2a02HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACP". (* [comment removed for export] *)
  #[using="IMG NEEDR lo LOS SLO SP1"] Lemma uwcd_store : forall mq m2 a b, UWCD mq -> munch [(a, b)] mq m2 -> b <= sp1 + 216 -> UWCD m2.
  Proof.
    intros mq m2 a b UW MU HB. rt_facts.
    eapply uwc_floor with (F := sp1 + 216); [| clear; lia].
    eapply uwc_munch; [eapply uwc_raise_s; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
    intros a0 Ha. cbn [outside]. split; [clear - Ha HB; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dv_MAIN_stmt : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
      (DCSE c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 (T2C t2pad) (CZC czpad) gb z32 z48 z64 u0 u1 u2 jq) DV_FSH 0 0 ->
    md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    UWCD mq -> 0 < mpd_abs dB -> mpd_abs dB <= mpd_abs dA ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RG xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9f690) fc None mq (seg_rom asegs)).

  #[using="Type"] Lemma lval_abs : forall e, Z.of_nat (length (md_limbs e)) = md_n e -> lval (md_limbs e) (md_n e) = mpd_abs e.
  Proof. intros e LEN. unfold lval, mpd_abs. rewrite <- LEN, Nat2Z.id, firstn_all. reflexivity. Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG NEEDR ra LOS SLO TOP LFB DIMG H0M XW W0AS gapn SP1 F64 FRSH ESF LOC CSP FN64 FB8"] Lemma s_stack_step : forall mq hq LBq ls dW CS0 v f m2 a,
    CSTA mq hq LBq ls dW CS0 DV_FSH v f -> munch [(a, sp1)] mq m2 -> wmono asegs mq m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 -> lo <= a -> a <= sp1 ->
    CSTA m2 hq LBq ls dW CS0 DV_FSH v f /\ (UWCD mq -> UWCD m2).
  Proof.
    intros mq hq LBq ls dW CS0 v f m2 a CST MU WM MI2 ST2 HLA HAS. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    (* [comment removed for export] *)
    assert (HH2 : HM asegs R HIA hq LBq LF1 m2).
    { eapply (hm_munch asegs R HIA hq LBq LF1 [(a, sp1)] mq m2 HHq MU WM). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      intros x Hx. left. left. rewrite HTq. clear - Hx HLA LOS SP1 TOP. lia. }
    split.
    - (* [comment removed for export] *)
      assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [] mq m2).
      { eapply (presA_drop_below asegs R HIA hq LBq LF1 _ a sp1 mq mq m2 sp1 HHq); [| clear; lia| clear - HLA LOS; lia].
        eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSq| clear - HLA; lia| clear - SP1 HAS; lia]| apply Forall_nil]. }
      (* [comment removed for export] *)
      eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := []); try eassumption; [apply Forall_nil|].
      apply Forall_forall. intros ac _. exact I.
    - (* [comment removed for export] *)
      intros UW. eapply uwcd_store; [exact UW| exact MU| clear; lia].
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG NS1 NEEDR LOS SLO SLOS TOP SPA TPV LFB XE AE BE HNDk DIMG H0M NST XW W0AS W0BLK D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR OB CABS slo SLO1 SLO2 MX0 OXs0 ESM SSH0 MI0"] Lemma dv_INIT : forall (h1 : HST asegs R HIA) (m2 : mem) (j1 j2 jz1 jx jy jt jp jq : list byte) (czpad : word)
      (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k168 k176 k184 k192 : word)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    dv_MAIN_stmt ->
    HM asegs R HIA h1 LB LF1 m2 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h ->
    havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    rw_cells asegs m2 FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs m2 (FB + 32) [CB 8 j1] -> rw_cells asegs m2 (FB + 48) [CB 8 j2] -> rw_cells asegs m2 (FB + 64) [C4 (Z_to_bv 64 0); CB 4 jz1] ->
    rw_cells asegs m2 (FB + 80) [CB 16 jx] -> rw_cells asegs m2 (FB + 112) [CB 16 jy] -> rw_cells asegs m2 (FB + 144) [CB 16 jt] ->
    rw_cells asegs m2 (FB + 176) [CB 12 jp; CB 4 jq] ->
    rw_cells asegs m2 (Z.shiftr FB 3 + al_sb AL) DV_FSH ->
    rw_cells asegs m2 (bv_unsigned sp + -104) SAVEL ->
    rw_cells asegs m2 sp1 [C8 k0; C8 k1; C8 k2; C8 k3; C8 k4; C8 k5; C8 k6; C8 k7; C8 k8; C8 k9; C8 k10; C8 k11; C8 k12; C8 k13; C8 k14; C8 k15; C8 k16; C8 k17; C8 k18] ->
    rw_cells asegs m2 (sp1 + 152) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FB)] ->
    rw_cells asegs m2 (sp1 + 168) [C8 k168; C8 k176; C8 k184; C8 k192] ->
    rw_cells asegs m2 (sp1 + 200) (CZC czpad) ->
    stk asegs m2 (sp1 + 216) (bv_unsigned sp + -104) -> stk asegs m2 lo sp1 -> mem_inv asegs m2 ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m2 ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    0 < mpd_abs dB ->
    aevtA asegs (KF asegs R HIA h1 mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 X) (Z_to_bv 64 (-8)) s6 s7 (Z_to_bv 64 A) SH4 (Z_to_bv 64 B) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f634) fc None m2 (seg_rom asegs)).
  Proof.
    intros until t6. intros KMAIN HH1 Ehcs ET1 ES1 EF1 EV1 EFR1 FHD J1C J2C JZC XC YC TC TPC FSH SAVE SPILL SP152 SL2 CZ2 SThi STlo MI2 PRES UW BPOS.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    ddestruct (frame_factsA R HIA CS h1 LB LF m2 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (_ & _ & _ & _ & _ & _ & _ & FBLO & SBND & APS).
    change (256 / 8) with 32 in SBND, APS.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (hcs_stack asegs R HIA h1) as SCS01.
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| rewrite ES1; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (rewrite <- Ehcs; exact SCS1).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 256) by (rewrite Ehcs; exact CFB).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    (* [comment removed for export] *)
    chunk_split SPILL 17%nat SPLO SPHI.
    apply rw_cells_CB_of in SL2; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in SL2.
    lazymatch type of SL2 with rw_cells _ _ _ [CB 32 ?j] => set (jh := j) in SL2; clearbody jh end.
    apply (rw_cells_split_CB asegs m2 _ [] 32 _ [] [8; 4; 4; 8; 4; 4]%nat) in SL2; [| reflexivity]. cbn [mk_CB_cells app] in SL2. cb8_all SL2.
    lazymatch type of SL2 with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c; C8 ?d; CB 4 ?e; CB 4 ?f] =>
      set (q0 := a) in SL2; set (q1 := b) in SL2; set (t2pad := c) in SL2; set (q3 := d) in SL2; set (q4 := e) in SL2; set (zpad := f) in SL2; clearbody q0 q1 t2pad q3 q4 zpad end.
    chunk_split SL2 3%nat T2R ZR. replace (sp1 + 168 + 16) with (sp1 + 184) in ZR by (clear; lia).
    (* [comment removed for export] *)
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
    chunk_split TPC 3%nat TPC3 JQC. replace (FB + 176 + 12) with (FB + 188) in JQC by (clear; lia).
    assert (IND : In (FB + 32, 216) (LB ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWX : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 80) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWY : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 112) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (CWT : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 144) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    unfold DV_FSH in FSH. cbn [zcells app] in FSH.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sp1 + 136, sp1 + 200); (FB + 80, FB + 160)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    do 19 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA h1 LB LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : stk asegs m3 (sp1 + 216) _ |- _ => rename H into SThi3 end.
    (* [comment removed for export] *)
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HP03.
    ddestruct (dv_TR h1 m3 Ehcs MI3 HP03) as ([MX3 OX3] & EXT3 & SSH3).
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP03| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
    assert (UW3 : UWCD m3).
    { pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    clear MU WM UW1.
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
    assert (T2R3 : rw_cells asegs m3 (sp1 + 168) (T2C (le_bytes_to_word t2pad))).
    { pose proof (rw_cells_split_C4 asegs m3 _ [C8 (Z_to_bv 64 (FB + 176))] (Z_to_bv 64 196609) _ T2R) as T22. cbn [app] in T22.
      pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m3 _ [C8 (Z_to_bv 64 (FB + 176)); C2 (Z_to_bv 64 196609); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 196609) / 2 ^ 16))] t2pad [] T22) as T23. cbn [app] in T23.
      assert (E2 : le2 (Z_to_bv 64 196609) = le2 (Z_to_bv 64 1)) by (rewrite !le2_of_Z; rewrite <- (CellsX.Z_to_le_bytes_mod 2 196609); reflexivity).
      assert (E3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 196609) / 2 ^ 16) = Z_to_bv 64 3) by (rewrite unsigned_lit by (clear; lia); reflexivity).
      rewrite E3 in T23.
      eapply rw_cells_reshape; [exact T23| |].
      - cbn -[le2 le4 le8]. repeat split; try (rewrite ?length_le2, ?length_le4, ?length_le8; reflexivity).
      - cbn -[le2 le4 le8]. rewrite E2. reflexivity. }
    clear XC XC2 YC YC2 TC TC2 ZR ZR2 T2R.
    (* [comment removed for export] *)
    destruct (stk_carve asegs m3 (sp1 + 216) (bv_unsigned sp + -104) gapn SThi3 ltac:(clear - GAP; lia)) as [_ [gb GAPC]].
    replace (bv_unsigned sp + -104 - Z.of_nat gapn) with (sp1 + 216) in GAPC by (clear - GAP; lia).
    apply rw_cells_CB_of in JZC; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in JZC.
    lazymatch type of JZC with rw_cells _ _ _ [CB 8 ?j] => set (z64 := j) in JZC; clearbody z64 end.
    chunk_join SPLO SPHI SPJ1. chunk_join SPJ1 SP152 SPC.
    set (dX0 := mkMPD (FB + 80) 1 0 0 [] (le_bytes_to_word xpad) LNull). set (dY0 := mkMPD (FB + 112) 1 0 0 [] (le_bytes_to_word ypad) LNull).
    set (dZ0 := mkMPD (sp1 + 184) 1 0 0 [] (le_bytes_to_word zpad) LNull). set (dT0 := mkMPD (FB + 144) 1 0 0 [] (le_bytes_to_word tpad) LNull).
    pose proof (rw_cells_nil_s m3 (sp1 + 184) ltac:(clear - SP1R SP1 SPR; lia)) as ZNIL.
    frame_aobj FSH (FB + 80) 2%nat as OXL. frame_aobj FSH (FB + 112) 2%nat as OYL. frame_aobj FSH (FB + 144) 2%nat as OTL.
    assert (OZL : aobj asegs AL (hcs asegs R HIA h1) m3 (sp1 + 184) 16).
    { apply (aobj_of_sshad_s (hcs asegs R HIA h1) m3 slo (bv_unsigned sp) (sp1 + 184) 1 CSOK1 SSH3);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCS1| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    fold DV_FSH in FSH.
    assert (CST0 : CSTA m3 h1 LB [dX0; dY0; dZ0; dT0] dX
                     (DCSE k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 (T2C (le_bytes_to_word t2pad)) (CZC czpad) gb j1 j2 z64
                           (le_bytes_to_word ub0) (le_bytes_to_word ub1) (le_bytes_to_word ub2) jq) DV_FSH 0 0).
    { eapply (A_mpi_client2.cs_init asegs R HIA); try eassumption.
      - rewrite EV1. clear. lia.
      - rewrite EFR1. clear. lia.
      - eapply presA_weaken; [exact HP03| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I].
      - repeat (apply Forall_cons; [unfold dX0, dY0, dZ0, dT0; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; unfold mpi_cells;
                  repeat (split; [first [assumption| reflexivity| (left; clear; lia)| (right; clear - SP1; lia)| (clear - FB8; Z.div_mod_to_equations; lia)| (clear - SP1M; Z.div_mod_to_equations; lia)]|]); try assumption|]).
        all: try apply Forall_nil.
        all: match goal with |- ?g => idtac "CSI-LOC-LEFT:" g end.
      - intros a b da db Ha Hb NE. destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; cbn in Ha, Hb; try (destruct a; discriminate); try (destruct b; discriminate);
          try (exfalso; apply NE; reflexivity).
        all: injection Ha as <-; injection Hb as <-; unfold dX0, dY0, dZ0, dT0; cbn [md_addr]; clear - F1 FBLO SLO SP1 NEEDR; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp, A_mpi_client2.chunk_okA, dX0, dY0, dZ0, dT0.
        repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; split; [| intros d0 Hd; cbn [In] in Hd; destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [md_addr]; clear - F1 FBLO SLO SP1 NEEDR GAP; lia]|]).
        all: try apply Forall_nil.
        all: first [left; clear - SP1 GAP; lia| right; left; clear; lia| right; right; clear; lia].
      - unfold DV_FSH. cbn. clear. lia. }
    clear XC3 YC3 TC3 ZR3 T2R3 SPC TPC3 JQC GAPC ZNIL FHD SAVE FSH J1C J2C JZC CZ2.
    (* [comment removed for export] *)
    pose proof (cs_opv_A _ _ _ _ _ _ _ CST0) as (CAv & OAv3 & ARv3 & A8v3 & EBA & LENA & NA & FAv & _).
    pose proof (cs_opv_B _ _ _ _ _ _ _ _ CST0) as (CBv3 & OBv3 & BRv3 & B8v3 & EBB3 & LENB3 & NB3 & FBv3 & _).
    assert (MAq : mpd_at asegs m3 LB dA).
    { destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE].
      - assert (EQA : dA = dX) by (destruct SXA as [K|K]; [symmetry; exact K| exfalso; clear - K E; lia]). rewrite EQA. exact MX3.
      - exact (proj1 (proj1 (Forall_forall _ _) EXT3 dA (ESA NE))). }
    assert (MBq : mpd_at asegs m3 LB dB) by exact (proj1 (proj1 (Forall_forall _ _) EXT3 dB ESB)).
    assert (NNA : 1 <= md_n dA -> md_own dA <> LNull).
    { intros N1 EO. pose proof MAq as [(_ & _ & _ & _ & _ & OWA) _]. rewrite EO in OWA. simpl in OWA. destruct OWA as [_ N0]. clear - N0 N1. lia. }
    assert (NNB : 1 <= md_n dB -> md_own dB <> LNull).
    { intros N1 EO. pose proof MBq as [(_ & _ & _ & _ & _ & OWB) _]. rewrite EO in OWB. simpl in OWB. destruct OWB as [_ N0]. clear - N0 N1. lia. }
    assert (PA0 : md_own dA = LHeap -> 0 < md_p dA).
    { intros EO. pose proof MAq as [(_ & _ & _ & _ & _ & OWA) _]. rewrite EO in OWA. simpl in OWA. destruct OWA as [N1 _]. exact (proj1 (FAv N1)). }
    assert (PB0 : md_own dB = LHeap -> 0 < md_p dB).
    { intros EO. pose proof MBq as [(_ & _ & _ & _ & _ & OWB) _]. rewrite EO in OWB. simpl in OWB. destruct OWB as [N1 _]. exact (proj1 (FBv3 N1)). }
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    pose proof CABS as CAB. unfold BX_mpi_cmp_abs_stmt.mpi_cmp_abs_stmtA, BX_mpi_cmp_abs_stmt.BX_MPI_CMP_ABS in CAB.
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { try unfold BX_mpi_cmp_abs_stmt.BX_MPI_CMP_ABS.
      eapply CAB with (CS := hcs asegs R HIA h1) (LB := LB) (dX := dA) (dY := dB) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact MAq | exact MBq | exact PA0 | exact PB0 | exact MI3 | exact (art_alwf asegs R HIA) | exact CSOK1
              | exact (hm_abase asegs R HIA h1 LB LF1 m3 HH3) | exact OAv3 | exact OBv3 | exact ST3
              | (intros N1; exact (proj2 (FAv N1))) | (intros N1; exact (proj2 (FBv3 N1)))
              | (clear - LOS ALO ACP; lia)
              | (unfold BX_mpi_cmp_abs_stmt.MPI_CMP_ABS_STACK_A; clear - SLO SP1 NEEDR; lia)
              | (clear - SLO SP1 NEEDR; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS1| clear; lia| clear - SP1; lia])
              | (destruct OA4 as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (destruct OB4 as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (intros N1; destruct (OA5 (NNA N1)) as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (intros N1; destruct (OB5 (NNB N1)) as [K|K]; [left; exact K| right; clear - K SP1; lia])
              | (rewrite <- AE; reflexivity)
              | (rewrite <- BE; reflexivity)
              | reflexivity
              | match goal with |- ?g => idtac "CABS-PRE-LEFT:" g end ]. }
    (* [comment removed for export] *)
    cbv beta. intros ms' PO. unfold A_mpi_cmp_mpi.mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU4 & WM4 & MI4 & ST4).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    destruct (s_stack_step m3 h1 LB _ _ _ _ _ _ lo CST0 MU4 WM4 MI4 ST4 ltac:(clear; lia) ltac:(clear - SLO SP1 NEEDR; lia)) as [CST4 UWK].
    pose proof (UWK UW3) as UW4. clear UWK.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (Z.sgn ?v)] => destruct (Z.sgn_spec v) as [(KS & ->)|[(KS & ->)|(KS & ->)]] end.
    3: { (* [comment removed for export] *)
      zstep. eapply dv_EARLY; [exact CST4| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact UW4| exact BPOS]. }
    all: zstep; eapply KMAIN; [exact CST4| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact UW4| exact BPOS| clear - KS; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis PHI0 : 0 <= PHIb.
  Hypothesis FR0 : 0 <= FRb.
  Local Notation C_EPI0 := (A_mpi_div_mpi_C.dv_EPI0 R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 lo LOS SLO TOP LFB dX dA dB PHIb FRb NST XW W0BLK).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="IMG NS1 NEEDR LOS SLO SLOS TOP SPA TPV LFB XE AE BE HNDk DIMG H0M NST XW W0AS W0BLK D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR OB CMPR CABS slo SLO1 SLO2 MX0 OXs0 ESM SSH0 MI0 PHI0 FR0"] Lemma dv_S : forall (h1 : HST asegs R HIA) (m1 : mem) (j1 j2 jz jx jy jt jp jq : list byte) (sl sl2 : list word)
      xra t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    dv_MAIN_stmt ->
    HM asegs R HIA h1 LB LF1 m1 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h ->
    havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) ->
    rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs m1 (FB + 32) [CB 8 j1] -> rw_cells asegs m1 (FB + 48) [CB 8 j2] -> rw_cells asegs m1 (FB + 64) [CB 8 jz] ->
    rw_cells asegs m1 (FB + 80) [CB 16 jx] -> rw_cells asegs m1 (FB + 112) [CB 16 jy] -> rw_cells asegs m1 (FB + 144) [CB 16 jt] ->
    rw_cells asegs m1 (FB + 176) [CB 12 jp; CB 4 jq] ->
    rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) DV_FSH0 ->
    rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL ->
    rw_cells asegs m1 sp1 (map C8 sl) -> length sl = 19%nat ->
    rw_cells asegs m1 (sp1 + 152) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 FB)] ->
    rw_cells asegs m1 (sp1 + 168) (map C8 sl2) -> length sl2 = 6%nat ->
    stk asegs m1 (sp1 + 216) (bv_unsigned sp + -104) -> stk asegs m1 lo sp1 -> mem_inv asegs m1 ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d ->
    aevtA asegs (KF asegs R HIA h1 mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (FB + 64)) a1 (Z_to_bv 64 65537) a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 X) (Z_to_bv 64 (-8)) s6 s7 (Z_to_bv 64 A) SH4 (Z_to_bv 64 B) (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f614) fc None m1 (seg_rom asegs)).
  Proof.
    intros until t6. intros KMAIN HH1 Ehcs ET1 ES1 EF1 EV1 EFR1 HKI FHD J1C J2C JZC XC YC TC TPC FSH SAVE SPILL LSL SP152 SL2C LSL2 SThi STlo MI1 PRES UW.
    rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
    ddestruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (_ & _ & _ & _ & _ & _ & _ & FBLO & SBND & APS).
    change (256 / 8) with 32 in SBND, APS.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h1) as CSOK1. pose proof (hcs_stack asegs R HIA h1) as SCS01.
    assert (SCS1 : crange (hcs asegs R HIA h1) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS01| clear - LOS; lia| rewrite ES1; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (rewrite <- Ehcs; exact SCS1).
    assert (CFB1 : crange (hcs asegs R HIA h1) FB 256) by (rewrite Ehcs; exact CFB).
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (hm_wlow asegs R HIA h LB LF m H0M) as WL.
    (* [comment removed for export] *)
    destruct sl as [|k0 sl]; [discriminate LSL|]. destruct sl as [|k1 sl]; [discriminate LSL|]. destruct sl as [|k2 sl]; [discriminate LSL|]. destruct sl as [|k3 sl]; [discriminate LSL|].
    destruct sl as [|k4 sl]; [discriminate LSL|]. destruct sl as [|k5 sl]; [discriminate LSL|]. destruct sl as [|k6 sl]; [discriminate LSL|]. destruct sl as [|k7 sl]; [discriminate LSL|].
    destruct sl as [|k8 sl]; [discriminate LSL|]. destruct sl as [|k9 sl]; [discriminate LSL|]. destruct sl as [|k10 sl]; [discriminate LSL|]. destruct sl as [|k11 sl]; [discriminate LSL|].
    destruct sl as [|k12 sl]; [discriminate LSL|]. destruct sl as [|k13 sl]; [discriminate LSL|]. destruct sl as [|k14 sl]; [discriminate LSL|]. destruct sl as [|k15 sl]; [discriminate LSL|].
    destruct sl as [|k16 sl]; [discriminate LSL|]. destruct sl as [|k17 sl]; [discriminate LSL|]. destruct sl as [|k18 sl]; [discriminate LSL|].
    destruct sl; [| discriminate LSL]. cbn [map] in SPILL. clear LSL.
    destruct sl2 as [|k168 sl2]; [discriminate LSL2|]. destruct sl2 as [|k176 sl2]; [discriminate LSL2|]. destruct sl2 as [|k184 sl2]; [discriminate LSL2|].
    destruct sl2 as [|k192 sl2]; [discriminate LSL2|]. destruct sl2 as [|k200 sl2]; [discriminate LSL2|]. destruct sl2 as [|k208 sl2]; [discriminate LSL2|].
    destruct sl2; [| discriminate LSL2]. cbn [map] in SL2C. clear LSL2.
    chunk_split SL2C 4%nat SL2a CZR. replace (sp1 + 168 + 32) with (sp1 + 200) in CZR by (clear; lia).
    apply rw_cells_CB_of in CZR; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in CZR.
    lazymatch type of CZR with rw_cells _ _ _ [CB 16 ?j] => set (jcz := j) in CZR; clearbody jcz end.
    apply (rw_cells_split_CB asegs m1 _ [] 16 jcz [] [8; 4; 4]%nat) in CZR; [| reflexivity]. cbn [mk_CB_cells app] in CZR. cb8_all CZR.
    lazymatch type of CZR with rw_cells _ _ _ [C8 ?a; CB 4 ?b; CB 4 ?c] => set (cz0 := a) in CZR; set (cz1 := b) in CZR; set (czp := c) in CZR; clearbody cz0 cz1 czp end.
    apply (rw_cells_split_CB asegs m1 _ [] 8 jz [] [4; 4]%nat) in JZC; [| reflexivity]. cbn [mk_CB_cells app] in JZC.
    lazymatch type of JZC with rw_cells _ _ _ [CB 4 ?a; CB 4 ?b] => set (jz0 := a) in JZC; set (jz1 := b) in JZC; clearbody jz0 jz1 end.
    unfold DV_FSH0 in FSH. cbn [zcells app] in FSH.
    assert (IND : In (FB + 32, 216) (LB ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWZ : client_wrange L (LB ++ fdata LF1) (arl_stklo R) (htop asegs R HIA h1) (FB + 64) 8) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    (* [comment removed for export] *)
    pose proof (munch_refl [(sp1 + 200, sp1 + 216); (FB + 64, FB + 72)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1s end.
    match goal with H : HM asegs R HIA h1 LB LF1 m1s |- _ => rename H into HH1s end.
    match goal with H : mem_inv asegs m1s |- _ => rename H into MI1s end.
    match goal with H : stk asegs m1s lo sp1 |- _ => rename H into ST1s end.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HP1s.
    ddestruct (dv_TR h1 m1s Ehcs MI1s HP1s) as ([MX1 OX1] & EXT1 & SSH1).
    pose proof (proj1 (Forall_forall _ _) EXT1 dB ESB) as [MB1 OB1].
    dpose (opv_of_mpd h1 LB LF1 m1s dB HH1s MB1 OB1 IB2) as (CBv & OBv & BRv & B8v & EBB & LENB & NB & FBv & SGB).
    rewrite <- BE in CBv, OBv, BRv, B8v. unfold mpi_cells in CBv.
    clear MU WM.
    (* [comment removed for export] *)
    assert (CZ3 : rw_cells asegs m1s (sp1 + 200) (CZC (le_bytes_to_word czp))).
    { pose proof (rw_cells_split_C4 asegs m1s _ [C8 (Z_to_bv 64 (FB + 64))] (Z_to_bv 64 65537) _ CZR) as T22. cbn [app] in T22.
      pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m1s _ [C8 (Z_to_bv 64 (FB + 64)); C2 (Z_to_bv 64 65537); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16))] czp [] T22) as T23. cbn [app] in T23.
      assert (E2 : le2 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1)) by (rewrite !le2_of_Z; rewrite <- (CellsX.Z_to_le_bytes_mod 2 65537); reflexivity).
      assert (E3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) = Z_to_bv 64 1) by (rewrite unsigned_lit by (clear; lia); reflexivity).
      rewrite E3 in T23.
      eapply rw_cells_reshape; [exact T23| |].
      - cbn -[le2 le4 le8]. repeat split; try (rewrite ?length_le2, ?length_le4, ?length_le8; reflexivity).
      - cbn -[le2 le4 le8]. rewrite E2. reflexivity. }
    assert (QB : bytes_at asegs m1s (FB + 64) (u32s [Z_to_bv 64 0])).
    { pose proof JZC as JZ2. chunk_split JZ2 1%nat JZa JZb. clear JZb.
      apply u32arr_ro. eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 0))); [eapply rw_cells_reshape; [exact JZa| cbn; split; [apply (length_le4 (Z_to_bv 64 0))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]. }
    assert (OYZ : aobj asegs AL (hcs asegs R HIA h1) m1s (sp1 + 200) 16).
    { apply (aobj_of_sshad_s (hcs asegs R HIA h1) m1s slo (bv_unsigned sp) (sp1 + 200) 1 CSOK1 SSH1);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCS1| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    assert (OQZ : aobj asegs AL (hcs asegs R HIA h1) m1s (FB + 64) 4).
    { eapply (A_mpi_cmp_int.aobj_of_partial_ci asegs AL (hcs asegs R HIA h1) m1s FB _ (FB + 64) 8%nat 4);
        [exact CSOK1| exact FSH| eapply crange_sub; [exact CFB1| clear; lia| clear; lia]| exact FB8| clear - F0 F1 FBLO; lia| clear; lia| clear; lia| reflexivity]. }
    assert (BS : md_addr dB + 16 <= lo \/ sp1 <= md_addr dB).
    { pose proof (proj1 (Forall_forall _ _) ESF dB ESB) as (_ & _ & K & _). destruct K as [K|K]; [left; exact K| right; clear - K SP1; lia]. }
    dpose OB as (OB1' & OB2' & OB3' & OB4' & OB5').
    assert (BPS : 1 <= md_n dB -> md_p dB + 4 * md_n dB <= lo \/ sp1 <= md_p dB).
    { intros N1. assert (NN : md_own dB <> LNull).
      { intros EO. pose proof MB1 as [(_ & _ & _ & _ & _ & OWB) _]. rewrite EO in OWB. simpl in OWB. destruct OWB as [_ N0]. clear - N0 N1. lia. }
      destruct (OB5' NN) as [K|K]; [left; exact K| right; clear - K SP1; lia]. }
    assert (BP4 : md_n dB = 0 \/ 0 < md_p dB /\ md_p dB mod 4 = 0).
    { pose proof MB1 as [(_ & _ & _ & _ & _ & OWB) _]. destruct (md_own dB) eqn:EO.
      - left. destruct OWB as [_ N0]. exact N0.
      - right. ddestruct OWB as (N1 & IN & P16 & UA). split; [exact (proj1 (FBv N1))| clear - P16; Z.div_mod_to_equations; lia].
      - right. ddestruct OWB as (N1 & P4 & P0 & BY & RO). split; [clear - P0; lia| clear - P4; Z.div_mod_to_equations; lia]. }
    pose proof CMPR as CMPc. unfold A_mpi_cmp_mpi_raw.mpi_cmp_mpi_raw_stmtA, A_mpi_cmp_mpi.A_MPI_CMP_MPI_E in CMPc.
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { try unfold A_mpi_cmp_mpi.A_MPI_CMP_MPI_E.
      eapply CMPc with (CS := hcs asegs R HIA h1) (X := B) (P := md_p dB) (n := md_n dB) (sg := md_sg dB) (xs := md_limbs dB) (pad := md_pad dB)
                       (Y := sp1 + 200) (Q := FB + 64) (n' := 1) (sg' := 1) (ys := [Z_to_bv 64 0]) (pad' := le_bytes_to_word czp) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact CBv | exact EBB | exact LENB | exact NB | exact SGB | exact BP4 | exact B8v | exact CZ3 | exact QB
              | exact MI1s | exact (art_alwf asegs R HIA) | exact CSOK1 | exact (hm_abase asegs R HIA h1 LB LF1 m1s HH1s)
              | exact OBv | exact OYZ | (intros N1; exact (proj2 (FBv N1))) | (intros _; exact OQZ) | exact ST1s
              | exact BS | exact BPS | (rewrite BE; exact BS) | (clear - SP1R; lia)
              | (rewrite BE; pose proof MB1 as [(_ & _ & B0q & _) _]; exact B0q)
              | (clear - LOS ALO ACP; lia)
              | (clear - SLO SP1 NEEDR; lia)
              | (clear - SP1M; Z.div_mod_to_equations; lia)
              | (eapply crange_sub; [exact SCS1| clear; lia| clear - SP1; lia])
              | (right; clear; lia)
              | (left; reflexivity)
              | (right; split; [clear - F0 F1 FBLO; lia| clear - F64; Z.div_mod_to_equations; lia])
              | (intros _; left; clear - FBLO; lia)
              | reflexivity
              | (clear; lia)
              | (f_equal; clear; lia)
              | match goal with |- ?g => idtac "CMPR-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold A_mpi_cmp_mpi.mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (HH2 : HM asegs R HIA h1 LB LF1 m2).
    { eapply (hm_munch asegs R HIA h1 LB LF1 [(lo, sp1)] m1s m2 HH1s MU2 WM2). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      intros xa Hxa. left. left. rewrite ET1. clear - Hxa LOS SP1 TOP. lia. }
    assert (PRES2 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m2).
    { eapply presW_munch; [exact PRES| exact MU2| exact WM2| |].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]| apply Forall_nil].
      - apply Forall_cons; [cbn [fst snd]; eapply wcover_of_wlow; [exact WL| clear - ALO LOS; lia| clear - SP1; lia]| apply Forall_nil]. }
    clear HH1s PRES HP1s MX1 OX1 EXT1 MB1 OB1 SSH1 OYZ OQZ QB.
    transport_after_call asegs m1s m2 MU2 WM2.
    (* [comment removed for export] *)
    clear MU2 WM2. assert (INF : In (FB, 256) LF1) by (left; reflexivity).
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 32)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H end.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA h1 LB LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    assert (FSH3 : rw_cells asegs m3 (Z.shiftr FB 3 + al_sb AL) DV_FSH) by (unfold DV_FSH; cbn [zcells app]; exact FSH).
    clear FSH MU WM.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    lazymatch goal with |- context [Z_to_bv 64 (Z.sgn ?v)] => destruct (Z.sgn_spec v) as [(KS & ->)|[(KS & ->)|(KS & ->)]] end.
    2: { (* [comment removed for export] *)
      zstep. zstep. zstep.
      assert (STall : stk asegs m3 lo (bv_unsigned sp + -104)).
      { pose proof (stk_of_rw_cells asegs m3 _ _ SPILL) as K1. cbn [cells_size csize Nat.add] in K1.
        pose proof (stk_of_rw_cells asegs m3 _ _ SP152) as K2. cbn [cells_size csize Nat.add] in K2.
        pose proof (stk_of_rw_cells asegs m3 _ _ SL2a) as K3. cbn [cells_size csize Nat.add] in K3.
        pose proof (stk_of_rw_cells asegs m3 _ _ CZ3) as K4. cbn [cells_size csize Nat.add] in K4.
        change (Z.of_nat 152) with 152 in K1. change (Z.of_nat 16) with 16 in K2, K4. change (Z.of_nat 32) with 32 in K3.
        replace (sp1 + 152 + 16) with (sp1 + 168) in K2 by (clear; lia). replace (sp1 + 168 + 32) with (sp1 + 200) in K3 by (clear; lia).
        replace (sp1 + 200 + 16) with (sp1 + 216) in K4 by (clear; lia).
        eapply (stk_merge asegs); [| exact SThi| clear - SP1 LOC; lia].
        eapply (stk_merge asegs); [| exact K4| clear - SP1 LOC; lia].
        eapply (stk_merge asegs); [| exact K3| clear - SP1 LOC; lia].
        eapply (stk_merge asegs); [| exact K2| clear - SP1 LOC; lia].
        eapply (stk_merge asegs); [exact ST3| exact K1| clear - SP1 LOC; lia]. }
      eapply C_EPI0 with (r := -12); try eassumption; try (clear; lia).
      destruct XW as [CW _]. intros xa Hxa. destruct (CW xa Hxa) as [K|[K|K]]; [left; clear - K LOC CSP; lia| right; left; exact K| right; right; exact K]. }
    (* [comment removed for export] *)
    all: zstep.
    all: assert (VB : 0 < mpd_abs dB) by (rewrite (mpd_abs_lval dB LENB); pose proof (lval_range (md_limbs dB) (md_n dB) ltac:(clear - NB; lia)) as LR;
                                         assert (LZ : lval [Z_to_bv 64 0] 1 = 0) by reflexivity; rewrite LZ in KS; (* [comment removed for export] *)
                                         destruct SGB as [SG|SG]; rewrite SG in KS; clear - KS LR; lia).
    all: eapply (dv_INIT h1 m3 j1 j2 jz1 jx jy jt jp jq (le_bytes_to_word czp) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k168 k176 k184 k192); try eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Fr.
  End Call.
End WalkS.
