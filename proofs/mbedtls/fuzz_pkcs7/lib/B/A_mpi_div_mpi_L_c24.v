(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_lset P_mpi_mul_int_W P_mpi_div_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_core_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA A_mpi_cmp_int A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24 A_mpi_div_mpi_M_c24 A_mpi_lset A_mpi_lset_ng A_mpi_mul_int A_mpi_mul_int_stmtV A_mpi_mul_int_ng A_mpi_cmp_mpi_raw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_shift_l_c24 A_mpi_add_sub_sz_c24 A_mpi_add_sub_o_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
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
Local Ltac2 dv_zcl_rel (t : Init.constr) heads : Init.bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f a => if Int.equal (Array.length a) 2 then List.exist (fun h => Constr.equal f h) heads else Init.false
  | _ => Init.false
  end.
Local Ltac2 dv_zcl_eqZ (t : Init.constr) : Init.bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f a =>
      if Int.equal (Array.length a) 3 then (if Constr.equal f constr:(@eq) then Constr.equal (Array.get a 0) constr:(Z) else Init.false) else Init.false
  | _ => Init.false
  end.
Local Ltac2 dv_zcl_keep (t : Init.constr) : Init.bool :=
  if dv_zcl_rel t [constr:(Z.lt); constr:(Z.le); constr:(Z.gt); constr:(Z.ge)] then Init.true
  else if dv_zcl_eqZ t then Init.true
  else match Constr.Unsafe.kind t with
       | Constr.Unsafe.App f a =>
           if Int.equal (Array.length a) 2 then
             (if Constr.equal f constr:(and) then
                (if dv_zcl_rel (Array.get a 0) [constr:(Z.le); constr:(Z.lt)] then dv_zcl_rel (Array.get a 1) [constr:(Z.le); constr:(Z.lt)] else Init.false)
              else Init.false)
           else if Int.equal (Array.length a) 1 then
             (if Constr.equal f constr:(not) then dv_zcl_eqZ (Array.get a 0) else Init.false)
           else Init.false
       | _ => Init.false
       end.
Local Ltac2 dv_zcl () : Init.unit :=
  let cands := List.fold_left (fun acc h =>
      let (id, _, ty) := h in
      if dv_zcl_keep ty then acc
      else if Constr.equal (Constr.type ty) constr:(Prop) then id :: acc else acc) [] (Control.hyps ()) in
  match cands with
  | [] => ()
  | _ :: _ =>
      match Control.case (fun () => Std.clear cands) with
      | Init.Val _ => ()
      | Init.Err _ =>
          let rec loop ids :=
            let rest := List.filter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => Init.false | Init.Err _ => Init.true end) ids in
            if Int.equal (List.length rest) (List.length ids) then () else loop rest in
          loop cands
      end
  end.
Local Ltac zchk_clear ::= ltac2:(Control.enter (fun () => dv_zcl ())).

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
  Definition DV_FSHq (j : nat) : list cell := firstn j DV_FSH ++ C1 (Z_to_bv 8 4) :: skipn (S j) DV_FSH.

  (* [comment removed for export] *)
  Hypothesis COPYX : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.
  Hypothesis LSETNG : mpi_lset_ng_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MULNG : mpi_mul_int_ng_stmtA asegs R HIA A_MPI_MUL_INT.
  Hypothesis MULI : mpi_mul_int_stmtA_v asegs R HIA A_MPI_MUL_INT.   (* [comment removed for export] *)
  Hypothesis CMPR : mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L66117246296.10100000OS2LF2ra2sp3LFB2FB3sp14gapn2PF1n". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma dvVr_S : forall n, dvVr (S n) = dvVrnd + dvVr n.
  Proof. intros n. unfold dvVr. rewrite Nat2Z.inj_succ. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L48078396760.10100000OS2LF2ra2sp3LFB2FB3sp14gapn2FF1n". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12128799109.1 L19980016842.7 L28275246517.6 L33860051774.2 L39261961171.9 L39272446419.9 L41650118032.6 L4781719053.2  L52101693566.17L62037211595.7 L6203936179.1  L66151427842.16L66668349941.1 L9356559676.11 L9838743115.2  00000300K00`00h01F01e02902?03;03V03[04704:04e04oS1fS1R3HIA1h2sp3TOP3sp13SP1S1R2sp2lo3SLO3sp13SP1S2dl3VIIS1R3HIA1h4PHIb3BUD2hq1v2HV3HVqS1R3HIA1h3FRb4BUDF2hq1f2HF4HFRqS1R2FB2dl3DIF3ALO2F1S1d2D0S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2dl3DIF3ALO2F11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1vS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L18359781713.10L19980016842.7 L20803336933.11L25148064707.3 L28275246517.6 L35590224338.3 L4223562214.6  L4781719053.2  L52101693566.17L60162046265.6 L62037211595.7 L6203936179.1  L66151427842.16L9356559676.11 L9838743115.2  00000Q00i01M01X01m02802L02R03N03b04=04B04^05I05SS1R3HIA1h1d3FRb4BUDF2hq1f2HF4HFRqS1R3HIA1h2sp3TOP3sp13SP1S1R3HIA1h4PHIb3BUD2hq1v2di2dj2HV3HVqS2di2dj3VJIS1R2sp2lo3SLO3sp13SP1S2di2dj3VIJS1R2FB2dj3DJF3ALO2F1S1d2D0S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS1R2FB2di3DIF3ALO2F1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L18359781713.10L19980016842.7 L25148064707.3 L31667811433.11L35590224338.3 L4223562214.6  L4781719053.2  L50313707442.2 L52101693566.17L60162046265.6 L6188244917.6  L62037211595.7 L6203936179.1  L66151427842.16L9356559676.11 L9838743115.2  00000Q00i01401X01c02702=02E03A03U03j04E04J04f05Q05[S1R3HIA1h1d3FRb4BUDF2hq1f2HF4HFRqS1R3HIA1h2sp3TOP3sp13SP1S2di2dj3VJIS1R3HIA1h4PHIb3BUD2hq1v2di2dj2HV3HVqS2di2dj3VIJS1R2FB2dj3DJF3ALO2F1S1d2D0S2di3VIIS1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq2di3DIF3ALO2F11a2HaS1R2FB2di3DIF3ALO2F1S1R2sp2lo3SLO3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS3sp14SP1R". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L10596430123.1 L18605071746.9 L24345703806.0 L2599671991.9  L27364772610.0 L27940405558.7 L29428324939.5 L31034375991.6 L31250592023.1 L31775652143.1 L32454903270.1 L35663928186.7 L36415413615.1 L38235734261.1 L39168071816.4 L39983567983.1 L4240581564.11 L44491235046.1 L44994687875.4 L47177391087.8 L48205731887.1 L52880146305.11L53035543507.6 L5413320392.1  L54523052982.7 L60098763854.3 L62018535662.1 L6203936179.1  L62096378824.1 L66151427842.16L67283817515.1 L776496616.3   L829317888.2   L831182850.7   L9080220944.4  L9356559676.11 L9631767084.2  L9631865001.9  00000400500600Z00[01601H01[01_01c01g02<02@02D02Q02U03;03?03N03h03l04Q04f04k05F05P05S05X05]06M06Q06]06g07A07P08;08B08CS2FBSSS1R5NEEDR2sp2lo3SLO3sp13SP13slo4SLO2SS1R5NEEDR2sp2lo3SLO3sp13SP1S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp3TOP2HTS2diS2FBS2FBS1R3HIA1h2sp2lo3TOP1HS2FBS2loS2FB1q2F03QLOS2FBS2FB2di2F02S11R2lo3LOS3sp13LOC3ALO3ACPS2FBS2sp2lo3sp13SP1S1R2lo3LOS2FB1q3ALO2F13QHIS2FBS1R3HIA1h2sp2lo3LOS3TOP3sp13SP12xa2HxS1R2lo3LOS2di3ALO3PICS3sp1S1R5NEEDR2sp2lo3SLO3sp13SP1S1R2lo3LOSS1RS3sp1S3sp1S3sp12r04SP1M1q1r1H2H02q02H42FB3F642di3P162QM2q1S2FBS2sp3sp13SP1S3sp14SP1RS1R2lo3LOS3sp13LOC3ALO3ACPS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2FB2F0F". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 SP1M F64 FRSH CFB ESF LOC CSP FN64 CMPR slo SLO1 SLO2 SSH0"] Lemma call_cmp0_l :
    forall mq hq LBq ls c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czpad gb z32 z48 z64 u0 u1 u2 jq
           v f i di (j : nat) (q : Z) (retpc : Z)
           t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX
         (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZCp (Z_to_bv 64 q) czpad) gb z32 z48 z64 u0 u1 u2 jq)
         (DV_FSHq j) v f ->
    nth_error ls i = Some di -> md_own di = LHeap ->
    (q = FB + 32 /\ j = 4%nat /\ firstn 4 z32 = repeat (Z_to_bv 8 0) 4) \/ (q = FB + 48 /\ j = 6%nat /\ firstn 4 z48 = repeat (Z_to_bv 8 0) 4) ->
    0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (sp1 + 200) ->
    (forall m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m2 hq LBq ls dX
            (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZCp (Z_to_bv 64 q) czpad) gb z32 z48 z64 u0 u1 u2 jq)
            (DV_FSHq j) v f ->
       (UWCD mq -> UWCD m2) ->
       aevtA asegs (KF asegs R HIA hq mo0) POSTD
         (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0' t1' t2' sp (Z_to_bv 64 sp1)
                  (Z_to_bv 64 (Z.sgn (md_sg di * lval (md_limbs di) (md_n di)))) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (Z_to_bv 64 retpc) fc None m2 (seg_rom asegs))) ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0v a1v a2 a3 a4 a5 a6 a7
               s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (Z_to_bv 64 A_MPI_CMP_MPI_E) fc None mq (seg_rom asegs)).
  Proof.
    intros until t6. intros CST NI OI QJ RPC RPE -> -> K. rt_facts. dpose FRSH as (F0 & F1 & F2 & F3).
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
    apply Forall_cons_iff in CHq'. destruct CHq' as [CZC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z32C CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z48C CHq'].
    clear CHq' SPC T2Cq ZCq GAPC SAVE FHD.
    cbn [fst snd] in CZC, Z32C, Z48C.
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & _ & _ & _ & _ & HFI & SLI & _ & ASI & OI'); try eassumption.
    assert (XP : 0 < md_addr di) by (unfold A_mpi_client2.struct_locA in SLI; destruct SLI as [[S1 _]|[S1 _]]; clear - S1 F0 LOS ALO ACP LOC; lia).
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _).
    dpose (S_opv_of_mpd hq LBq LF1 mq di HHq MI OI' ltac:(intros EO; exfalso; exact (NSI EO))) as (CI & _ & _ & I8 & BYI & LENI & NRI & PAI & SGI).
    unfold mpi_cells in CI.
    assert (OCZ : aobj asegs AL (hcs asegs R HIA hq) mq (sp1 + 200) 16).
    { apply (S_aobj_of_sshad (hcs asegs R HIA hq) mq slo (bv_unsigned sp) (sp1 + 200) 1 CSOKq SSHq);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCSq| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    assert (QX : aobj asegs AL (hcs asegs R HIA hq) mq q 4 /\ bytes_at asegs mq q (u32s [Z_to_bv 64 0]) /\ FB + 32 <= q /\ q + 8 <= FB + 64 /\ q mod 8 = 0).
    { destruct QJ as [(-> & -> & ZQ) | (-> & -> & ZQ)].
      - split; [| split; [| split; [clear; lia| split; [clear; lia| clear - F64; Z.div_mod_to_equations; lia]]]].
        + eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB (DV_FSHq 4) (FB + 32) 4 4 CSOKq SHq);
            first [ reflexivity | (eapply crange_sub; [exact CFBq| clear; lia| clear; lia]) | (clear - F64; Z.div_mod_to_equations; lia) | (clear - F0; lia) | (clear; lia) ].
        + destruct Z32C as [[_ BZ] _]. cbn [cells_bytes cbytes] in BZ. rewrite app_nil_r in BZ.
          rewrite <- (firstn_skipn 4 z32), ZQ in BZ. apply bytes_at_app in BZ. destruct BZ as [BZ _].
          eapply bytes_at_ext; [exact BZ| exact (eq_sym (u32s_repeat0 1))].
      - split; [| split; [| split; [clear; lia| split; [clear; lia| clear - F64; Z.div_mod_to_equations; lia]]]].
        + eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB (DV_FSHq 6) (FB + 48) 6 4 CSOKq SHq);
            first [ reflexivity | (eapply crange_sub; [exact CFBq| clear; lia| clear; lia]) | (clear - F64; Z.div_mod_to_equations; lia) | (clear - F0; lia) | (clear; lia) ].
        + destruct Z48C as [[_ BZ] _]. cbn [cells_bytes cbytes] in BZ. rewrite app_nil_r in BZ.
          rewrite <- (firstn_skipn 4 z48), ZQ in BZ. apply bytes_at_app in BZ. destruct BZ as [BZ _].
          eapply bytes_at_ext; [exact BZ| exact (eq_sym (u32s_repeat0 1))]. }
    destruct QX as (OQ & BYQ & QLO & QHI & QM).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { pose proof CMPR as SPEC. unfold mpi_cmp_mpi_raw_stmtA, A_MPI_CMP_MPI_E in SPEC. unfold A_MPI_CMP_MPI_E.
      eapply SPEC with (CS := hcs asegs R HIA hq) (lo := lo) (X := md_addr di) (P := md_p di) (n := md_n di) (sg := md_sg di) (xs := md_limbs di) (pad := md_pad di)
                       (Y := sp1 + 200) (Q := q) (n' := 1) (sg' := 1) (ys := [Z_to_bv 64 0]) (pad' := czpad);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact CI | exact BYI | exact LENI | exact NRI | exact SGI | exact I8 | exact CZC | exact BYQ | exact MIq | exact OI' | exact OCZ | exact STq | exact CSOKq | reflexivity
              | exact (art_alwf asegs R HIA) | exact (hm_abase asegs R HIA hq LBq LF1 mq HHq)
              | (intros _; exact OQ) | (intros N1; exact (proj2 (PAI N1)))
              | (eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia])
              | (destruct ASI as [KK|KK]; [left; exact KK| right; exact KK])
              | lazymatch goal with
                | |- md_n di = 0 \/ _ => right; split; [exact PI0| pose proof MI as [(_ & _ & _ & _ & _ & OWN) _]; rewrite OI in OWN; ddestruct OWN as (_ & _ & P16 & _); clear - P16; Z.div_mod_to_equations; lia]
                | |- 1 = 0 \/ _ => right; split; [clear - F0 QLO; lia| clear - QM; Z.div_mod_to_equations; lia]
                | |- 1 = 1 \/ _ => left; reflexivity
                | |- 0 <= 1 <= _ => clear; lia
                | |- (sp1 + 200) mod 8 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 + 200 + 16 <= lo \/ _ => right; clear; lia
                | |- 1 <= md_n di -> _ => intros _; left; clear - PIC ALO LOS; lia
                | |- 1 <= 1 -> _ => intros _; left; clear - F1 ALO LOS QHI; lia
                | |- 0 <= lo => clear - LOS ALO ACP; lia
                | |- lo <= sp1 - _ => clear - SLO SP1 NEEDR; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < md_addr di => exact XP
                | |- 0 < sp1 + _ => clear - LOC LOS ALO ACP; lia
                end
              | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "CMP0-PRE-LEFT:" g end ] ]. }
    cbv beta. intros ms' PO. unfold mpi_cmp_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [exact RPC| exact RPE]).
    assert (LV0 : lval [Z_to_bv 64 0] 1 = 0) by exact (lval_repeat0_app 1 [] 1 ltac:(clear; lia)).
    replace (md_sg di * lval (md_limbs di) (md_n di) - 1 * lval [Z_to_bv 64 0] 1) with (md_sg di * lval (md_limbs di) (md_n di)) by (rewrite LV0; clear; lia).
    lazymatch type of MU2 with munch _ _ ?mx => first [rename mx into m2 | set (m2 := mx) in *] end.
    assert (FB8q : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (HH2 : HM asegs R HIA hq LBq LF1 m2).
    { eapply (hm_munch asegs R HIA hq LBq LF1 [(lo, sp1)] mq m2 HHq MU2 WM2). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      intros xa Hx. left. left. rewrite HTq. clear - Hx LOS SP1 TOP. lia. }
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [] mq m2).
    { eapply (presA_drop_below asegs R HIA hq LBq LF1 _ lo sp1 mq mq m2 sp1 HHq); [| clear; lia| clear - LOS; lia].
      eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq ls dX
             (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad (CZCp (Z_to_bv 64 q) czpad) gb z32 z48 z64 u0 u1 u2 jq)
             (DV_FSHq j) v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := []); try eassumption; [apply Forall_nil|].
      apply Forall_forall. intros ac _. exact I. }
    eapply K; [exact CST2|].
    intros UW. eapply M_uwcd_munch; [exact UW| exact MU2|]. apply Forall_cons; [cbn [snd]; clear; lia| apply Forall_nil].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0?L12789385789.6 L17762320911.2 L27940405558.7 L29428324939.5 L31034375991.6 L34979112605.7 L35663928186.7 L3618068308.1  L38235734261.1 L38551529394.0 L39268637205.0 L39332637397.0 L39686831147.1 L4240581564.11 L44571603816.1 L49118974339.4 L51005809078.7 L51725509627.1 L53035543507.6 L55311226528.1 L60098763854.3 L62335543678.0 L65614147016.1 L66038874368.2 L66049669634.7 L66151427842.16L67806095031.9 L67883417576.3 L9080220944.4  L9122136456.2  L9356559676.11 L9631767084.2  00000D00K00f01801K01f02;02?02C02D02E02F02J03003403C03^03b04704;04E04F04K04U04o05Y06=06I06X06^07I07PS1R2lo3LOS2FB3ALO2F1S2FB2F0S1R5NEEDR2sp2lo3SLO3sp13SP1S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp3TOP2HTS1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h2sp2lo3TOP1HS2FBS2loSSSS2FBS2FB2di2F02S11R2lo3LOS3sp13LOC3ALO3ACPS2FBS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3SLO3sp13SP1S2FBS1R2lo3LOS2di3ALO3PICS2FBS1R2lo3LOSSS3sp1S3sp14SP1RS1R2lo3LOS3sp13LOC3ALO3ACPS3sp12r04SP1M1q1r1H2H02q02H42FB3F642di3P16S1R5NEEDR2sp2lo3SLO3sp13SP13slo4SLO2S2sp3sp13SP1S2sp2lo3sp13SP1S1j2HjS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2FB2F0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 SP1M F64 FRSH CFB ESF LOC CSP FN64 CMPR slo SLO1 SLO2 SSH0"] Lemma call_cmpraw :
    forall mq hq LBq ls c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq
           v f i di (retpc : Z)
           t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6,
    CSTA mq hq LBq ls dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    nth_error ls i = Some di ->
    md_own di = LHeap -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
    a0v = Z_to_bv 64 (md_addr di) -> a1v = Z_to_bv 64 (sp1 + 168) ->
    (forall m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       CSTA m2 hq LBq ls dX (DCSM c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 t2pad czc gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
       (UWCD mq -> UWCD m2) ->
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
    apply Forall_cons_iff in CHq'. destruct CHq' as [CZC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [GAPC CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [SAVE CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [FHD CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z32C CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [Z48C CHq'].
    apply Forall_cons_iff in CHq'. destruct CHq' as [Z64C CHq']. apply Forall_cons_iff in CHq'. destruct CHq' as [TPC CHq'].
    clear CHq' SPC ZCq CZC GAPC SAVE FHD Z32C Z48C Z64C.
    cbn [fst snd] in T2Cq, TPC.
    edestruct K_local_facts with (mq := mq) (i := i) (d := di) as (MI & NSI & _ & _ & _ & _ & HFI & SLI & _ & ASI & OI'); try eassumption.
    assert (XP : 0 < md_addr di) by (unfold A_mpi_client2.struct_locA in SLI; destruct SLI as [[S1 _]|[S1 _]]; clear - S1 F0 LOS ALO ACP LOC; lia).
    ddestruct (HFI OI) as (PI0 & PIC & INI & N1I & _).
    dpose (S_opv_of_mpd hq LBq LF1 mq di HHq MI OI' ltac:(intros EO; exfalso; exact (NSI EO))) as (CI & _ & _ & I8 & BYI & LENI & NRI & PAI & SGI).
    unfold mpi_cells in CI.
    assert (OT2 : aobj asegs AL (hcs asegs R HIA hq) mq (sp1 + 168) 16).
    { apply (S_aobj_of_sshad (hcs asegs R HIA hq) mq slo (bv_unsigned sp) (sp1 + 168) 1 CSOKq SSHq);
        [clear - SLO2 SLO SP1 NEEDR; lia| cbn; clear - SP1; lia| clear - SP1M; Z.div_mod_to_equations; lia| clear - SP1R; lia|].
      eapply crange_sub; [exact SCSq| clear - SLO SP1 NEEDR; lia| cbn; clear - SP1; lia]. }
    assert (OTP : aobj asegs AL (hcs asegs R HIA hq) mq (FB + 176) 12).
    { replace 12 with (8 + 4) by reflexivity. apply C_aobj_merge; [clear; lia| clear; lia| |].
      - eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 176) 22 1 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| reflexivity|].
        intros j Hj. assert (j = 0%nat) as -> by (clear - Hj; lia). reflexivity.
      - eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 176 + 8) 23 4 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    assert (BYT : bytes_at asegs mq (FB + 176) (u32s [u0; u1; u2])) by (destruct TPC as [[_ KK] _]; exact KK).
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { pose proof CMPR as SPEC. unfold mpi_cmp_mpi_raw_stmtA, A_MPI_CMP_MPI_E in SPEC. unfold A_MPI_CMP_MPI_E.
      eapply SPEC with (CS := hcs asegs R HIA hq) (lo := lo) (X := md_addr di) (P := md_p di) (n := md_n di) (sg := md_sg di) (xs := md_limbs di) (pad := md_pad di)
                       (Y := sp1 + 168) (Q := FB + 176) (n' := 3) (sg' := 1) (ys := [u0; u1; u2]) (pad' := t2pad);
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
                | |- (sp1 + 168) mod 8 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 + 168 + 16 <= lo \/ _ => right; clear; lia
                | |- 1 <= md_n di -> _ => intros _; left; clear - PIC ALO LOS; lia
                | |- 1 <= 3 -> _ => intros _; left; clear - F1 ALO LOS; lia
                | |- 0 <= lo => clear - LOS ALO ACP; lia
                | |- lo <= sp1 - _ => clear - SLO SP1 NEEDR; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- 0 < md_addr di => exact XP
                | |- 0 < sp1 + _ => clear - LOC LOS ALO ACP; lia
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
  Local Notation DCSOb c0 c8 c16 c48 c80 c120 ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq :=
    (DCSM c0 c8 c16 (Z_to_bv 64 65537) (Z_to_bv 64 4294967295) (Z_to_bv 64 (Z.lxor ny 18446744073709551615)) c48
          (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 48)) (Z_to_bv 64 (2 ^ 61)) c80 (Z_to_bv 64 ((ny - 2) * 4))
          (Z_to_bv 64 ((ny - 1) * 4)) (Z_to_bv 64 (ny - 1)) (Z_to_bv 64 k) c120
          t2pad (CZCp czp czpad) gb z32 z48 z64 u0 u1 u2 jq).

  (* [comment removed for export] *)
  Definition linvk (kx : Z) (dLX dY dZ dT : mpd) (i ny : Z) : Prop :=
    md_addr dLX = FB + 80 /\ md_addr dY = FB + 112 /\ md_addr dZ = sp1 + 184 /\ md_addr dT = FB + 144
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
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c48 c80 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 c48 c80 c120 ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny + 1 <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvVr n <= PHIb -> f + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 (Z_to_bv 64 (i + 1)) t2 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fb44) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition dvL5_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c80 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) c80 c120 ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linvk (2 * (i - ny)) dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 -> v + dvVr n <= PHIb -> f + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0xa018c) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L13270049643.9  L27515139277.9  L31813027332.6  L32867401788.215L33323923983.9  L3482964649.9   L3798149545.7   L42967147320.215L49000787209.4  L61436909883.2  L64503042233.6  L8632193901.1   L9356559676.11  Q12388912010.216Q1433360151.216 Q15022709143.216Q20537614359.216Q3853489290.216 Q58026207754.21600000;00E00Z01_01`01i02:03?03J03P03b03e04P05105U06906]07>07_S3dLX1i3IXLS2dA1i3INAS2dA1i2ny3NY13NYI3INAS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX1i2ny3NY13NYI3INA4NA983SPR2F04SP1RFS1i2ny2KBS3FRb2FF1n1f2HF1HS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX1i2ny3NY13NYI3INA4NA983SPR2F04SP1RS1n1i2ny2RNS1i2nyS4PHIb2PF1n1v2HV1HS1iS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M D0 SP1 GAP FRSH CFB LOC KFIN"] Lemma dv_L5 : forall n, dvLH_stmt n -> dvL5_stmt n.
  Proof.
    intros n KH. unfold dvL5_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. kit_chunks CHq.
    ddestruct LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L39728673364.3 L41019279709.3 L49849232497.13L59529426586.3 L62018535662.1 L9356559676.11 00000<00H01:01F01I024S2dl3idx3IDXS2dl3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dl3idx3IDX3ALO3PLCS2dl3idx3IDXS1RS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPR". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L67741340990.10300000OS2LF2ra2sp3LFB2FB3sp14gapn2dy1H". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma cp_cap : forall dy, 0 <= md_n dy <= MPI_MAX_LIMBS -> copy_PHI dy <= dvcCP.
  Proof. intros dy H. unfold copy_PHI, dvcCP, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L45148039480.10400000OS2LF2ra2sp3LFB2FB3sp14gapn2dy1H". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma mul_cap : forall dt dy, 0 <= md_n dy <= MPI_MAX_LIMBS -> mul_int_PHI dt dy <= dvcMUL.
  Proof. intros dt dy H. unfold mul_int_PHI, copy_PHI, dvcMUL, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L49429103922.10500000VS2LF2ra2sp3LFB2FB3sp14gapn2dx2dt2H12H2". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma as_cap : forall dx dt, 0 <= md_n dx <= MPI_MAX_LIMBS -> 0 <= md_n dt <= MPI_MAX_LIMBS -> add_sub_PHI dx dx dt <= dvcAS.
  Proof. intros dx dt H1 H2. unfold add_sub_PHI, A_mpi_add_abs_W.add_abs_PHI, dvcAS, grow_PHI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L22712702117.107L40881342907.107L41997743205.107L53427879150.106L67536571068.10500000Y01>01g02I02iS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2Hc2Hn3BLRS2LF2ra2sp3LFB2FB3sp14gapn1c2dl3BLR1HS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2Hc2Hn3BLRS2LF2ra2sp3LFB2FB3sp14gapn1c2dl2SNS2LF2ra2sp3LFB2FB3sp14gapn2dl2Hn". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L26523304876.10100000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
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
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 ((i - ny) * 32)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linvk (2 * (i - ny) + 1) dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + (dvcCP + dvcSHL + dvcAS) + dvVr n <= PHIb -> f + (copy_FR 0 + shift_l_FR + add_sub_FR (d + 1)) + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0114) fc None mq (seg_rom asegs)).

  Ltac l4_cond :=
    repeat match goal with
           | |- context [Z.ltb ?a ?b] =>
               first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia)
                     | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ]
           end;
    cbv [Z.b2z]; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l;
    unfold_cond; fold_lit_ux;
    repeat match goal with
           | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
           end;
    solve_cond_rec.
  Ltac l4_nf :=
    lazymatch goal with
    | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xa03b8 else _) _ _ _ _) => replace c with false; [cbv_concl_iota| symmetry; l4_cond]
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01W0@C7096915042.401 D33876909647.400D63873442836.400K21870859916.402K22945712379.402K66327680928.401L10041968289.0  L12469921329.0  L12861988900.9  L14447101554.5  L14794338612.5  L14820281134.10 L16000728743.6  L1685717371.0   L18357479357.11 L1855173106.9   L19133426325.6  L21868076544.5  L22938730615.5  L23524570067.14 L25095893474.13 L26845910153.2  L27109749153.0  L29832375856.1  L29956516996.0  L31527751786.6  L31942703947.393L32172768967.389L32172768967.393L32284259785.0  L32532556920.4  L33324104207.7  L34860304136.6  L36508794932.6  L40066488116.5  L42816623016.8  L46190619535.390L47314679148.11 L48222540875.393L51158826717.16 L52428691159.8  L53518944813.389L53609733305.393L53618266946.2  L54060558805.11 L5605601736.8   L57652312495.1  L59310648043.7  L59667784614.1  L6178369912.3   L61798049332.5  L63343663265.0  L63650381673.14 L63885703535.393L65252552111.1  L66084005463.13 L66084350309.14 L66330468140.4  L67345532263.10 L7735389571.5   L8045422791.2   L8532400182.5   L8820192273.7   L8929159528.392 L8929620893.389 L8929620893.393 L9356559676.11  L9931879857.7   P14461423358.402P14783166904.402P36523116728.402P40077402040.402P61800574648.402P66327680928.401P7750690063.402 Q10812129647.396Q11801279589.400Q12388912010.393Q19991027068.402Q20537614359.393Q24841257623.393Q26295627581.396Q33874924623.401Q33877164610.396Q33889765055.396Q38966708490.393Q41261544093.275Q45539900993.402Q45989664010.393Q48467890406.402Q49698585326.400Q50458135125.396Q51120983794.396Q51135677050.399Q51337909069.393Q63871233556.401Q63873185817.396Q63883819088.396Q63885703535.393Q63885753572.396Q67304644247.393Q7368569088.275 Q8943555749.393 00000101G02W03X04Y04Z04[04\05505605705T05i05j06Q06n07D07E07F08608d08j08k08o09009>0:40;Q0=20=30=@0=V0=m0=n0=o0>M0??0?e0A20Aj0B@0Bn0Bo0C70CZ0D30D70DQ0DU0D_0D`0Da0EN0F[0F_0GH0H40H50HV0HW0H]0Hn0IH0Jc0L>0M_0NJ0Nd0P@0Q\0S80TT0V00V10WE0X80X`0YP0YQ0ZD0[70[\0\R0]E0^80^h0_R0_S0`C0`D0aA0af0bW0cH0d;0dk0eX0fE0g20g_0hR0i90i^FS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY13INA2NZ3idx2wv2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY13idx2wv2Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wv3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wv3PZF3IDXFSFS1d3FRb2FF1n1f2HF3FN33FRGFFS1d3FRb2FF1n1f2HF3FN23FN33FRGS2dA1i2ny3NY13NYI3INASS4PHIb2PF1n2dY1v2HV3CN23CN33VRG3PFN3CPCS1d3FRb2FF1n1f2HF3FN33FRG3FFNS2dZ1i2ny4LENZ3idx3IDXFFS4PHIb2PF1n2dY1v1i2ny2HV3CN33VRG3PFN3CPC3dT33SHCS2dA2dY2dT1i2ny3NY13NYI3INA2NT3dT33NK33dT43NK4S1i2nySS2dZSS1d3FRb1n1f2HFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3PZ03idxS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2Z03PZ03PZC3idx3IDXSS2dZ1i2ny3idxS2dA3dLX2dY1i2ny2XB2TBS2dY2dT3dT33NK33dT43NK4FFS3dLX1i2ny3NY13NYI3IXL3dX53NK5S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3idxS2dA2dY2dT1i2ny3NY13NYI3INA2NT3dT33NK3S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY12Z03PZ03idx3IDXS4PHIb2PF1n3dLX2dY1v1i2ny2HV3VRG3PFN3CPC3dT33SHC3dT43ASCS1d3FRb2FF1n1f3FRG3HF5S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2nyFS2ny3NY1S4PHIb2PF1n2dY1v2HV3CN23CN33VRG3CPCS1d3FRb2FF1n1f2HF3FRG3FFNS2FBS2dZ1i2ny4LENZ3idx3IDX3NTHS2dZS1i2ny3NYIFSS4PHIb1n3dLX2dY1v1i2ny2HV3CPC3dT33SHC3dT43ASCS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3SPR2F04SP1R3NY12Z03PZ03idx3IDXS2FBS4PHIb2PF1n3dLX2dY1v1i2ny3VRG3dT33dT43HV5S4PHIb2PF1n2dY1v1i2ny2HV3CN33VRG3CPC3dT33SHCFS1d3FRb2FF1n1f2HF3FN23FN33FRG3FFNFS1i2nyS2dZ1i2ny3idx3IDXS2dA1i2ny4NA983NY13NYI3INAS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13NYI2Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13NYI2Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ2dT1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2Z03PZ03PZC3idx3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2dA1i2ny4NA983NY13NYI3INAS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3ALO3NY13INA2NZ3idx2wv3PZCS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idx2wvS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2dT1i2ny3idxFS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idxS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idx2wvS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2dT1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dT2nyFS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2dT1i2ny3idxFS1R2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3ACV3NY13INA2NZ3idx3PZCS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13PZ03idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3PZ03IDXS2LF3LFB2dA4gapn1n3dLX2dY2dZ2dT1i2ny3NY13INA2NZ3idxS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx2wv3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3NY13idx3IDXS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2dT1i2ny3idxS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dT2nyS2LF3LFB4gapn1n3dLX2dY2dZ2dT1i2ny3idx". (* [comment removed for export] *)
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
    eapply (call_copy_ll mq hq LBq _ _ v f 3%nat 1%nat dT dY 0xa0120); try eassumption; try reflexivity; try (rewrite EAD; reflexivity); try (rewrite EAY; reflexivity).
    - discriminate.
    - rewrite EAD. clear. lia.
    - clear - HV CPC CN2 CN3 VRG PFN. lia.
    - clear - HF FN2 FN3 FRG FFN. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST3) as (CH3 & SH3 & MI3 & ST3 & HH3 & HT3 & HS3 & HFL3 & HCS3 & HVQ3 & HFQ3 & OK3 & CSOK3 & SB643 & SCS3 & CFB3 & LAWS3 & KINV3).
      clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      assert (EAD3 : md_addr dT3 = FB + 144) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[[(-> & VT3 & NK3)|(-> & NK3 & _)] _] _].
      2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
           - clear - HV CPC CN2 CN3 VRG PFN. lia.
           - clear - HF FN2 FN3 FRG FFN. lia. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      pose proof (shl_cap ((i - ny) * 32) dT3 ltac:(unfold MPI_MAX_LIMBS; clear - NY1 NYI INA NA98; lia) (mpd_nr _ _ _ ML3)) as SHC.
      (* [comment removed for export] *)
      zstep. zstep. zstep. clear MU WM.
      unfold mpi_shift_l_stmtA_c in SHL.
      eapply (M_call_xop_l A_MPI_SHIFT_L _ _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3) (i := 3%nat) (dl := dT3) (c := (i - ny) * 32) (retpc := 0xa0130); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity).
      + rewrite EAD3. clear. lia.
      + cbv beta. clear - NY1 NYI INA NA98. lia.
      + clear - HV CPC SHC CN3 VRG PFN. lia.
      + cbv beta. clear - HF FN3 FRG FFN. lia.
      + clear. lia.
      + intros m4 h4 LB4 dT4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
        destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4' & MI4 & ST4 & HH4 & HT4 & HS4 & HFL4 & HCS4 & HVQ4 & HFQ4 & OK4 & CSOK4 & SB644 & SCS4 & CFB4 & LAWS4 & KINV4).
        clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH4.
        pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        assert (EAD4 : md_addr dT4 = FB + 144) by (rewrite EAL4; exact EAD3).
        ddestruct RR4 as [[(-> & VT4 & _ & _)| ->] (_ & _ & _ & NK4)].
        2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD4| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             - clear - HV CPC SHC CN3 VRG PFN. lia.
             - clear - HF FN3 FRG FFN. lia. }
        zstep.
        edestruct K_local_facts with (mq := m4) (i := 3%nat) (d := dT4) as (_ & NST4 & _); try eassumption; [reflexivity|].
        assert (OTH4 : md_own dT4 = LHeap) by (eapply M_out_heapA; [exact ML4| exact NST4| clear - NK4 NK3 NT INA NY1 NYI; lia]).
        edestruct K_local_facts with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (as_cap dLX dT4 (mpd_nr _ _ _ MLX4) (mpd_nr _ _ _ ML4)) as ASC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. clear MU WM.
        eapply (call_addsub_ll 1 ASP m4 h4 LB4 _ _ _ _ 0%nat 3%nat dLX dT4 0xa0148); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAD4; reflexivity).
        * discriminate.
        * rewrite EAX. clear. lia.
        * rewrite EAD4. clear. lia.
        * clear - HV CPC SHC ASC VRG PFN. lia.
        * clear - HF FRG FFN. lia.
        * clear. lia.
        * intros m5 h5 LB5 dX5 r y0'' y1'' y2'' ya1'' ya2'' ya3'' ya4'' ya5'' ya6'' ya7'' y3'' y4'' y5'' y6'' CST5 RR5 ML5 EAL5 UW5. cbn [set_nth] in CST5.
          assert (EAX5 : md_addr dX5 = FB + 80) by (rewrite EAL5; exact EAX).
          assert (HV5 : v + copy_PHI dY + shift_l_PHI dT3 ((i - ny) * 32) + add_sub_PHI dLX dLX dT4 + dvVr n <= PHIb) by (clear - HV CPC SHC ASC; lia).
          assert (HF5 : f + copy_FR 0 + shift_l_FR + add_sub_FR (d + 1) + dvFr n <= FRb) by (clear - HF; lia).
          destruct (kit_facts _ _ _ _ _ _ _ _ CST5) as (CH5 & SH5 & MI5 & ST5 & HH5 & HT5 & HS5 & HFL5 & HCS5 & HVQ5 & HFQ5 & OK5 & CSOK5 & SB645 & SCS5 & CFB5 & LAWS5 & KINV5).
          clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH5.
          pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
          ddestruct RR5 as [[(-> & VX5)| ->] (_ & _ & _ & NK5)].
          2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST5| reflexivity| exact EAX5| exact EAY| exact EAZ| exact EAD4| exact UW5| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
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
          zstep. zstep. replace (4 * (i - ny)) with (4 * idx) by (subst idx; clear; lia). zstep.
          replace (4 * idx + md_p dZ) with (md_p dZ + 4 * idx) by (clear; lia).
          zstep. zstep. l4_nf.
          zstep. zstep. zstep. zstep. l4_nf.
          zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
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
          match goal with H : rw_cells asegs m6 (sp1 + 184) _ |- _ => rename H into CZ6 end.
          destruct (limb_store_kit m5 m6 h5 LB5 _ _ _ _ 2%nat dZ idx _ CST5 eq_refl OZH IDX MU WM HH6 MI6 ST6 ltac:(rewrite EAZ; exact CZ6) UAZ' ltac:(apply upd_length)) as (CST6 & _ & UWK).
          cbn [set_nth] in CST6.
          unfold dvL5_stmt in K5.
          eapply K5 with (i := i) (ny := ny) (k := k); [exact CST6| apply linv_Z; exact LI5| exact RN| exact HK| exact (UWK UW5)| exact BPOS| exact NA98| exact HV5| exact HF5].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL4_stmt (n : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0060) fc None mq (seg_rom asegs)).

  Local Ltac l4_chunks CHq :=
    let C := fresh "CHq'" in
    pose proof CHq as C; unfold A_mpi_div_mpi_C.DCS in C;
    apply Forall_cons_iff in C; destruct C as [SPC C]; apply Forall_cons_iff in C; destruct C as [T2Cq C]; apply Forall_cons_iff in C; destruct C as [ZCq C];
    apply Forall_cons_iff in C; destruct C as [CZCq C]; apply Forall_cons_iff in C; destruct C as [GAPC C]; apply Forall_cons_iff in C; destruct C as [SAVE C];
    apply Forall_cons_iff in C; destruct C as [FHD C]; apply Forall_cons_iff in C; destruct C as [Z32C C]; apply Forall_cons_iff in C; destruct C as [Z48C C];
    apply Forall_cons_iff in C; destruct C as [Z64C C]; apply Forall_cons_iff in C; destruct C as [TPC C]; apply Forall_cons_iff in C; destruct C as [JQC _];
    cbn [fst snd] in SPC, T2Cq, ZCq, CZCq, GAPC, SAVE, FHD, Z32C, Z48C, Z64C, TPC, JQC; unfold A_mpi_div_mpi_C.dv_sp in SPC.
  Local Ltac2 Set LiaOrc.tbl := fun () => "04X0@D25900232977.307D32856653715.428D42415728606.432D42415728606.433D55579844745.432D60189065437.307D68127099103.428D9411077970.433 D991576234.428  L10432810472.13 L10685100449.0  L11725985951.3  L12266043405.1  L12267397436.2  L12289641699.3  L12469921329.0  L12808385313.0  L12861988900.11 L12884375298.10 L13740540993.11 L14447004729.1  L14447004729.2  L14793915263.2  L14820281134.11 L15822417165.1  L15824827452.2  L16000728743.6  L1685717371.0   L17524925726.422L17524925726.455L1819810129.422 L1821910231.454 L1845510483.3   L1855173106.11  L19377170497.1  L20305144376.3  L2057604755.3   L20734849921.255L21024009684.3  L21586866712.12 L21723165401.17 L21866712442.1  L21868500043.2  L22939159100.2  L22941438733.1  L23524570067.17 L24023900370.0  L24636227096.12 L25095893474.12 L25483070336.3  L26793678904.3  L26834531361.3  L26845910153.2  L26985680806.1  L27333189682.404L27588716945.2  L27817441514.422L27817441514.455L28245139357.1  L28632618922.2  L29786545640.404L29956516996.0  L30176943327.421L30334941133.1  L30336823036.2  L30399176481.0  L30817758586.3  L31145622673.2  L31525654619.6  L31525654619.9  L31527751786.6  L31687975849.255L31813027332.6  L31942703947.255L32172768967.251L32172768967.255L32284259785.0  L32565125921.0  L33179501181.300L3318711009.405 L33324104207.8  L33325904157.6  L33578466172.426L34080941563.2  L34860304136.5  L35907759677.255L36523706914.2  L36523706914.3  L37065417382.1  L37185112175.425L38069426200.12 L38259954321.2  L39207674324.3  L39284637285.0  L40066129279.1  L40066129279.2  L41415745009.255L42411609006.0  L42816623016.8  L43062351738.3  L43143490841.421L44654336316.2  L45657748817.2  L46190619535.252L46318111700.3  L47314679148.10 L48222540875.255L48700858022.1  L51158826717.20 L52428691159.11 L52635831073.0  L52955959985.4  L53518944813.251L53609733305.255L53618266946.2  L53987612891.11 L54060460629.13 L5413320392.1   L54435618246.19 L55815189670.1  L5605601736.11  L57652312495.1  L57698627611.2  L58815124353.1  L59081127747.12 L59310648043.7  L59975262609.2  L60090976557.4  L61030873410.404L6178369912.3   L61798214783.1  L61798214783.2  L62037211595.7  L62623490959.425L63072848869.3  L63650266843.12 L63650266843.15 L63650381673.15 L63800406256.426L63885703535.255L6525035386.3   L65252552111.1  L66084005463.17 L66084350309.17 L67138797694.6  L6911114296.3   L7735748552.2   L7738195705.2   L8045422791.2   L8532400182.5   L8820192273.7   L8929159528.254 L8929620893.251 L8929620893.255 L9018141615.1   L9356559676.11  L9515905201.6   L9931879857.7   P12278670331.432P12278670331.433P14461423358.428P14783166904.428P15835051771.432P15835051771.433P21870859916.432P21870859916.433P22945712379.432P22945712379.433P27590552406.308P28627113325.308P30347570235.432P30347570235.433P31146933846.308P36523116728.428P38261788758.308P40077402040.428P44651977723.432P44651977723.433P45659584406.308P57713046236.308P59963990870.308P61800574648.428P7750690063.428 P7750690063.432 P7750690063.433 Q10592318619.416Q10812129647.258Q1103009890.431 Q1103009890.432 Q11124718690.429Q11335372772.427Q11799173861.424Q11799173861.457Q11801279589.307Q11801279589.428Q11801279589.432Q11801279589.433Q11968186855.308Q14349578653.412Q15624853491.451Q16827575549.308Q17048688612.413Q18089507553.451Q18289286367.427Q18775750062.430Q22821429170.432Q24841257623.255Q25954107624.308Q25984765940.429Q26196310761.431Q26295627581.258Q26316671538.409Q27469433981.429Q28212980322.431Q28212980322.432Q28465177121.305Q28492942068.424Q29147619072.424Q2937789922.428 Q30064627682.428Q32854668691.427Q33310991603.451Q33740410509.428Q33889765055.258Q34089326809.412Q3419689062.308 Q3421936230.307 Q34357517856.418Q34669208217.414Q34964695575.421Q36721801753.420Q38251425378.429Q38802716831.416Q38966708490.255Q39688975392.413Q40039923341.424Q41009769046.425Q41106113683.427Q41259810063.304Q44298944140.409Q44330035869.414Q44491479147.424Q44894040693.429Q45989664010.255Q46092830461.428Q47976846438.431Q48234175664.427Q48590533389.429Q49698585326.426Q49698585326.430Q49698585326.431Q4983094669.429 Q50006609944.419Q50458135125.258Q51016035635.420Q51120983794.258Q51173003698.432Q51337909069.255Q51956833029.431Q51956833029.432Q5265442331.306 Q52946507198.408Q52946507198.451Q54043690820.420Q54481541668.418Q54512832306.419Q56571005952.424Q57228775306.307Q57230951818.308Q58972088529.417Q59389523937.451Q59581139423.427Q59617570334.451Q60189065437.308Q62096121588.428Q62223702353.421Q63172140343.424Q63883819088.258Q63885703535.255Q63885753572.258Q64140058237.429Q64228675114.423Q64228675114.456Q64944938496.421Q65952862367.432Q67125903774.408Q67283571366.424Q67304644247.255Q68123692404.429Q68205412585.431Q68415679339.424Q6912043759.417 Q7366573714.304 Q866574336.421  Q8943555749.255 Q9405445373.428 00001U02P04505Z07?08d09_0;D0;E0<30<40<A0<E0<F0<S0<T0<U0=60=]0=b0=g0=h0=i0>J0>N0>O0>d0>e0>f0>g0?S0@?0@K0A00A50A90AE0B50B90Bb0CP0CT0CU0CV0CZ0DU0DV0E?0Ej0F70F;0F@0FF0FK0G90G:0HH0IV0IZ0I[0JG0JH0K40K80K90K:0KG0KH0KW0L20L@0ML0Ma0NQ0Oh0QC0QD0QE0R\0SH0Sa0T60Tb0Tl0U@0V?0VI0VJ0VN0W:0Wc0Wd0Wh0Wi0Wn0Wo0X[0X\0Y:0YG0Z30Z40Z50Za0Ze0[H0\O0\T0][0^=0^>0^M0_30_40_<0_a0`K0`P0a90a>0ac0ag0ah0am0b20bL0bM0b\0cH0cR0cW0cX0d30d_0dk0eP0fA0g10g]0hd0i10i50im0jd0k70k;0k<0k=0kC0kT0kn0m=0nL0og0ok10V10m11G12A13;14514o15i16c17]18W19Q1:K1;a1=71>11>k1@A1A;1BQ1CK1DE1E?1FU1GN1Hd1I^1Jl1Kh1La1MT1NA1NB1NC1Nf1OW1PP1QI1R;1Rl1Sa1TS1Ui1V\1W>1W?1X21X31Xd1YO1ZA1Zn1Zo1[R1\G1\f1]M1^01^e1_W1`B1`e1aG1aH1ak1b\1c>1c?1cl1d_1e[1fW1gP1hC1iA1jB1jC1k61k`1lS1m61m^1nO1o<1oc20V21821c22M23023e23f23g24R25>25j26M27N27m28k29V2:H2;52;62;72;c2<E2<g2<h2=k2>i2>j2?c2@\2AO2B12B22B32C?2Cb2Dc2Dd2EK2F22FY2G<2HZ2J<2J=2Jo2KQ2L32L`2MC2N82NZ2OM2P72P82PW2Q:S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2h33HT32HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2h53HT52HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2h53HT52HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idx2HB5Ha_st5Hl_stFS4PHIb2PF1n2dY2dT1v2HV3CN23CN33CN43VRG3PFN3MUCSS2FB3sp14FBLOS2FBFS2FB3sp14FBLOFSS1d3FRb2FF1n1f2HF3FN23FN33FN43FRGS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS3sp1S3sp1FFS1d3FRb2FF1n1f2HF3FN23FN33FN43FRGS2FBFS2dA1i2ny3NY13NYI3INASFFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2sp3sp13SP1S1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS3sp1S2FBS2sp3sp13SP1S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3PZ03idxS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO3SHE3SB6S2FBFFS2FBS4PHIb2PF1n2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3PFN3MUC3dT33SHCSS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK33dT43NK4S2FB3sp14FBLOS2FBS3sp1S1i2nyS3sp1S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxFS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2FBFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxSS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2FBFSS2FB3sp14FBLOFS1d3FRb1n1f3HF5S1d3FRb1n1f3FN23FN33FN43HF5S1d3FRb1n1f2HFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12Z04PZ163PZ03idx3IDXS2dA1i2ny3NY13NYI3INAS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3PZ03idxS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2Z03PZ03PZC3idx3IDXSSS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZCS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2dA3dLX2dY1i2ny2XB2wz2TBS2dA1i2ny3dX53Q173BTPS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS3sp14gapnS2dT3dT33NK33dT43NK4S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R2Z03PZ03idxS3sp14gapnFS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBSS3sp1FS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxSS3dLX1i2ny3NY13NYI3IXL3dX53NK5S2FB3sp14FBLOS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxFFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2FBS2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK3S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12Z03PZ03idx3IDXS3sp1S4PHIb2PF1n3dLX2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3PFN3MUC3dT33SHC3dT43ASCS1d3FRb2FF1n1f3FN23FN33FN43FRG3HF5SS1R2FB3sp14SHLOS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyFS2ny3NY1S1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS4PHIb2PF1n2dY2dT1v2HV3CN23CN33CN43VRG3MUCS3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S3sp1S1d3FRb2FF1n1f2HF3FN23FN33FN43FRG3FFNS2FBFS3sp1S3sp1S2dZ1i2ny4LENZ3idx3IDX3NTHFS1R2FB3sp14SHLOS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS1i2ny3NYIS3sp1FS1R5NEEDR2sp2lo3LOS3SLO3SPRS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2sp3sp13SP1S4PHIb1n3dLX2dY2dT1v1i2ny3dT33dT43HV5S4PHIb1n3dLX2dY2dT1v1i2ny3CN23CN33CN43dT33dT43HV5S4PHIb1n3dLX2dY2dT1v1i2ny2HV3MUC3dT33SHC3dT43ASCS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12Z03PZ03idx3IDXS2FB3sp14FBLOS2FBS4PHIb2PF1n3dLX2dY2dT1v1i2ny3CN23CN33CN43VRG3dT33dT43HV5S4PHIb2PF1n2dY2dT1v1i2ny2HV3CN23CN33CN43VRG3MUC3dT33SHCS1R3HIA1h3sp12xa2HaS2FBFFS1i2nyS2dZ1i2ny3idx3IDXS2dA1i2ny4NA983NY13NYI3INAS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3idx3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2Z03PZ03PZC3idx3IDXS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R2FB3sp14gapn2gb4SHLOS2dA1i2ny4NA983NY13NYI3INAS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx4FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS2LF2sp3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxFFS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_st5SAEstS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13idx2HB5Ha_st5Hl_stS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxFS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stFS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny4SP1R3idx2HBS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxFS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HBS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny4SP1R3idx2HBS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxFS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxFS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF2lo3LFB2FB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stFS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny2F03idx2HBS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HBS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny4SP1R3idx2HBS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stFFS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS1R2LF2sp2lo3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS1R2LF2lo3LFB2FB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PZ03idx3IDXS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZ3idxFFS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxFS1R5NEEDR2LF2sp2lo3SLO3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF2lo3LFB2FB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stFS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS1R2LF2sp2lo3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stFS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13idx3IDXS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS1R2LF2ra2sp3LFB2FB3sp14gapn3FB81n3dLX2dZ1i2ny3SPR2F04SP1R3NY12Z03PZ03idx2HB5Ha_st5Hl_st5SAEstS1R2LF2ra2sp3LFB2FB3sp14gapn3FB81n3dLX2dZ1i2ny3SPR2F04SP1R3NY12Z03PZ03idx3IDX2HB5Ha_st5Hl_st5SAEstFS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idxS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idxS2LF3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idxS1R2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny3idxFS2LF3LFB4gapn1n3dLX2dZ1i2ny3idxS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H SHL MULI CMPR ASM slo SLO1 SLO2 SSH0 PF0 FF0"] Lemma dv_L4 : forall n, dvL5_stmt n -> dvL4c_stmt n -> dvL4_stmt n.
  Proof.
    intros n K5 K4c. unfold dvL4_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. l4_chunks CHq.
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
    zstep. zstep.
    try replace (4 * (i - ny)) with (4 * idx) by (subst idx; clear; lia). zstep.
    zstep.
    l4_nf.
    zstep. zstep. zstep. zstep.
    l4_nf.
    zstep.
    l4_nf.
    zstep. zstep.
    replace (Z.land (md_p dZ + 4 * idx) 3) with ((md_p dZ + 4 * idx) mod 4) by (symmetry; exact (Z.land_ones (md_p dZ + 4 * idx) 2 ltac:(lia))).
    l4_nf.
    zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wz _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear MU WM.
    pose proof (cs_c24 _ _ _ _ _ _ _ _ _ _ CST) as C24q.
    eapply (call_mul_ll mq hq LBq _ _ v f 3%nat 1%nat dT dY (w32 wz) 0xa00ac); try eassumption; try reflexivity; try (rewrite EAD; reflexivity); try (rewrite EAY; reflexivity).
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
      clear SPC T2Cq ZCq CZCq GAPC SAVE FHD Z32C Z48C Z64C TPC JQC. l4_chunks CH3.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      assert (EAD3 : md_addr dT3 = FB + 144) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[(-> & VT3 & _)| ->] (_ & _ & _ & NK3)].
      2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
           - clear - HV MUC CN2 CN3 CN4 VRG PFN. lia.
           - clear - HF FN2 FN3 FN4 FRG FFN. lia. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      pose proof (shl_cap ((i - ny) * 32) dT3 ltac:(unfold MPI_MAX_LIMBS; clear - NY1 NYI INA NA98; lia) (mpd_nr _ _ _ ML3)) as SHC.
      (* [comment removed for export] *)
      clear MU. pose proof (munch_refl [(sp1 + 80, sp1 + 88)] m3) as MU.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3s end.
      rewrite Z.shiftl_mul_pow2 in SPC by (clear; lia). change (2 ^ 5) with 32 in SPC.
      match goal with H : HM asegs R HIA h3 LB3 LF1 m3s |- _ => rename H into HH3s end.
      match goal with H : mem_inv asegs m3s |- _ => rename H into MI3s end.
      match goal with H : stk asegs m3s lo sp1 |- _ => rename H into ST3s end.
      assert (CST3s : CSTA m3s h3 LB3 [dLX; dY; dZ; dT3] dX (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 ((i - ny) * 32)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH (v + mul_int_PHI dT dY) (f + mul_int_FR (d + 1))).
      { eapply S_cs_store with (mq := m3) (a := sp1 + 80) (b := sp1 + 88); try eassumption.
        - clear; lia.
        - left. clear - SP1. lia.
        - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD3; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
        - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
        - eapply S_dcs_ok; [exact OK3| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
      assert (UW3s : UWCD m3s).
      { eapply M_uwcd_munch; [exact UW3| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
      clear MU WM. pose proof (munch_refl ([] : list ivl) m3s) as MU. pose proof (wmono_refl asegs m3s) as WM.
      zstep. clear MU WM.
      rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
      unfold mpi_shift_l_stmtA_c in SHL.
      eapply (M_call_xop_l A_MPI_SHIFT_L _ _ _ _ _ _ SHL ltac:(clear; lia) ltac:(vm_compute; discriminate) shl_fresh) with (mq := m3s) (i := 3%nat) (dl := dT3) (c := (i - ny) * 32) (retpc := 0xa00c4); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity).
      + rewrite EAD3. clear. lia.
      + cbv beta. clear - NY1 NYI INA NA98. lia.
      + clear - HV MUC SHC CN2 CN3 CN4 VRG PFN. lia.
      + cbv beta. clear - HF FN2 FN3 FN4 FRG FFN. lia.
      + clear. lia.
      + intros m4 h4 LB4 dT4 r y0' y1' y2' ya1' ya2' ya3' ya4' ya5' ya6' ya7' y3' y4' y5' y6' CST4 RR4 ML4 EAL4 UW4. cbn [set_nth] in CST4.
        destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4' & MI4 & ST4 & HH4 & HT4 & HS4 & HFL4 & HCS4 & HVQ4 & HFQ4 & OK4 & CSOK4 & SB644 & SCS4 & CFB4 & LAWS4 & KINV4).
        clear SPC T2Cq ZCq CZCq GAPC SAVE FHD Z32C Z48C Z64C TPC JQC. l4_chunks CH4.
        pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        assert (EAD4 : md_addr dT4 = FB + 144) by (rewrite EAL4; exact EAD3).
        ddestruct RR4 as [[(-> & VT4 & _ & _)| ->] (_ & _ & _ & NK4)].
        2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST4| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD4| exact UW4| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
             - clear - HV MUC SHC CN2 CN3 CN4 VRG PFN. lia.
             - clear - HF FN2 FN3 FN4 FRG FFN. lia. }
        zstep.
        edestruct K_local_facts with (mq := m4) (i := 3%nat) (d := dT4) as (_ & NST4 & _); try eassumption; [reflexivity|].
        assert (OTH4 : md_own dT4 = LHeap) by (eapply M_out_heapA; [exact ML4| exact NST4| clear - NK4 NK3 NT INA NY1 NYI; lia]).
        edestruct K_local_facts with (mq := m4) (i := 0%nat) (d := dLX) as (MLX4 & _); try eassumption; [reflexivity|].
        pose proof (as_cap dLX dT4 (mpd_nr _ _ _ MLX4) (mpd_nr _ _ _ ML4)) as ASC.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. clear MU WM.
        eapply (call_addsub_ll (-1) ASM m4 h4 LB4 _ _ _ _ 0%nat 3%nat dLX dT4 0xa00dc); try eassumption; try reflexivity; try (rewrite EAX; reflexivity); try (rewrite EAD4; reflexivity).
        * discriminate.
        * rewrite EAX. clear. lia.
        * rewrite EAD4. clear. lia.
        * clear - HV MUC SHC ASC CN2 CN3 CN4 VRG PFN. lia.
        * clear - HF FN2 FN3 FN4 FRG FFN. lia.
        * clear. lia.
        * intros m5 h5 LB5 dX5 r y0'' y1'' y2'' ya1'' ya2'' ya3'' ya4'' ya5'' ya6'' ya7'' y3'' y4'' y5'' y6'' CST5 RR5 ML5 EAL5 UW5. cbn [set_nth] in CST5.
          assert (EAX5 : md_addr dX5 = FB + 80) by (rewrite EAL5; exact EAX).
          assert (HV5 : v + mul_int_PHI dT dY + shift_l_PHI dT3 ((i - ny) * 32) + add_sub_PHI dLX dLX dT4 + (dvcCP + dvcSHL + dvcAS) + dvVr n <= PHIb) by (clear - HV MUC SHC ASC; lia).
          assert (HF5 : f + mul_int_FR (d + 1) + shift_l_FR + add_sub_FR (d + 1) + (copy_FR 0 + shift_l_FR + add_sub_FR (d + 1)) + dvFr n <= FRb) by (clear - HF; lia).
          destruct (kit_facts _ _ _ _ _ _ _ _ CST5) as (CH5 & SH5 & MI5 & ST5 & HH5 & HT5 & HS5 & HFL5 & HCS5 & HVQ5 & HFQ5 & OK5 & CSOK5 & SB645 & SCS5 & CFB5 & LAWS5 & KINV5).
          clear SPC T2Cq ZCq CZCq GAPC SAVE FHD Z32C Z48C Z64C TPC JQC. l4_chunks CH5.
          pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
          ddestruct RR5 as [[(-> & VX5)| ->] (_ & _ & _ & NK5)].
          2: { zstep. eapply M_dv_ERR with (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST5| reflexivity| exact EAX5| exact EAY| exact EAZ| exact EAD4| exact UW5| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| |].
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
          clear MU. pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL + 6, Z.shiftr FB 3 + al_sb AL + 6 + 1)] m5) as MU.
          unfold DV_FSH in SH5. cbn [zcells app] in SH5.
          pose proof (art_data_lo asegs R HIA) as ADL.
          assert (INF : In (FB, 256) LF1) by (left; reflexivity).
          assert (SHE : Z.shiftr FB 3 + al_sb AL + 6 = shadow_of AL (FB + 8 * 6)).
          { unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm 8 6), Z.div_add by lia. lia. }
          pose proof (hcs_shadow_band asegs R HIA h5 (FB + 8 * 6) (CFB5 (FB + 8 * 6) ltac:(lia))) as SB6.
          assert (SHLO : Z.shiftr FB 3 + al_sb AL + 6 + 1 <= sp1) by (clear - SHE SB6 ALO ACV ACP LOS SLO NEEDR LOC CSP SP1 SPR; lia).
          assert (FBLO : FB + 256 <= sp1) by (clear - F0 F1 F2 ADL ALO ACV ACP LOS SLO NEEDR LOC CSP SP1 SPR; lia).
          pose proof (conj ZCq I) as ZCb. pose proof (conj GAPC I) as GPb. clear ZCq GAPC.
          zstep. zstep.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
          match goal with H : HM asegs R HIA h5 LB5 LF1 m6 |- _ => rename H into HH6 end.
          match goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
          match goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
          match goal with H : rw_cells _ m6 (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into SH6 end.
          destruct ZCb as [ZCq _]. destruct GPb as [GAPC _].
          pose proof (rw_cells_transport asegs _ _ _ _ _ ZCq MU WM ltac:(cbn [disjoint_from fst snd]; split; [clear - SHLO; lia| exact I])) as ZC6.
          pose proof (rw_cells_transport asegs _ _ _ _ _ GAPC MU WM ltac:(cbn [disjoint_from fst snd]; split; [clear - SHLO; lia| exact I])) as GP6.
          clear ZCq GAPC. rename ZC6 into ZCq. rename GP6 into GAPC.
          assert (UW6 : UWCD m6).
          { eapply M_uwcd_munch; [exact UW5| exact MU|]. apply Forall_cons; [cbn [snd]; clear - SHLO; lia| apply Forall_nil]. }
          assert (LJ5 : forall d0, In d0 [dX5; dY; dZ; dT4] -> md_addr d0 + 16 <= FB + 8 * 6 \/ FB + 8 * 6 + 8 <= md_addr d0).
          { intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX5, ?EAY, ?EAZ, ?EAD4; clear - FBLO; lia. }
          lazymatch type of CST5 with CSTA _ _ _ ?lsx ?dWx ?CSx _ ?vx ?fx =>
            assert (CH6 : Forall (fun ac => rw_cells asegs m6 (fst ac) (snd ac)) CSx)
              by (unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp; repeat (apply Forall_cons; [cbn [fst snd]; assumption|]); apply Forall_nil);
            assert (CST6 : CSTA m6 h5 LB5 lsx dWx CSx (DV_FSHq 6) vx fx)
              by (eapply A_mpi_div_mpi_C.cs_shadow_write with (mq := m5) (j := 6);
                  first [ exact CST5| exact LJ5| exact MU| exact WM| exact HH6| exact MI6| exact ST6| exact CH6| reflexivity
                        | (unfold DV_FSHq, DV_FSH; cbn [zcells app firstn skipn]; exact SH6)| assumption| lia ])
          end.
          clear MU WM. assert (IND5 : In (FB + 32, 216) (LB5 ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
          pose proof (munch_refl [(FB + 48, FB + 52)] m6) as MU. pose proof (wmono_refl asegs m6) as WM.
          zstep. zstep.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
          match goal with H : HM asegs R HIA h5 LB5 LF1 m7 |- _ => rename H into HH7 end.
          match goal with H : mem_inv asegs m7 |- _ => rename H into MI7 end.
          match goal with H : stk asegs m7 lo sp1 |- _ => rename H into ST7 end.
          lazymatch type of Z48C with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m7 (FB + 48) [] cs [] Z48C) as Z48M end.
          cbn [app cells_size cells_bytes csize cbytes Nat.add] in Z48M. clear Z48C. rename Z48M into Z48C.
          lazymatch type of Z48C with rw_cells _ _ _ [CB _ ?bs] =>
            assert (Z48F : firstn 4 bs = repeat (Z_to_bv 8 0) 4) by (first [reflexivity| vm_compute; reflexivity]);
            lazymatch type of CST6 with CSTA _ _ _ ?lsx ?dWx (DCS ?spc ?t2c ?zc ?czc ?gbx ?z32x _ ?z64x ?tpcx ?jqx) ?shx ?vx ?fx =>
              assert (CST7 : CSTA m7 h5 LB5 lsx dWx (DCS spc t2c zc czc gbx z32x bs z64x tpcx jqx) shx vx fx)
            end
          end.
          { eapply S_cs_store with (mq := m6) (a := FB + 48) (b := FB + 52); [exact CST6| exact HH7| exact MU| exact WM| exact MI7| exact ST7| clear; lia| right; clear; lia| | |].
            - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX5, ?EAY, ?EAZ, ?EAD4; clear - FBLO; lia.
            - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
            - pose proof OK5 as K. unfold A_mpi_div_mpi_C.DCS in K |- *. repeat (apply Forall_cons_iff in K; destruct K as [?K K]). repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
          assert (UW7 : UWCD m7) by (eapply M_uwcd_munch; [exact UW6| exact MU| apply Forall_cons; [cbn [snd]; clear - FBLO; lia| apply Forall_nil]]).
          clear MU WM. pose proof (munch_refl [(sp1 + 200, sp1 + 212)] m7) as MU. pose proof (wmono_refl asegs m7) as WM.
          pose proof (rw_cells_merge asegs m7 (sp1 + 200) [C8 czp] [C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 1)] [C4 czpad] CZCq) as CZM.
          cbn [app cells_size cells_bytes csize cbytes Nat.add] in CZM. clear CZCq.
          zstep. zstep. zstep.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
          match goal with H : HM asegs R HIA h5 LB5 LF1 m8 |- _ => rename H into HH8 end.
          match goal with H : mem_inv asegs m8 |- _ => rename H into MI8 end.
          match goal with H : stk asegs m8 lo sp1 |- _ => rename H into ST8 end.
          lazymatch type of CZM with rw_cells _ _ _ [C8 ?w0; C4 ?w1; C4 ?w2] =>
            pose proof (rw_cells_split_C4 asegs m8 (sp1 + 200) [C8 w0] w1 [C4 w2] CZM) as CZT end.
          cbn [app] in CZT.
          assert (E2 : le2 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1)) by (rewrite !le2_of_Z; rewrite <- (CellsX.Z_to_le_bytes_mod 2 65537); reflexivity).
          assert (E3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 65537) / 2 ^ 16) = Z_to_bv 64 1) by (rewrite unsigned_lit by (clear; lia); reflexivity).
          rewrite E3 in CZT.
          assert (CZ8 : rw_cells asegs m8 (sp1 + 200) (CZCp (Z_to_bv 64 (FB + 48)) czpad)).
          { eapply rw_cells_reshape; [exact CZT| |].
            - cbn -[le2 le4 le8]. repeat split; try (rewrite ?length_le2, ?length_le4, ?length_le8; reflexivity).
            - cbn -[le2 le4 le8]. rewrite E2. reflexivity. }
          clear CZM CZT.
          lazymatch type of CST7 with CSTA _ _ _ ?lsx ?dWx (DCS ?spc ?t2c ?zc _ ?gbx ?z32x ?z48x ?z64x ?tpcx ?jqx) ?shx ?vx ?fx =>
            assert (CST8 : CSTA m8 h5 LB5 lsx dWx (DCS spc t2c zc (CZCp (Z_to_bv 64 (FB + 48)) czpad) gbx z32x z48x z64x tpcx jqx) shx vx fx)
          end.
          { eapply S_cs_store with (mq := m7) (a := sp1 + 200) (b := sp1 + 212); [exact CST7| exact HH8| exact MU| exact WM| exact MI8| exact ST8| clear; lia| left; clear - SP1; lia| | |].
            - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX5, ?EAY, ?EAZ, ?EAD4; clear - FBLO; lia.
            - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
            - pose proof OK5 as K. unfold A_mpi_div_mpi_C.DCS in K |- *. repeat (apply Forall_cons_iff in K; destruct K as [?K K]). repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
          assert (UW8 : UWCD m8).
          { eapply uwc_floor with (F := sp1 + 216); [| clear; lia].
            eapply uwc_munch; [eapply A_mpi_div_mpi_M_c24.uwc_raise_m; [exact UW7| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
            intros xa Ha. cbn [outside]. split; [clear - Ha; lia| exact I]. }
          clear MU WM. pose proof (munch_refl ([] : list ivl) m8) as MU. pose proof (wmono_refl asegs m8) as WM.
          zstep. zstep. zstep. clear MU WM.
          eapply (call_cmp0_l m8 h5 LB5 [dX5; dY; dZ; dT4]) with (i := 0%nat) (di := dX5) (j := 6%nat) (q := FB + 48) (retpc := 0xa0108); try eassumption; try reflexivity; try (rewrite EAX5; reflexivity).
          -- right. split; [reflexivity| split; [reflexivity| exact Z48F]].
          -- clear. lia.
          -- intros m9 q0 q1 q2 qa1 qa2 qa3 qa4 qa5 qa6 qa7 q3 q4 q5 q6 CST9 UW9i.
            repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
            destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST9) as (CH9 & SH9 & MI9 & ST9 & HH9).
            l4_chunks CH9.
            unfold DV_FSHq, DV_FSH in SH9. cbn [zcells app firstn skipn] in SH9.
            pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL + 6, Z.shiftr FB 3 + al_sb AL + 6 + 1)] m9) as MU. pose proof (wmono_refl asegs m9) as WM.
            pose proof (conj ZCq I) as ZCb. pose proof (conj GAPC I) as GPb. clear ZCq GAPC.
            zstep. zstep.
            lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
            match goal with H : HM asegs R HIA h5 LB5 LF1 m10 |- _ => rename H into HH10 end.
            match goal with H : mem_inv asegs m10 |- _ => rename H into MI10 end.
            match goal with H : stk asegs m10 lo sp1 |- _ => rename H into ST10 end.
            match goal with H : rw_cells _ m10 (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into SH10 end.
            destruct ZCb as [ZCq _]. destruct GPb as [GAPC _].
            pose proof (rw_cells_transport asegs _ _ _ _ _ ZCq MU WM ltac:(cbn [disjoint_from fst snd]; split; [clear - SHLO; lia| exact I])) as ZC10.
            pose proof (rw_cells_transport asegs _ _ _ _ _ GAPC MU WM ltac:(cbn [disjoint_from fst snd]; split; [clear - SHLO; lia| exact I])) as GP10.
            clear ZCq GAPC. rename ZC10 into ZCq. rename GP10 into GAPC.
            assert (UW10 : UWCD m10).
            { eapply M_uwcd_munch; [exact (UW9i UW8)| exact MU|]. apply Forall_cons; [cbn [snd]; clear - SHLO; lia| apply Forall_nil]. }
            lazymatch type of CST9 with CSTA _ _ _ ?lsx ?dWx ?CSx _ ?vx ?fx =>
              assert (CH10 : Forall (fun ac => rw_cells asegs m10 (fst ac) (snd ac)) CSx)
                by (unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp; repeat (apply Forall_cons; [cbn [fst snd]; assumption|]); apply Forall_nil);
              assert (CST10 : CSTA m10 h5 LB5 lsx dWx CSx DV_FSH vx fx)
                by (eapply A_mpi_div_mpi_C.cs_shadow_write with (mq := m9) (j := 6);
                    first [ exact CST9| exact LJ5| exact MU| exact WM| exact HH10| exact MI10| exact ST10| exact CH10| reflexivity
                          | (unfold DV_FSH; cbn [zcells app]; exact SH10)| assumption| lia ])
            end.
            (* [comment removed for export] *)
            clear MU WM. pose proof (munch_refl ([] : list ivl) m10) as MU. pose proof (wmono_refl asegs m10) as WM.
            lazymatch goal with |- context [Z_to_bv 64 (Z.sgn ?vv)] => destruct (Z.sgn_spec vv) as [(KS & ->)|[(KS & ->)|(KS & ->)]] end.
            1-2: zstep; eapply K5; [exact CST10| exact LI5'| exact RN| exact HK| exact UW10| exact BPOS| exact NA98| clear - HV5 CN2 CN3 CN4; lia| clear - HF5 FN2 FN3 FN4; lia].
            zstep. eapply K4c; [exact CST10| exact LI5| exact RN| exact HK| exact UW10| exact BPOS| exact NA98| clear - HV5; lia| clear - HF5; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDW_stmt (n Q : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z) wz
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wz -> (w32 wz - 1) mod 2^32 <= Z.of_nat Q ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fe6c) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L3793790120.116 L64507207096.11600000n01kS2LF2ra2sp3LFB1d3FRb2FB3sp14gapn2FF1n1f2HF3FN13FN23FN33FN43FRGS2LF2ra2sp3LFB4PHIb2FB3sp14gapn2PF1n1v2HV3CN13CN23CN33CN43VRG". (* [comment removed for export] *)
  #[using="LF ra sp LFB D0 FB sp1 gapn"] Lemma budget_err : forall n v f, v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb -> v + PF <= PHIb /\ f + FF <= FRb.
  Proof.
    intros n v f HV HF. dpose caps_nonneg as (CN1 & CN2 & CN3 & CN4). dpose frs_nonneg as (FN1 & FN2 & FN3 & FN4).
    pose proof (dvVr_ge n) as VRG. pose proof (dvFr_ge n) as FRG. unfold dvVrnd in HV. unfold dvFrnd in HF. split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDW2_stmt (n Q : nat) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z) wq
           xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wq -> w32 wq <= Z.of_nat Q ->
    (forall j w, 1 <= j -> nth_error (md_limbs dT) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0) ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9feb4) fc None mq (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@C7096915042.251 D33876909647.250D63873442836.250K21870859916.252K22945712379.252K66327680928.251L12469921329.0  L14447101554.5  L14794338612.5  L16000728743.6  L1685717371.0   L19133426325.6  L21868076544.5  L22938730615.5  L29832375856.1  L29956516996.0  L32170472955.238L32321742194.6  L32477325796.2  L32534791728.247L36508794932.6  L36571201320.0  L38691415991.0  L40066488116.5  L41811005730.8  L45099190568.0  L46190619535.238L53517041937.238L53550479595.0  L54949972769.0  L59310730320.9  L59310730321.11 L59667784614.1  L61798049332.5  L65252552111.1  L66330468140.4  L7665232397.1   L7735389571.5   L8532400182.5   L8927066272.239 L8927066273.238 L8929159528.242 L9356559676.11  P14461423358.252P14783166904.252P36523116728.252P40077402040.252P61800574648.252P66327680928.251P7750690063.252 Q10812129647.246Q1129201116.246 Q1130936680.246 Q1133410593.246 Q11801279589.250Q19991027068.252Q24841257623.241Q26295627581.246Q33874924623.251Q33877164610.246Q33889765055.246Q38966708490.241Q45989664010.241Q48467890406.252Q49698585326.250Q50458135125.246Q51135677050.249Q51336009840.243Q53831382756.246Q57769205668.243Q57769252262.246Q57771708690.246Q57775887855.246Q63871233556.251Q66391428222.246Q66401733687.246Q66403993731.246Q67304644247.241Q8945721240.243 00000101F02>03>04404504604704804M04N04d04e04f04j04k06G06]06c07T07U07V07W07X08308408e09P09Q09R09g0:E0:I0:J0:N0:O0:S0:T0:e0<=0=U0>m0?X0@i0BD0C_0E00FA0FB0GU0HG0HH0HI0HJ0I10I20Id0JH0K=0Ko0La0MP0N?0N@0O20OV0PF0Q80Qh0RP0S80S`0TH0U30U40U50U60Uh0VLFS2LF2ra2sp3LFB2dA2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idx3SPR2F04SP1R2wv3NY13INA2NZ2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3KW1S2LF3LFB2dA2FB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3NY13INA2NZ3PZF3KW1S2LF3LFB2FB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3PZF3IDX3KW1FFFFS2dA1i2ny3NY13NYI3INASS2dZ1i2ny3idx4LENZ3IDXFFS2dZSS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZCS2dZ1i2ny3idx4LENZ3IDXS1j2J1S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idxFSSFS2dA2dT1i2ny3NY13NYI3INA2NTSS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny2wz3idxS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wzFSS2dZ1i2ny3idx3IDX3KW1S2dZ1i2ny3idx3IDX1H2H03KW23PZ0S2dZFS2FBFS2dTFS2dZ1i2ny3idx3IDXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wz3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDX3KW1S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wz3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDX3KW1S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny2wz3idx3ACV3SPR2F04SP1R3NY12Z03PZ03PZC3IDX3KW1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3PZC3IDXFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3ALO2wv3NY13INA2NZ3PZCS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZFFFS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wvFS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3NY13INA2NZS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny2wz3idxS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny2wz3idxFS1R2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3ACV3PZC3IDXS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13PZ03KW1S2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13INA2NZS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3NY13PZ03KW1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3KW1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3KW1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3KW1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx3KW1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx2wv3KW1FFFS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny2wz3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny2wz3idx". (* [comment removed for export] *)
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
    zstep. zstep. zstep. zstep. if_cases KW1; zify_cond KW1; [exfalso; clear - KW1 IDX PZ0 PZC; lia|].
    zstep. zstep. zstep. zstep. if_cases KW2; zify_cond KW2;
      [exfalso; clear - KW2 PZ0 PZC IDX; repeat match type of KW2 with context [?a <? ?b] => revert KW2; case (Z.ltb_spec a b); intros ? KW2 end;
       cbn [Z.b2z] in KW2; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in KW2; lia|].
    zstep. zstep. shadow_chk OPZ (4 * idx + md_p dZ) 4.
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
    match goal with H : rw_cells asegs m2 (sp1 + 184) _ |- _ => rename H into CZ2 end.
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
    eapply (call_lset_ng_l m2 hq LBq _ _ v f 3%nat dT 0 0x9feb4); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
    - rewrite EAD. clear. lia.
    - clear - NT INA NY1 NYI. lia.
    - clear. lia.
    - clear. lia.
    - intros m3 h3 LB3 dT3 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 CST3 RR3 ML3 EAL3 UW3. cbn [set_nth] in CST3.
      assert (EAD3 : md_addr dT3 = FB + 144) by (rewrite EAL3; exact EAD).
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
        eapply M_dv_ERR with (r := -16); [exact CST3| reflexivity| exact EAX| exact EAY| | exact EAD| exact UW3| clear; lia| exact HVE| exact HFE].
        unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_addr]. exact EAZ.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvDWg (n Q : nat) (U pc : Z) (RA : mpd -> word -> word -> Prop) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z) wq
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX
         (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    nth_error (md_limbs dZ) (Z.to_nat (i - ny)) = Some wq -> w32 wq <= Z.of_nat Q ->
    (forall j w, U <= j -> nth_error (md_limbs dT) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0) ->
    RA dZ a1 a5 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11v t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mq (seg_rom asegs)).
  Definition dvDW3_stmt (n Q : nat) : Prop :=
    dvDWg n Q 1 0x9ff10 (fun _ _ a5 => a5 = Z_to_bv 64 (al_sb AL)).
  Definition dvDW5_stmt (n Q : nat) : Prop :=
    dvDWg n Q 2 0x9ff9c (fun dZ a1 a5 => a1 = Z_to_bv 64 (md_p dZ) /\ a5 = Z_to_bv 64 (al_sb AL)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@L12515393408.3  L13845124416.5  L16000728743.6  L17715532577.0  L25176780149.8  L29956516996.0  L31940620758.5  L32170474491.240L32170474493.241L39188636933.0  L41418037451.245L47314679148.10 L48224558806.6  L53379847057.3  L53517045521.240L5374952848.5   L5562114849.0   L59308960241.4  L59310614993.7  L59310727760.6  L59310727766.6  L61642822427.9  L65252552111.1  L66151427842.19 L8532400182.5   L8927065761.240 L8927065767.241 L8927181073.242 L8929159528.245 L9356559676.11  Q10812129647.249Q12392256627.319Q20550926318.319Q26295627581.249Q33889765055.249Q45989664010.243Q50458135125.249Q51120983794.249Q51335961025.246Q63883752419.246Q63883819088.249Q63885753572.249Q67304644247.243Q8945737257.246 00000;00N00c00d01?01@01Q03604W04X05F05i06>06H07407F07G07U07n08C08X09709;09_0:00;?0<J0=U0>`0?K0@:0A80B90BZ0CI0D50DV0EC0F20FW0G<0Ga0HP0I1S2wq3QNZ2WRS4PHIb2PF1v3HVE3PFNS2dA1i2ny3NY13NYI3INASS2dA2dT1i2ny3NY13NYI3INA2NTSS2dZ1i2ny3idx3PZRS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n1Q3dLX2dZ1i2ny3idx3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZC3IDX3KC1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n1Q3dLX2dZ1i2ny3idx3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2Z03PZ03PZC3KC1SS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ1i2ny3idxS2dA2dT1i2ny3NY13NYI3INA2NT3dT33NK3S2dZ1i2ny3idx3IDX3PZRS2Q'2wq2QBS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idxS3FRb2FF1f3HFE3FFNSS2wq2QB3QNZ2WRS2u02u12u23dT33VZ32GT3LR2S2dZ1i2ny3idx3IDX3KC1S2dZ1i2ny3idx3PZR3KC3S1R2dZ1i2ny3idx3ACV3PZ03PZC3IDXS2FBS2dZ1i2ny3idx2r04PZ161q1r1H2H02q02H4S2dZ1i2ny3idx3IDXS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3SPR2F04SP1R3NY12Z03PZ03IDX3PZR3KC1S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3SPR2F04SP1R3NY12Z03PZ03PZR3KC1S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3SPR2F04SP1R3NY12Z03PZ03PZR3KC1S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dZ2ny3idx3SPR2F04SP1R3NY12Z03PZ03PZR3KC1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ2u02u12u21i2ny3idx3dT34cmpvS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ2u02u12u21i2ny3idx3dT34cmpvS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idxS2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3NY13PZR3KC1S2LF3LFB2dA4gapn1n1Q3dLX2dZ1i2ny3idx3NY13INA2NZS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3KC1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3KC1S2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx3KC1S2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dZ1i2ny3idxS2LF3LFB4gapn1n1Q3dLX2dZ1i2ny3idx". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H MULNG CMPR slo SLO1 SLO2 SSH0 PF0 FF0"] Lemma dv_DW5 : forall n Q, dvL4_stmt n -> (forall Q', Q = S Q' -> dvDW_stmt n Q') -> dvDW5_stmt n Q.
  Proof.
    intros n Q K4 KDW. unfold dvDW5_stmt, dvDWg. intros until t6. intros CST LI RN NTH QB ZT RA HK UW BPOS NA98 HV HF. destruct RA as [-> ->]. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    destruct (budget_err _ _ _ HV HF) as [HVE HFE].
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ).
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    set (idx := i - ny) in *.
    assert (IDX : 0 <= idx < md_n dZ) by (subst idx; rewrite NZ; clear - NY1 NYI INA; lia).
    assert (PZR : 0 < md_p dZ /\ md_p dZ + 4 * idx + 4 < 2 ^ 64) by (clear - PZ0 PZC ACV IDX; lia).
    assert (PZA : (md_p dZ + 4 * idx) mod 4 = 0) by (clear - PZ16; Z.div_mod_to_equations; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    if_cases KC1; zify_cond KC1; [exfalso; clear - KC1 IDX; lia|].
    zstep. zstep. zstep.
    replace (0 <? md_p dZ) with true by (symmetry; apply Z.ltb_lt; clear - PZR; lia).
    replace (md_p dZ + 4 * idx <? 1) with false by (symmetry; apply Z.ltb_ge; clear - PZR IDX; lia).
    cbn [Z.b2z Z.lxor].
    zstep.
    zstep. if_cases KC3; zify_cond KC3; [exfalso; clear - KC3 PZR; lia|].
    zstep. assert (LZA : Z.land (md_p dZ + 4 * idx) 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact PZA). rewrite LZA.
    zstep. zstep. zstep. shadow_chk OPZ (md_p dZ + 4 * idx) 4.
    pose proof (u32arr_read asegs mq (md_p dZ) (md_limbs dZ) idx wq _ UAZ NTH ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep. clear MU WM.
    pose proof (cs_c24 _ _ _ _ _ _ _ _ _ _ CST) as C24q.
    eapply (call_mul_ng_l mq hq LBq _ _ v f 3%nat dT (w32 wq) 2 655332); try eassumption; try reflexivity; try (rewrite EAD; reflexivity).
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
      assert (EAD3 : md_addr dT3 = FB + 144) by (rewrite EAL3; exact EAD).
      ddestruct RR3 as [[(-> & VZ3 & _)| ->] (_ & _ & _ & NK3)].
      2: { unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep. eapply M_dv_ERR with (r := -16); [exact CST3| reflexivity| exact EAX| exact EAY| exact EAZ| exact EAD3| exact UW3| clear; lia| exact HVE| exact HFE]. }
      zstep.
      edestruct K_local_facts with (mq := m3) (i := 3%nat) (d := dT3) as (_ & NST3 & _); try eassumption; [reflexivity|].
      assert (OTH3 : md_own dT3 = LHeap) by (eapply M_out_heapA; [exact ML3| exact NST3| clear - NK3 NT INA NY1 NYI; lia]).
      assert (LI3 : linv dLX dY dZ dT3 i ny) by (eapply linv_T; [exact LI| exact EAL3| exact OTH3| exact NK3]).
      (* [comment removed for export] *)
      zstep. zstep. zstep. clear MU WM.
      eapply (call_cmpraw m3 h3 LB3) with (i := 3%nat) (di := dT3) (retpc := 655348); try eassumption; try reflexivity; try (rewrite EAD3; reflexivity); [clear; lia|].
      intros m4 z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 CST4 UWK. pose proof (UWK UW3) as UW4.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
      destruct (kit_facts _ _ _ _ _ _ _ _ CST4) as (CH4 & SH4' & MI4 & ST4 & HH4 & _).
      clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH4.
      set (cmpv := md_sg dT3 * lval (md_limbs dT3) (md_n dT3) - 1 * lval [u0; u1; u2] 3) in *.
      zstep.
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0@C26840107418.310C601670438.254  D18694488097.253D25312390013.308D40377636077.308D55473375817.253K12129020021.255K13933473562.255K25675773025.310K30788161014.310K40962858357.255K48056743797.255K54509607265.310K56623506564.310K61624464225.310K63563842176.254L10363041570.2  L10642704280.3  L11146238902.2  L12117080213.2  L12138107471.2  L12469921329.0  L13937033210.2  L14343865800.1  L14554717887.5  L1685717371.0   L17060135621.2  L17660516633.242L18761833895.5  L21920025279.6  L24084976897.2  L25680471169.2  L25858047826.2  L27038155402.2  L28508438659.287L28508438660.286L28862916362.2  L30800338198.2  L30981510610.2  L31525954925.2  L34785933159.2  L3573825802.2   L35846324226.8  L35907695816.296L35907808182.293L40091177158.1  L4031406518.2   L40959102357.2  L41042593915.5  L41417953388.242L41418037451.296L41766935438.2  L4586513446.250 L46190619535.296L47015188111.2  L48061376405.2  L50581837322.3  L51023689398.3  L53517045520.286L53623799102.5  L54522759553.2  L56638829634.4  L58133293238.2  L5831383034.11  L59310727760.3  L59310727761.6  L59310727764.3  L59310727766.3  L59310727767.4  L59321132280.6  L61636567937.2  L61997691801.2  L62830729610.1  L62832826796.4  L63346541849.286L63560127072.1  L66151427842.16 L66151427842.17 L67574619286.245L67576709976.289L67576709979.290L67576709983.242L7131264010.2   L8927065760.286 L8927065765.290 L8927065767.287 L8929159528.293 L9356559676.11  P11150019414.310P12141789871.309P17047015973.310P24081221089.255P28866574314.255P30977918258.255P3587019242.255 P4035162454.310 P41763277678.310P50568644330.255P51035661910.310P56623506564.310P58146322518.310P63563842176.254P7143400682.255 Q11801279589.253Q11801279589.308Q14331660581.249Q14342228332.249Q14342278511.246Q15618424998.245Q16858858661.255Q18696473121.254Q20013594135.294Q24814724221.305Q24837033773.304Q2514434743.245 Q25306249017.305Q25307919245.302Q25310437757.309Q25312130928.304Q25622449825.307Q25632916009.305Q26295627581.249Q26295627581.302Q26295627581.305Q28770016439.294Q38667434164.299Q38962480304.304Q40258548363.255Q40375623405.309Q40377895136.304Q42816481578.253Q46281013204.246Q46711588518.294Q50458135125.249Q50458135125.302Q50458135125.305Q54608293134.302Q55126681098.304Q55471390793.254Q59541579092.302Q60412549208.249Q64032823942.308Q64054320522.294Q65860365407.249Q66791166483.299Q66791183892.302Q66791183892.304Q67246447712.249Q7411613069.252 Q8943472942.302 Q8945717657.246 Q8945717661.299 Q9992779027.302 00000100200]01P02k03l04\05L06]07n08^09N0:_0:`0<10<20<80<D0<E0<F0<G0<H0<I0<M0<\0<]0<^0=F0=O0=^0=_0=`0=g0=m0?O0A10A20A30A40A<0AC0AD0A_0C?0D_0Dc0Dd0De0E70E_0FN0FO0G70Gf0Gl0Gm0Gn0Go0H^0I00I10I20I30IP0I\0Ik0J70JC0JR0Jl0Jm0K50K90KA0L00L10LL0Lj0N20O`0Q@0RH0RI0T;0Ui0WW0YE0Z00[?0[@0\N0]M0^T0_[0`b0b80cG0dN0ed0ee0g40g50h<0hZ0i@0i[0j60jQ0jo0k00kN0l>0ld0mT0n20nT0o60o\10>10d11J11e12G12i13N14814e14f15P16616^17<17a18<18^19@19j1:T1;51;[1<91<h1=U1>31>Y1??1?e1@D1@c1AE1A`1BB1BlFFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny2wvS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3wv23dT2S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3SPR2F04SP1R3wv22T03PT03dT23Y023PY03T024PT023T32S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3SPR2F04SP1R2wv2T03PT02T3S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PT03PTF2T33KC1S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PT03PTF2T33KC1S1R2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3ACV2F13wv23PT03PTF2T33KC13dT23PY03KC33KC43KC5S1R2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3ACV2F13wv23PT03PTF2T33KC13dT23PY03KC33KC43KC5S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PT03PTF2T33KC1S2LF3LFB2FB4gapn1n1Q3dLX2dT2ny2wv3PT03PTF2T33KC1S1R2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3ACV2F13wv23PT03PTF2T33KC13dT23PY03KC33KC43KC5FS1R2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3ACV2F13wv23PT03PTF2T33KC13dT23PY03KC33KC43KC5FS1j2J2S2dT4LENT2T3FFFFFS2dTS2dY2ny3NY13PYRSFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyS3dT23T32S3dT25LENT23T32FFS2dT2T3S1j2J2S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03dT23Y024NY1'3PY03PYC3T024PT02S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03dT23Y024NY1'3PY03PYC3T024PT02FFFS2dY3PYRS2dY2nyFS2dA2dT1i2ny3NY13NYI3INA2NTS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T33dT23Y023PY03T024PT02S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T33dT23Y023PY03T024PT02S2dTFFS1R2dY3ACV3PY03PYCS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3dT2FS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2nyS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3dT2S1j2J1FFFS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3dT2S1R2dT3ACV3PT03PTCFFFS2dA1i2ny3NY13NYI3INA3dT23NT2S2dT3PTR3KC1S2dY2ny3NY13KC2S2dT3PTR3KC5S2dY3PYR3KC3S2dT2T33PTR3KC4S2dY2ny3NY13NYL5LENY24NTHYFS2ny3NY1S2dTS2dT3dT2S2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3dT2FS2dT2r04PT161q1r1H2H02q02H4S2dY2ny2r04PY161q1r1H2H02q02H4S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T3S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T33dT23Y023PY03T024PT024EPT24PTC23T32S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T33dT23Y023PY03T024PT02S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dT2ny3ACV3SPR2F04SP1R2T03PT03PTC2T3FS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NY13NYL2T03PT03dT23Y024NY1'3PY03PYC3T024PT023PYR3KC2S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NYL2T03PT03dT23Y024NY1'3PY03PYC3T024PT023PYR3KC2S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NYL2T03PT03dT23Y024NY1'3PY03PYC3T024PT023PYR3KC2S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2dT2ny3ACV3SPR2F04SP1R3NYL2T03PT03dT23Y024NY1'3PY03PYC3T024PT023PYR3KC2S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO3wv23PTC2T33dT2FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB4gapn1n1Q3dLX2dY2dT2ny3ALO3wv23dT24EPT24PTC23T32S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB4gapn1n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO3wv23dT24EPT24PTC23T32S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO3wv23PTC2T33dT2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO3wv23dT24EPT24PTC23T32FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3ALO3wv23PTC2T33dT2FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n1Q3dLX2dT2ny3ALO2wv3PTC2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny2wvS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3wv23dT2S2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB2FB4gapn1n1Q3dLX2dT2nyFS2LF3LFB4gapn1n1Q3dLX2dT2ny2wvS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23T32S2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2dT2ny3dT2S2LF3LFB2FB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3wv23dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3PT03dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3PT03dT2S2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL3dT23KC2S2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2dT2ny3dT2FS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3wv23dT23T32S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23T32S1R2LF3LFB4gapn1n1Q3dLX2dT2ny3ACV3PTC2T3S2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S2LF3LFB2FB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL3dT23KC2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3NYL3dT23KC2S2LF3LFB4gapn1n1Q3dLX2dT2ny2wv2T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23T32S2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S1R2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3ACV3PTC2T33dT2S2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dT2ny2T3S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23KC2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23KC2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23KC2S2LF3LFB4gapn1n1Q3dLX2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dT2ny3PT0S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dT2nyS2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT2S2LF3LFB4gapn1n1Q3dLX2dY2dT2ny3dT23PYR3KC2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_DW3 : forall n Q, dvDW5_stmt n Q -> dvDW3_stmt n Q.
  Proof.
    intros n Q K5. unfold dvDW3_stmt, dvDWg. intros until t6. intros CST LI RN NTH QB ZT RA HK UW BPOS NA98 HV HF. subst a5. kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 1%nat) (d := dY) as (MLY & _); try eassumption; [reflexivity|].
    pose proof MLY as [(CY & _) _]. rewrite EAY in CY. unfold mpi_cells in CY.
    edestruct K_local_facts with (mq := mq) (i := 3%nat) (d := dT) as (MLT & NSTl & _ & _ & _ & _ & HFT & _ & T8 & _ & OTs); try eassumption; [reflexivity|].
    pose proof MLT as [(CT & _ & T0 & LENT & NRT & OWT) SGT]. rewrite OTH in OWT. ddestruct OWT as (NT1 & INT & PT16 & UAT). rewrite EAD in CT. unfold mpi_cells in CT.
    ddestruct (HFT OTH) as (PT0 & PTC & _ & _ & PTF & _).
    assert (OPT : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dT) (4 * md_n dT)) by (eapply hm_aobj_block; [exact HHq| exact INT]).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dT) (4 * md_n dT))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INT| clear; lia| clear; lia]).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & _); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _) _]. rewrite EAZ in CZ. unfold mpi_cells in CZ.
    assert (T3 : 3 <= md_n dT) by (clear - NT INA NY1 NYI; lia).
    assert (PTR : 0 < md_p dT /\ md_p dT + 4 * md_n dT < 2 ^ 64) by (clear - PT0 PTC ACV; lia).
    assert (LTA : Z.land (md_p dT) 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - PT16; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(md_p dT, md_p dT + 4)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KC1; zify_cond KC1; [exfalso; clear - KC1 PTR; lia|].
    zstep. rewrite LTA. zstep. zstep. zstep. shadow_chk OPT (md_p dT) 4.
    pose proof (u32arr_store_ok asegs mq (md_p dT) (md_limbs dT) 0 _ UAT ltac:(clear - T3 LENT; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dT) (md_limbs dT) 0 vv UAT ltac:(clear - T3 LENT; lia)) as UAT'; change (md_p dT + 4 * 0) with (md_p dT + 0) in UAT'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (FB + 144) _ |- _ => rename H into CT2 end.
    assert (MU' : munch [(md_p dT + 4 * 0, md_p dT + 4 * 0 + 4)] mq m2) by (replace (md_p dT + 4 * 0) with (md_p dT) by (clear; lia); exact MU).
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 3%nat dT 0 _ CST eq_refl OTH ltac:(clear - T3; lia) MU' WM HH2 MI2 ST2 ltac:(rewrite EAD; exact CT2) UAT' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2. pose proof (UWK UW) as UW2. clear MU MU' WM UWK.
    lazymatch type of CST2 with context [set_limbsA dT ?xs] => set (dT2 := set_limbsA dT xs) in * end.
    assert (EPT2 : md_p dT2 = md_p dT) by reflexivity.
    assert (LI2 : linv dLX dY dZ dT2 i ny) by (unfold dT2; apply linv_Tl; exact LI).
    assert (ZT2 : forall j w, 1 <= j -> nth_error (md_limbs dT2) (Z.to_nat j) = Some w -> bv_unsigned w mod 2^32 = 0).
    { intros j w J1 NJ. unfold dT2, A_mpi_div_mpi_M_c24.set_limbsA in NJ. cbn [md_limbs] in NJ.
      rewrite nth_error_upd_other in NJ by (clear - J1; lia). apply (ZT j w J1 NJ). }
    try clear CT2. try clear CY. try clear CZ. try clear OPT. try clear CWT. try clear UAT. try clear UAT'. try clear MLT. try clear MLY. try clear MLZ. try clear SOKw.
    destruct (kit_facts _ _ _ _ _ _ _ _ CST2) as (CH2 & _).
    clear SPC T2Cq ZCq GAPC SAVE FHD TPC JQC. kit_chunks CH2.
    dpose LI2 as (_ & _ & _ & EAD2 & _ & _ & _ & OTH2 & _ & _ & _ & _ & _ & _ & NT2 & _ & _).
    edestruct K_local_facts with (mq := m2) (i := 1%nat) (d := dY) as (MLY2 & NSY2 & _ & _ & _ & _ & HFY2 & _ & Y82 & _ & OYs2); try eassumption; [reflexivity|].
    pose proof MLY2 as [(CY2 & _ & Y02 & LENY2 & NRY2 & OWY2) SGY2]. rewrite OYH in OWY2. ddestruct OWY2 as (NY1' & INY2 & PY16 & UAY2).
    ddestruct (HFY2 OYH) as (PY0 & PYC & _ & _ & PYF & _).
    rewrite EAY in CY2. unfold mpi_cells in CY2.
    assert (OPY : aobj asegs AL (hcs asegs R HIA hq) m2 (md_p dY) (4 * md_n dY)) by (eapply hm_aobj_block; [exact HH2| exact INY2]).
    edestruct K_local_facts with (mq := m2) (i := 3%nat) (d := dT2) as (MLT2 & NST2 & _ & _ & _ & _ & HFT2 & _ & T82 & _ & OTs2); try eassumption; [reflexivity|].
    pose proof MLT2 as [(CT2 & _ & T02 & LENT2 & NRT2 & OWT2) SGT2]. rewrite OTH2 in OWT2. ddestruct OWT2 as (NT12 & INT2 & PT162 & UAT2). rewrite EAD2 in CT2. unfold mpi_cells in CT2.
    ddestruct (HFT2 OTH2) as (PT02 & PTC2 & _ & _ & PTF2 & _).
    rewrite EPT2 in INT2, UAT2, CT2.
    assert (OPT2 : aobj asegs AL (hcs asegs R HIA hq) m2 (md_p dT) (4 * md_n dT2)) by (eapply hm_aobj_block; [exact HH2| exact INT2]).
    assert (CWT2 : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dT) (4 * md_n dT2))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INT2| clear; lia| clear; lia]).
    edestruct K_local_facts with (mq := m2) (i := 2%nat) (d := dZ) as (MLZ2 & _); try eassumption; [reflexivity|].
    pose proof MLZ2 as [(CZ2 & _) _]. rewrite EAZ in CZ2. unfold mpi_cells in CZ2.
    destruct (M_locals_apart _ _ _ _ _ _ _ _ 3%nat 1%nat dT2 dY CST2 eq_refl eq_refl ltac:(discriminate)) as [_ LAP]. specialize (LAP OTH2 OYH).
    assert (T32 : 3 <= md_n dT2) by (clear - NT2 INA NY1 NYI; lia).
    assert (PYR : 0 < md_p dY /\ md_p dY + 4 * md_n dY < 2 ^ 64) by (clear - PY0 PYC ACV; lia).
    destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 1))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY2 NYL NY1; lia].
    pose proof (munch_refl [(md_p dT + 4, md_p dT + 4 + 4)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep. zstep. zstep. replace (md_p dY + (ny - 1) * 4) with (md_p dY + 4 * (ny - 1)) by (clear; lia).
    zstep. if_cases KC2; zify_cond KC2; [exfalso; clear - KC2 PYR NY1 NYL; lia|].
    zstep. zstep. zstep.
    match goal with |- context [Z.b2z (0 <? ?p)] => replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; clear - PYR; lia) end.
    match goal with |- context [Z.b2z (?e <? 1)] => replace (e <? 1) with false by (symmetry; apply Z.ltb_ge; clear - PYR NY1 NYL; lia) end.
    cbn [Z.b2z Z.lxor].
    zstep.
    zstep. if_cases KC3; zify_cond KC3; [exfalso; clear - KC3 PYR; lia|].
    zstep.
    match goal with |- context [Z.land ?e 3] => assert (LYA : Z.land e 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - PY16; Z.div_mod_to_equations; lia); rewrite LYA end.
    zstep. zstep.
    zstep. if_cases KC4; zify_cond KC4; [exfalso; clear - KC4 PTR T3; lia|].
    zstep. if_cases KC5; zify_cond KC5; [exfalso; clear - KC5 PTR; lia|].
    zstep. zstep. shadow_chk OPY (md_p dY + 4 * (ny - 1)) 4.
    pose proof (u32arr_read asegs m2 (md_p dY) (md_limbs dY) (ny - 1) wy _ UAY2 NTHY ltac:(clear - NY1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. zstep. zstep. shadow_chk OPT2 (md_p dT + 4) 4. clear RD.
    pose proof (u32arr_store_ok asegs m2 (md_p dT) (md_limbs dT2) 1 _ UAT2 ltac:(clear - T32 LENT2; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs m2 (md_p dT) (md_limbs dT2) 1 vv UAT2 ltac:(clear - T32 LENT2; lia)) as UAT3; change (md_p dT + 4 * 1) with (md_p dT + 4) in UAT3; set (wv2 := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m3 |- _ => rename H into HH3 end.
    match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
    match goal with H : stk asegs m3 lo sp1 |- _ => rename H into ST3 end.
    match goal with H : rw_cells asegs m3 (FB + 144) _ |- _ => rename H into CT3 end.
    zstep.
    assert (MU' : munch [(md_p dT2 + 4 * 1, md_p dT2 + 4 * 1 + 4)] m2 m3) by exact MU.
    destruct (limb_store_kit m2 m3 hq LBq _ _ _ _ 3%nat dT2 1 _ CST2 eq_refl OTH2 ltac:(clear - T32; lia) MU' WM HH3 MI3 ST3 ltac:(rewrite EAD2; exact CT3) UAT3 ltac:(apply upd_length)) as (CST3 & _ & UWK).
    cbn [set_nth] in CST3.
    unfold dvDW5_stmt, dvDWg in K5.
    eapply K5 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST3| apply linv_Tl; exact LI2| exact RN| exact NTH| exact QB| | split; reflexivity| exact HK| exact (UWK UW2)| exact BPOS| exact NA98| exact HV| exact HF].
    intros j w J2 NJ. unfold A_mpi_div_mpi_M_c24.set_limbsA in NJ. cbn [md_limbs] in NJ.
    rewrite nth_error_upd_other in NJ by (clear - J2; lia). apply (ZT2 j w ltac:(clear - J2; lia) NJ).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@L28508442243.239L28508442245.237L34785989292.248L39172636981.0  L42967148590.234L48279326478.3  L53517041937.237L55713073078.240L59310730320.9  L59310730321.11 L59310730326.5  L59310730327.10 L59321132280.7  L63346541849.237L8927066273.237 L8927066278.240 L8927066279.239 L8929159528.243 L9356559676.11  Q12088191450.244Q12088239070.247Q12090435434.247Q12388451857.238Q12392695838.240Q1343392926.240 Q15022709143.237Q20537683340.238Q20550345603.240Q22153646565.247Q26295627581.247Q28757581603.240Q38667433655.244Q39033263875.240Q46724285746.240Q50458135125.247Q54608293134.247Q55128416958.247Q58026207754.237Q8945721246.244 00001:02D02l02m04:04E04m05U05g06B06N06i07B07j09E0:W0;i0=;0=f0>E0>d0?C0?i0@O0A50A^0BG0C00CS0Cn0DL0Do0EX0F60FQ0G40GW0H=0HXS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R2Y04NY1'3PY03PYCS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R2Y04NY1'3PY03PYCS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2nySS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y03PY03PYCS2ny3NY12KTS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2nyS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2nyS2dY2ny3NY12KT3KW1S2dY2ny3NY12KT1H2H03KW23PY0S2dY3PY03KW3S2dY2ny3NY14PY163PY02KT3KW4S2dY2ny3NY13NYL4LENY4NTHYS2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2nyS1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NY13NYL2Y04NY1'4PY163PY03PYC3KW1S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NYL2Y04NY1'3PY03PYC3KW1S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NYL2Y04NY1'3PY03PYC3KW1S1R2LF2ra2sp3LFB2FB3sp14gapn1n1Q3dLX2dY2ny3ACV3SPR2F04SP1R3NYL2Y04NY1'3PY03PYC3KW1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB4gapn1n1Q3dLX2dY2ny3KW1S2LF3LFB4gapn1n1Q3dLX2dY2ny3KW1S2LF3LFB4gapn1n1Q3dLX2dY2ny3KW1S2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2nyS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2nyS2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2nyS2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3PY03KW1S2LF3LFB4gapn1n1Q3dLX2dY2nyS2LF3LFB2FB4gapn1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL3KW1S2LF2sp2lo3LFB3sp14gapn3SP11n1Q3dLX2dY2nyS2LF3LFB2FB4gapn1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL3KW1S2LF3LFB4gapn1n1Q3dLX2dY2ny3NYL3KW1S2LF2lo3LFB3sp14gapn3LOC1n1Q3dLX2dY2nyS2LF3LFB4gapn1n1Q3dLX2dY2ny". (* [comment removed for export] *)
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
      zstep. zstep.
      eapply K3 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST| exact LI| exact RN| exact NTH| exact QB| exact ZT| reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
    - (* [comment removed for export] *)
      destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 2))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY NYL NY1 KT; lia].
      zstep. zstep. zstep. zstep. zstep. if_cases KW1; zify_cond KW1; [exfalso; clear - KW1 KT PY0 PYC NY1 NYL; lia|].
      zstep. zstep. zstep. zstep. if_cases KW2; zify_cond KW2;
        [exfalso; clear - KW2 KT PY0 PYC NY1 NYL; repeat match type of KW2 with context [?a <? ?b] => revert KW2; case (Z.ltb_spec a b); intros ? KW2 end;
         cbn [Z.b2z] in KW2; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in KW2; lia|].
      zstep. if_cases KW3; zify_cond KW3; [exfalso; clear - KW3 PY0 PYC; lia|].
      zstep. zstep. if_cases KW4; zify_cond KW4; [exfalso; change 3 with (Z.ones 2) in KW4; rewrite Z.land_ones in KW4 by (clear; lia); clear - KW4 PY16 PY0 PYC KT NY1 NYL; lia|].
      zstep. zstep. shadow_chk OPY (md_p dY + (ny - 2) * 4) 4.
      pose proof (u32arr_read asegs mq (md_p dY) (md_limbs dY) (ny - 2) wy _ UAY NTHY ltac:(clear - NY1 KT; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD. zstep.
      eapply K3 with (i := i) (ny := ny) (k := k) (wq := wq); [exact CST| exact LI| exact RN| exact NTH| exact QB| exact ZT| reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H LSETNG MULNG CMPR slo SLO1 SLO2 SSH0 PF0 FF0"] Lemma dv_DW : forall n, dvL4_stmt n -> forall Q, dvDW_stmt n Q.
  Proof.
    intros n K4 Q. induction Q as [|Q IH].
    - apply dv_DW1, dv_DW2, dv_DW3, dv_DW5; [exact K4| intros Q' E; discriminate E].
    - apply dv_DW1, dv_DW2, dv_DW3, dv_DW5; [exact K4| intros Q' E; injection E as <-; exact IH].
  Qed.

  (* [comment removed for export] *)
  Definition dvLg (n : nat) (pc : Z)
      (RS : mpd -> mpd -> Z -> Z -> word -> word -> word -> word -> word -> word -> word -> word -> Prop) : Prop :=
    forall mq hq LBq dLX dY dZ dT c0 c8 c16 c48 c80 c120 t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq v f (i ny k : Z)
           xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 c48 c80 c120 ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f ->
    linv dLX dY dZ dT i ny -> i - ny <= Z.of_nat n ->
    RS dLX dZ i ny c48 c80 a0 a1 a3 a4 a5 t1 ->
    0 <= k < 32 -> UWCD mq -> 0 < mpd_abs dB -> md_n dA <= 9998 ->
    v + dvVrnd + dvVr n <= PHIb -> f + dvFrnd + dvFr n <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (RGM xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None mq (seg_rom asegs)).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *) (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L11601619207.103L22502704494.103L35497640934.102L35497640934.103L56087813952.104L56093676630.103L8929208426.103 L9068841147.104 00000J00f01@01Z02;02Z03903XS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn1xS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB2FB3sp14gapn1x2Hx1nS2LF2ra2sp3LFB2FB3sp14gapn1x2HxS2LF2ra2sp3LFB2FB3sp14gapn1x2HxS2LF2ra2sp3LFB2FB3sp14gapn1x2Hx". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
  Proof.
    intros x Hx. change 18446744073709551615 with (Z.ones 64).
    rewrite <- Z.ldiff_ones_l_low; [| lia | ].
    2:{ destruct (Z.eq_dec x 0) as [->|]. cbn; lia. apply Z.log2_lt_pow2; lia. }
    rewrite Z.ldiff_land, Z.land_comm, Z.land_ones by lia. unfold Z.lnot.
    rewrite <- (Z.mod_add _ 1) by lia. change (Z.ones 64) with (2^64 - 1). rewrite Z.mod_small; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L33279436385.10400000OS2LF2ra2sp3LFB2FB3sp14gapn1i2ny". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma idx_word : forall i ny, 0 <= ny < 2^64 -> Z_to_bv 64 (i + 1 + Z.lxor ny 18446744073709551615) = Z_to_bv 64 (i - ny).
  Proof.
    intros i ny Hn. rewrite lxor_ones64 by exact Hn. rewrite <- (P_mpi_div_mpi.zbv_add_modulus sp (i - ny)). f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3b_stmt (n : nat) : Prop :=
    dvLg n 0x9fd64 (fun dLX _ i ny c48 c80 a0 _ a3 a4 a5 t1 =>
      c48 = Z_to_bv 64 i /\ c80 = Z_to_bv 64 (i - ny) /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a3 = Z_to_bv 64 (md_p dLX)
      /\ a4 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL) /\ a5 = Z_to_bv 64 1 /\ t1 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38596635253.0000001S".
  #[using="Type"] Lemma dv_shr62 : forall e, 0 <= e < 2 ^ 62 -> Z.shiftr e 62 = 0.
  Proof. intros e He. rewrite Z.shiftr_div_pow2 by (clear; lia). apply Z.div_small. exact He. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L39188636933.0 L51795289313.1900000100QSS1x1c1r2Hr2r12Hx1q2r01H2H02q02H4".
  #[using="Type"] Lemma dv_shr8r : forall x c r, 0 <= r < 8 -> x mod 8 = 0 -> Z.shiftr (x + (8 * c + r)) 3 = Z.shiftr x 3 + c.
  Proof. intros x c r Hr Hx. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8. revert Hr Hx. clear. intros Hr Hx. Z.div_mod_to_equations. lia. Qed.
  Local Ltac dv_fsh C K Rm :=
    replace (Z.shiftr (FB + C) 3 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + K)
      by (assert (Z.shiftr (FB + C) 3 = Z.shiftr FB 3 + K) by (rewrite <- (dv_shr8r FB K Rm) by (clear - F64; lia); f_equal; clear; lia); lia).
  Local Ltac dv_zhelp := repeat match goal with |- context [Z.shiftr ?e 62] => rewrite (dv_shr62 e) by zlia end.
  Local Ltac zchk_fails ::= constr:([A_MPI_DIV_MPI_E + 3884]).
  Local Ltac zstep ::= zpre; step; zsimp; dv_zhelp; zpre.
  Local Ltac dv_chunks CHq :=
    let C := fresh "CHq'" in
    pose proof CHq as C; unfold A_mpi_div_mpi_C.DCS in C;
    apply Forall_cons_iff in C; destruct C as [SPC C]; apply Forall_cons_iff in C; destruct C as [T2Cq C]; apply Forall_cons_iff in C; destruct C as [ZCq C];
    apply Forall_cons_iff in C; destruct C as [CZCq C]; apply Forall_cons_iff in C; destruct C as [GAPC C]; apply Forall_cons_iff in C; destruct C as [SAVE C];
    apply Forall_cons_iff in C; destruct C as [FHD C]; apply Forall_cons_iff in C; destruct C as [Z32C C]; apply Forall_cons_iff in C; destruct C as [Z48C C];
    apply Forall_cons_iff in C; destruct C as [Z64C C]; apply Forall_cons_iff in C; destruct C as [TPC C]; apply Forall_cons_iff in C; destruct C as [JQC _];
    cbn [fst snd] in SPC, T2Cq, ZCq, CZCq, GAPC, SAVE, FHD, Z32C, Z48C, Z64C, TPC, JQC; unfold A_mpi_div_mpi_C.dv_sp in SPC.

  Local Ltac2 Set LiaOrc.tbl := fun () => "04C0@C7096915042.281 D2216271572.279 D33876909647.279D35300034347.271D35515137683.264D60189065437.271D62883116959.264D62883116959.267D62883116959.274D6645954592.267 D6645954592.274 K12278670331.282K15835051771.281K21870859916.281K22945712379.281K30347570235.281K44651977723.281K45774582958.264K45774582958.267K45774582958.274K66327680928.264K66327680928.267K66327680928.274K66327680928.281L10353723466.4  L10869547493.171L1226287630.258 L12265645300.4  L12303521380.261L12303521380.264L14354071846.1  L14447004729.2  L14449150449.4  L14793915263.2  L14796357303.4  L15278480665.255L15465599222.259L15822417165.1  L15822811636.4  L16000728743.6  L1685717371.0   L16896526054.1  L18888483069.171L19561689303.2  L21866058115.4  L21866712442.1  L2230640144.175 L22510978493.12 L22940782580.4  L22941438733.1  L24663763785.254L24664289724.168L24664289724.169L24664307378.171L25379465539.12 L26985680806.1  L27588716945.2  L27637064285.5  L27707769983.3  L28632618922.2  L28786337297.2  L29832375856.1  L30334282548.4  L30334941133.1  L31145622673.2  L31160754072.169L31486203162.12 L31688505692.169L31940060916.175L32171172728.175L32172768967.264L32321742194.5  L32418217581.2  L33177588698.259L34055563380.266L34080941563.2  L34900348238.169L35908285640.168L35908285640.169L36511010743.5  L36523706914.3  L36571201320.0  L36577269016.12 L36766760858.2  L38259954321.2  L38603518414.265L39172636981.0  L39934933784.12 L40064506039.4  L40066129279.2  L40234857116.175L41247884433.4  L41807682882.3  L42113020712.1  L42624411411.2  L42690912751.2  L44656115725.1  L44656516340.4  L45657748817.2  L45777250370.2  L45779514273.4  L46190619535.260L47415570738.257L47805194247.265L48700858022.1  L48773294933.254L48790513818.169L49759334170.12 L50160111710.169L50863131871.255L50981599394.11 L53518944813.264L54080989308.168L55148681496.12 L55348327217.2  L55461957149.1  L55815189670.1  L55990716303.255L5606672193.1   L56249019699.169L57698627611.2  L59321132281.6  L59321132283.8  L59323229392.8  L59667784614.1  L59975262609.2  L60953215123.3  L61614513008.175L6178455275.4   L61795903927.4  L61798214783.2  L63172243738.12 L64047791002.265L64543491215.2  L64713462746.258L66332508238.2  L66332610735.3  L6682157388.169 L7026953071.168 L7026953071.169 L7716192930.175 L7737532928.4   L7738195705.2   L8331041601.1   L8927014434.175 L8927557799.265 L8927575063.255 L8929093992.169 L8929111654.171 L8929159528.258 L8929159528.260 L8929159528.268 L8929620893.264 L9356559676.11  P14461423358.264P14461423358.267P14461423358.274P14461423358.282P14783166904.264P14783166904.267P14783166904.274P14783166904.281P27590552406.271P28627113325.271P28773282303.271P31146933846.271P32425075329.271P36523116728.264P36523116728.267P36523116728.274P36523116728.281P38261788758.271P40077402040.264P40077402040.267P40077402040.274P40077402040.281P45659584406.271P45774582958.264P45774582958.267P45774582958.274P45774582958.280P45774582958.282P57713046236.271P59963990870.271P61800574648.264P61800574648.267P61800574648.274P61800574648.281P61800574648.282P66327680928.281P7750690063.264 P7750690063.267 P7750690063.274 P7750690063.281 Q10812129647.274Q11801279589.264Q11801279589.267Q11801279589.271Q11801279589.274Q11801279589.279Q13396307760.271Q19361811857.266Q19361811857.273Q20122760503.264Q20122760503.271Q20612482221.271Q2216526553.276 Q2218480852.281 Q2229126692.274 Q2231059088.274 Q2231109781.271 Q22537500579.266Q24839708456.265Q26295627581.264Q26295627581.266Q26295627581.274Q27494214828.264Q28074340950.261Q28465177121.268Q28981407372.263Q30354477985.264Q30354477985.266Q31311148087.270Q31760482915.266Q31760682198.263Q31762679511.266Q33874924623.281Q33877164610.276Q33889765055.274Q3421936230.270 Q38968267957.265Q39686552230.260Q41261513261.271Q41262017704.265Q44278218633.261Q44278218633.263Q45714648102.270Q45989664010.267Q49472925079.260Q49698585326.262Q49698585326.265Q49698585326.272Q49698585326.280Q50160717600.264Q50162387860.264Q50162713889.261Q50458135125.264Q50458135125.266Q50458135125.274Q51003780618.260Q51335846007.271Q5265442331.269 Q52744951088.263Q52744951088.266Q52744951088.273Q55535214433.264Q55535214433.266Q57228775306.270Q5939317587.260 Q5939828392.263 Q60635441820.265Q61424693930.279Q61435199010.274Q62413858999.260Q67119445988.263Q67126186956.265Q67127742067.260Q67128284040.263Q67304644247.267Q7368538544.271 Q7369010997.265 Q8344907421.263 Q8945605423.261 Q8945605423.263 Q8945622943.271 00000101>02Q04905106Y07Q08J09B0:;0;30;j0<a0=X0>O0?F0@=0A40Al0Bc0CZ0DR0EI0EJ0EX0F[0GA0GB0HJ0IR0IV0IW0IX0IY0IZ0J@0KI0KM0KN0Kc0Kd0Kh0Lj0M20M30M70N:0Nc0Nd0Nh0P10Q30R50S70S<0SA0SB0ST0S]0S^0S_0Sc0Sd0Sh0Si0Tl0U00V80V[0X20YP0Yb0Yc0[A0\I0\S0]Z0^S0_N0_O0_P0_Q0`:0`B0`C0`i0`j0aS0aT0aU0bX0bf0bm0c10c80c<0c@0cA0cB0cC0cD0cj0e30fQ0fV0h40hW0h[0i^0jD0jm0kS0lT0m=0mC0mG0mL0n20n70o90o:0oQ10110R10V10W10c10d11111211311711]11a12G12H12I12J12l13N14e14f14g14l16C17a19G1:f1<E1=k1?Q1@o1BM1C81DK1E_1G21HD1IW1Jk1L>1MP1Nb1P41QI1R[1T:1UM1Va1X41YF1ZX1[k1]?1^R1_d1a61ah1b[1cM1cN1cO1dD1eV1fi1h=1iP1jb1l41l51m@1nL1oW20a21J22822g23U24C24a25E26426b27D27f28M29029V2:92:\2;?2;f2<M2<f2=?2=X2>?2>a2?F2?b2@E2@h2AD2Ag2BJ2Bm2CY2DB2Dk2Ec2FG2Fc2GJ2H12HT2I72IS2J72J^2KC2Kh2LM2M@2Mc2NF2Ni2OD2O_2P:2P^2QG2Qm2R[2SJ2T82T[2U>2V32VO2Vk2WG2Wn2XU2Y12Y_2Z;2ZW2[32[Z2\>2\b2]>2]W2^02^IFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R2wv3NY12X03PX02Z03PZ03IDXS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R2wv3NY13INA2NZ2X03PX02Z03PZ0S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n2hq3dLX2dZ1i2ny3SPR2F04SP1R3HTq2X03PX02Z03PZ02HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny2a62HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3SPR2F04SP1R2X03PX02Z03PZ02HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny2a62HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3wx12HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny2wx2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3wx12HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a64LENX3PXF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx14LENX3PXF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx4LENX3PXF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a64LENZ3PZF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx14LENZ3PZF2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx4LENZ3PZF2HB5Ha_st5Hl_stFS1i2ny3NY13NYIS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X03PX02Z03PZ03IDXS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyFS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3SPR2F04SP1R3NY12X03PX02Z03PZ01HS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3SPR2F04SP1R3NY12X03PX02Z03PZ01HS2FBFFFFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S2FBFS2dA1i2ny3NY13NYI3INASS2FBS1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S2FB3F64FS2FBS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X03PX02Z03PZ03IDXS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FS2FBS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S3sp1S3sp1FS2dZ1i2ny4LENZ3IDXS2dZ1i2nyFFS2dZFS2FBFS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X03PX02Z03PZ03IDXS2FBS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X04PX163PX02Z03PZ03IDXS2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3PZ0S1R2ra2sp2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS2dZ1i2ny4LENZ3IDXFS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Z03PZ03PZCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3SPR2F04SP1R3NY12X03PX02Z03PZ01HS3sp14gapnS1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F04SP1R2X03NX13PX03PXC2Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3SPR2F04SP1R2X03PX02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R2X03PX02Z03PZ0FFSS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2FB3F64FS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nySS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1FFS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X03PX02Z03PZ03IDXS1i2ny3NY13NYIS2wv2MBS2FBS3dLX1iS2FBS2FBFFFFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Z03PZ03PZCS3sp1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3PX0S2FBS2ra2sp2FB3sp14gapn1n3dLX2dZ1i2ny3SPR2F04SP1R3NY12X03PX02Z03PZ03IDXS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS2ra2sp2FB3sp14gapn3FB81n3dLX2dZ2ny3SPR2F04SP1R3NY12X03PX02Z03PZ0S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1i2nyS2FBS3sp1S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS3sp1S1R2ra2sp2FB3sp14gapn1n3dLX2dZ2ny3ACV3SPR2F02F14SP1R2X03PX02Z03PZ0FS2dZ1i2ny4LENZ3IDX4NTHZS3dLX1i2ny3NY13NYI3IXL4LENX4NTHXS3dLX1i2ny3NY13NYI3IXL4LENX5NTHX1S2dZFS2sp3sp13SP1FS2dZ1i2ny3IDXFFS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyS2FBS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ2nyFFFS2ra2sp2FB3sp14gapn1n3dLX2dZ2ny2F0S2ra2sp2FB3sp14gapn1n3dLX2dZ2ny2F0S1R2ra2sp2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Z03PZ03PZCFFS3sp1S1R2ra2sp2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03NX13PX03PXC2Z03PZ03PZC3IDXS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03NX13PX03PXC2Z03PZ03PZC3IDXS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03NX13PX03PXC2Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03NX13PX03PXC2Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03NX13PX03PXC2Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3ACV3SPR2F04SP1R3NY13INA2NZ2X03PX02Z03PZ03PZC3IDXS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO4LENZ3PZC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F13EAX2HB5Ha_st5Hl_st4LENX3PXCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a63EAX2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx13EAX2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx3EAX2HB5Ha_st5Hl_stFFS2LF2sp3LFB3sp14gapn3SP11n3dLX2dZ1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2dZ2ny2a63ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2dZ2ny3ALO2F13wx12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB4gapn1n3dLX2dZ2ny3ALO2F12wx2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dZ1i2ny3ALO2wv3NY13INA2NZ3PZCS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a62HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx12HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dZ1i2ny2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dZ1i2ny2wvS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2F02HBS2LF3LFB2FB4gapn1n3dLX2dZ2ny2F02HBS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny2wv3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PX03IDXS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PX03IDXS2LF3LFB2FB4gapn1n3dLX2dZ2ny2F02HBS2LF3LFB3sp14gapn1n3dLX2dZ2ny4SP1R2HBS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny2wv3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ1i2ny2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2ny2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2HB5Ha_stS1R2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3ACV3NY13INA2NZ3PZCS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2nyS2LF3LFB4gapn1n3dLX2dZ1i2nyS2LF3LFB4gapn1n3dLX2dZ1i2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3NY13INA2NZS2LF3LFB3sp14gapn1n3dLX2dZ2ny2HB5Ha_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a62HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny3wx12HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2ny2wx2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13IXLS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ1i2ny2HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PZ03IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3NY13PZ03IDXS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2ny2a62HB5Ha_st5Hl_stS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2nyS2LF3LFB4gapn1n3dLX2dZ2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_L3b : forall n, (forall Q, dvDW_stmt n Q) -> dvL3b_stmt n.
  Proof.
    intros n KDW. unfold dvL3b_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & -> & ->). kit_pre CST mq hq. dv_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX).
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    assert (CWZ : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (md_p dZ) (4 * md_n dZ))
      by (eapply client_wrange_block; [apply in_or_app; left; exact INZ| clear; lia| clear; lia]).
    destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 1))) as [wx1|] eqn:NTHX1; [| apply nth_error_None in NTHX1; exfalso; clear - NTHX1 LENX IXL NY1 NYI; lia].
    destruct (nth_error (md_limbs dLX) (Z.to_nat i)) as [wx|] eqn:NTHX; [| apply nth_error_None in NTHX; exfalso; clear - NTHX LENX IXL NY1 NYI; lia].
    assert (IDX : 0 <= i - ny < md_n dZ) by (rewrite NZ; clear - NY1 NYI INA; lia).
    destruct (nth_error (md_limbs dZ) (Z.to_nat (i - ny))) as [wz|] eqn:NTHZ; [| apply nth_error_None in NTHZ; exfalso; clear - NTHZ LENZ IDX; lia].
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWTP : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 176) 12) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (munch_refl [(FB + 176, FB + 188)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    cbv [DV_FSH app] in SHq.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    dv_fsh 176 22 0.
    zstep. zstep. zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    replace ((i + 1) * 4 + md_p dLX + -8) with (md_p dLX + 4 * (i - 1)) by (clear; lia).
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    shadow_chk OPX (md_p dLX + 4 * (i - 1)) 4.
    zstep. zstep. zstep.
    dv_fsh 180 22 4.
    zstep.
    pose proof (u32arr_read asegs _ (md_p dLX) (md_limbs dLX) (i - 1) wx1 _ UAX NTHX1 ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. zstep.
    zstep. zstep. zstep.
    shadow_chk OPX (md_p dLX + 4 * i) 4.
    zstep. zstep. zstep.
    dv_fsh 184 23 0.
    zstep.
    pose proof (u32arr_read asegs _ (md_p dLX) (md_limbs dLX) i wx _ UAX NTHX ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. zstep.
    replace (Z.land (FB + 184) 7) with 0 by (rewrite zchk_land7; clear - F64; lia).
    zstep. zstep.
    zstep. zstep. zstep.
    rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. replace ((i - ny) * 4) with (4 * (i - ny)) by (clear; lia).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (CST1 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) c120 ny k t2pad czp czpad gb z32 z48 z64 a6 (sx32 wx1) u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := FB + 176) (b := FB + 188); try eassumption.
      - clear; lia.
      - right. clear. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW1 : UWCD m2).
    { eapply M_uwcd_munch; [exact UW| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    clear MU WM. pose proof (munch_refl [(sp1 + 120, sp1 + 128)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (CST2 : CSTA m3 hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 a6 (sx32 wx1) u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := m2) (a := sp1 + 120) (b := sp1 + 128); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m3) by (eapply S_uwcd_store; [exact UW1| exact MU| clear; lia]).
    clear MU WM. pose proof (munch_refl [(FB + 176, FB + 188)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. replace (4 * (i - ny) + md_p dZ) with (md_p dZ + 4 * (i - ny)) by (clear; lia).
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (CST3 : CSTA m4 hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) (Z_to_bv 64 (4 * (i - ny))) ny k t2pad czp czpad gb z32 z48 z64 a6 (sx32 wx1) (sx32 wx) jq) DV_FSH v f).
    { eapply S_cs_store with (mq := m3) (a := FB + 176) (b := FB + 188); try eassumption.
      - clear; lia.
      - right. clear. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW3 : UWCD m4).
    { eapply M_uwcd_munch; [exact UW2| exact MU|]. apply Forall_cons; [cbn [snd]; clear - F1 ALO LOS SLO SP1 NEEDR; lia| apply Forall_nil]. }
    clear MU WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    shadow_chk OPZ (md_p dZ + 4 * (i - ny)) 4.
    pose proof (u32arr_read asegs _ (md_p dZ) (md_limbs dZ) (i - ny) wz _ UAZ NTHZ ltac:(clear - IDX; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD. zstep.
    pose proof (munch_refl [(md_p dZ + 4 * (i - ny), md_p dZ + 4 * (i - ny) + 4)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    pose proof (u32arr_store_ok asegs _ (md_p dZ) (md_limbs dZ) (i - ny) _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs m4 (md_p dZ) (md_limbs dZ) (i - ny) vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m5 |- _ => rename H into HH5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    match goal with H : stk asegs m5 lo sp1 |- _ => rename H into ST5 end.
    match goal with H : rw_cells asegs m5 (sp1 + 184) _ |- _ => rename H into CZ5 end.
    destruct (limb_store_kit m4 m5 hq LBq _ _ _ _ 2%nat dZ (i - ny) _ CST3 eq_refl OZH IDX MU WM HH5 MI5 ST5 ltac:(rewrite EAZ; exact CZ5) UAZ' ltac:(apply upd_length)) as (CST4 & _ & UWK).
    cbn [set_nth] in CST4.
    eapply (KDW (Z.to_nat (2^32))) with (i := i) (ny := ny) (k := k) (wz := wv); [exact CST4| apply linv_Z; exact LI| exact RN| | | exact HK| exact (UWK UW3)| exact BPOS| exact NA98| exact HV| exact HF].
    - unfold A_mpi_div_mpi_M_c24.set_limbsA. cbn [md_limbs]. apply nth_error_upd_same. clear - IDX LENZ. lia.
    - rewrite Z2Nat.id by (clear; lia). pose proof (Z.mod_pos_bound (w32 wv - 1) (2^32) ltac:(clear; lia)) as MB. clear - MB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *) (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL3a_stmt (n : nat) : Prop :=
    dvLg n 0x9fd08 (fun dLX _ i ny c48 c80 a0 _ a3 a4 a5 t1 =>
      c48 = Z_to_bv 64 i /\ c80 = Z_to_bv 64 (i - ny) /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a3 = Z_to_bv 64 (md_p dLX)
      /\ a4 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL) /\ a5 = Z_to_bv 64 1 /\ t1 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L28463817154.158L31160753818.158L31688505438.158L34900347980.158L35908285898.158L39172636981.0  L48790514072.158L50160111964.158L54968207265.2  L59321132283.6  L60358257857.2  L6261078406.227 L66253707781.225L6682157134.158 L6960165442.227 L8929093738.158 L8929159528.230 L8941826058.227 L9356559676.11  Q13398550429.231Q1433360151.228 Q20610763776.231Q26295627581.234Q27494214828.234Q30354477985.234Q3853489290.228 Q44288275348.231Q50147674428.231Q50160717600.234Q50162387860.234Q50458135125.234Q55535214433.234Q8956254002.231 00001201j02g03d04U04V05605n06406L06S07\08j08k0:40;:0<G0=T0>?0>`0?D0?h0@>0@a0A=0A^0B:0BY0C80CW0Co0DK0DaS1R2ra2sp2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3IXL2X03PX03PXC2KIS2ra2sp2FB3sp14gapn1n3dLX1i2ny3SPR2F04SP1R3NY12X03PX02KIS2ra2sp2FB3sp14gapn1n3dLX1i2ny3SPR2F04SP1R3NY12X04PX163PX02KIS1R2ra2sp2FB3sp14gapn1n3dLX2ny3ACV3SPR2F04SP1R2X03NX13PX03PXCS2ra2sp2FB3sp14gapn1n3dLX1i2ny3SPR2F04SP1R2X03PX0SS2ra2sp2FB3sp14gapn1n3dLX2ny3PX0S2ra2sp2FB3sp14gapn1n3dLX1i2ny3SPR2F04SP1R3NY12X03PX02KIS1i2KIS3dLX1i3IXL4LENX2KI4NTHXS3dLX1iS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3IXL2X03PX03PXC2KIS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13NYI3IXL2X03PX03PXCFS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3IXL2X03PX03PXC2KIS1R2ra2sp2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13IXL2X03PX03PXC2KIS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13IXL2X03PX03PXC2KIS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX1i2ny3ACV3SPR2F04SP1R3NY13IXL2X03PX03PXC2KIS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2nyS2LF3LFB4gapn1n3dLX2nyS2LF3LFB4gapn1n3dLX1i2ny3NY13PX02KIS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF2lo3LFB3sp14gapn3LOC1n3dLX2nyS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2ny3NY12KIS2LF3LFB4gapn1n3dLX1i2nyS2LF3LFB4gapn1n3dLX1i2ny3IXLS2LF3LFB4gapn1n3dLX2ny". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64"] Lemma dv_L3a : forall n, dvL3b_stmt n -> dvL3a_stmt n.
  Proof.
    intros n KB. unfold dvL3a_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
    dpose LI as (EAX & EAY & EAZ & EAD & OXH & OYH & OZH & OTH & NY1 & NYI & INA & IXL & NYL & NZ & NT & YB & XB).
    edestruct K_local_facts with (mq := mq) (i := 0%nat) (d := dLX) as (MLX & NSX & _ & _ & _ & _ & HFX & _ & X8 & _ & OXs); try eassumption; [reflexivity|].
    pose proof MLX as [(CX & _ & X0 & LENX & NRX & OWX) SGX]. rewrite OXH in OWX. ddestruct OWX as (NX1 & INX & PX16 & UAX).
    ddestruct (HFX OXH) as (PX0 & PXC & _ & _ & PXF & _).
    assert (OPX : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dLX) (4 * md_n dLX)) by (eapply hm_aobj_block; [exact HHq| exact INX]).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    unfold dvL3b_stmt, dvLg in KB.
    (* [comment removed for export] *)
    zstep. zstep. zstep; if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by (clear - NY1 NYI INA NA98; lia).
    - destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 2))) as [wx|] eqn:NTHX; [| apply nth_error_None in NTHX; exfalso; clear - NTHX LENX IXL KI; lia].
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      replace (md_p dLX + (i + -2) * 4) with (md_p dLX + 4 * (i - 2)) by (clear; lia).
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep.
      shadow_chk OPX (md_p dLX + 4 * (i - 2)) 4.
      pose proof (u32arr_read asegs mq (md_p dLX) (md_limbs dLX) (i - 2) wx _ UAX NTHX ltac:(clear - KI; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      eapply KB with (i := i) (ny := ny) (k := k); [exact CST| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
    - zstep. zstep.
      eapply KB with (i := i) (ny := ny) (k := k); [exact CST| exact LI| exact RN| repeat split; reflexivity| exact HK| exact UW| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L18932531241.10300000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma zbv_add_k : forall x k, Z_to_bv 64 (x + k * 18446744073709551616) = Z_to_bv 64 x.
  Proof.
    intros x k. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition dvL2_stmt (n : nat) : Prop :=
    dvLg n 0x9fd04 (fun dLX dZ i ny c48 c80 a0 a1 a3 a4 a5 t1 =>
      c48 = Z_to_bv 64 i /\ c80 = Z_to_bv 64 (i - ny) /\ a0 = Z_to_bv 64 (md_p dLX + 4 * i) /\ a1 = Z_to_bv 64 (md_p dZ + 4 * (i - ny))
      /\ a3 = Z_to_bv 64 (md_p dLX) /\ a4 = Z_to_bv 64 (Z.shiftr (md_p dLX + 4 * i) 3 + al_sb AL) /\ a5 = Z_to_bv 64 1
      /\ t1 = Z_to_bv 64 (i + 1)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@C7096915042.236 D33876909647.235D63873442836.235K21870859916.237K22945712379.237K66327680928.236L12469921329.0  L14447101554.5  L14794338612.5  L16000728743.6  L1685717371.0   L19133426325.6  L21868076544.5  L22938730615.5  L29832375856.1  L36508794932.6  L40066488116.5  L59667784614.1  L61798049332.5  L66330468140.4  L7735389571.5   L9356559676.11  P14461423358.237P14783166904.237P36523116728.237P40077402040.237P61800574648.237P66327680928.236P7750690063.237 Q11801279589.235Q19991027068.237Q33874924623.236Q33877164610.231Q48467890406.237Q49698585326.235Q51135677050.234Q63871233556.236Q63873185817.23100000101A02K03F04304404504604704L04M04c04d04e04i04j04k04o05005105205]06i08?09U0:a0;m0;n0=<0=^0=_0>O0?<0?=0?j0@U0A?0AfFS2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY13INA2NZ2Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dZ1i2ny3idx3SPR2F04SP1R2wv3NY12Z03PZ03IDXS2LF3LFB2dA2FB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZ3PZF3IDXS2LF3LFB2FB4gapn1n3dLX2dZ1i2ny3idx2wv3PZF3IDXFFFFS2dA1i2ny3NY13NYI3INASS2dZ1i2ny3idx4LENZ3IDXFFS2dZFFS2dZFFFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3PZC3IDXS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dZ1i2ny3idx3ALO2wv3PZC3IDXFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3ALO2wv3NY13INA2NZ3PZCS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wvFS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx2wv3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dZ1i2ny3idx3NY13INA2NZFS1R2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3ACV3PZC3IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13PZ03IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx2wv3NY13IDXS2LF3LFB4gapn1n3dLX2dZ1i2ny3idx3NY13IDX". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64 FB8"] Lemma dv_L2 : forall n, dvL3a_stmt n -> dvL2_stmt n.
  Proof.
    intros n KA. unfold dvL2_stmt, dvLg. intros until t6. intros CST LI RN RS HK UW BPOS NA98 HV HF. ddestruct RS as (-> & -> & -> & -> & -> & -> & -> & ->). kit_pre CST mq hq. kit_chunks CHq.
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
    pose proof (u32arr_store_ok asegs mq (md_p dZ) (md_limbs dZ) idx _ UAZ ltac:(clear - IDX LENZ; lia) ltac:(f_equal; clear; lia)) as SOKw.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?vv)] =>
      pose proof (u32arr_write asegs mq (md_p dZ) (md_limbs dZ) idx vv UAZ ltac:(clear - IDX LENZ; lia)) as UAZ'; set (wv := vv) in * end.
    store_done.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    match goal with H : rw_cells asegs m2 (sp1 + 184) _ |- _ => rename H into CZ2 end.
    destruct (limb_store_kit mq m2 hq LBq _ _ _ _ 2%nat dZ idx _ CST eq_refl OZH IDX MU WM HH2 MI2 ST2 ltac:(rewrite EAZ; exact CZ2) UAZ' ltac:(apply upd_length)) as (CST2 & _ & UWK).
    cbn [set_nth] in CST2.
    unfold dvL3a_stmt, dvLg in KA.
    eapply KA with (i := i) (ny := ny) (k := k); [exact CST2| apply linv_Z; exact LI| exact RN| repeat split; reflexivity| exact HK| exact (UWK UW)| exact BPOS| exact NA98| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03X0@D35300034347.284D35300034347.289D60189065437.284D60189065437.289L10169803483.2  L10353723466.4  L12376170316.5  L12469921329.0  L13743515073.1  L14557301081.185L1685717371.0   L20733292093.189L20733292094.187L2230640144.187 L2230640147.189 L2591472616.288 L26985680806.1  L27588716945.2  L28456661569.1  L28505741378.185L28505741378.275L28632618922.2  L28786337297.2  L31145622673.2  L31162833106.187L31409735961.274L31528481419.185L31688505821.183L31688523346.185L31690620437.189L31690620438.187L31748969496.12 L31763290408.183L31940060916.187L31940060919.189L32171172728.187L32171172731.189L32172570698.278L32172571597.281L32418217581.2  L32622295223.185L32867401788.278L32876037132.6  L33179470056.278L33179470703.281L34080941563.2  L34785933159.2  L34897664049.273L34898266628.187L34900348367.183L35203387009.280L35908268998.185L35908285513.183L35910366081.189L35910366082.187L37056898846.183L38259954321.2  L39172636981.0  L40234857116.187L40234857119.189L41247884433.4  L41661770456.278L42011311069.3  L45657748817.2  L46190619535.279L46190619535.282L47663730673.185L47803461040.278L47803461175.281L48574312970.187L48700858022.1  L48788434896.187L50162226964.187L51970675011.12 L52064949411.273L52860930961.2  L53516912039.273L53518407638.275L53519142048.278L53519142695.281L55815189670.1  L57444257313.2  L57698627611.2  L59321132280.6  L59323229416.8  L59323229417.8  L59975262609.2  L60539411773.183L60681291923.3  L61614513008.187L61614513011.189L61997691801.2  L62657810409.2  L63344671256.12 L63346541849.276L63436913239.4  L64991703782.183L65029001240.12 L66255411083.273L66794228432.185L6684272134.187 L68145906413.7  L7716192929.189 L7716192930.187 L8700593567.288 L8927014433.189 L8927014434.187 L8927460375.273 L8929094121.183 L8929111654.185 L8929111654.275 L8929159528.276 L8929159528.279 L8929159528.281 L8929162512.278 L8929162903.281 L8929163528.284 L9356559676.11  L9414061457.2   P27590552406.285P27590552406.289P28627113325.285P28627113325.289P28773282303.284P28773282303.289P31146933846.285P31146933846.289P32425075329.284P32425075329.289P38261788758.285P38261788758.289P45659584406.285P45659584406.289P52851231062.285P52851231062.289P57432086862.284P57432086862.289P57713046236.285P57713046236.289P59963990870.285P59963990870.289P9427955542.285 P9427955542.289 Q10812129573.292Q10812129647.289Q11801279589.284Q11801279589.289Q11968186855.285Q12388454016.289Q13394305280.289Q13394305671.286Q13396274048.281Q1433360151.281 Q15234078760.285Q15902026880.289Q15904470070.288Q16827575549.285Q20014132204.283Q20537681181.289Q20612382749.281Q20614875418.286Q20614875805.289Q2228978978.286 Q2228979365.289 Q2231059088.289 Q2231059162.292 Q22537500579.284Q22632467622.281Q24840799258.286Q24840800157.289Q25954107624.285Q26295627581.284Q26295627581.287Q26295627581.289Q26295631709.292Q27494214828.289Q28465177121.282Q28465177121.286Q28770550092.283Q30354477985.284Q30354477985.289Q31760482915.284Q31760482915.286Q31760600278.281Q3421936230.284 Q3421936230.288 Q3853489290.281 Q38669678599.284Q38967168000.289Q38967168903.286Q41259840541.289Q41259841434.286Q41262017704.285Q43215146679.281Q44275611278.286Q44278103945.281Q46711053149.283Q50160307238.286Q50160717600.289Q50162387860.289Q50458135125.284Q50458135125.287Q50458135125.289Q50458139189.292Q51338106304.286Q51338106439.289Q5265442331.283 Q5265442331.287 Q54608293134.287Q55128416958.286Q55533542357.286Q55535214433.289Q57228775306.284Q57228775306.288Q60189065437.285Q61435194946.292Q61435199010.289Q64053772401.283Q66791183892.287Q66793640608.284Q66793640608.286Q67148154653.289Q67150340011.288Q7366603783.286 Q7366604672.289 Q7369010997.285 Q8943472942.284 Q8943620527.289 Q8943620648.286 Q8945589039.281 Q9877412789.285 Q9992779027.287 00001b03T05F07807?07M07Z07[07`08g08h09N0:40;A0<N0=70=<0==0=B0>T0?m0?n0?o0@00A=0Af0BL0C^0Dj0F<0GS0H<0II0Io0JU0L60MW0O?0Pn0Po0Q00RX0Rd0TL0V;0VE0VL0Wd0Y50ZF0ZG0[J0\O0]T0^Y0_f0_g0_h0a50bB0bP0d80dA0dB0dk0e[0fA0gi0iX0k90k>0kd0m10m60n^0n_0oH10110Z11J11O11P11Q11j12K12l12m14N14Z14[14\14d14k15T16=16H16I17218Z19a19b1:<1;]1=>1=?1>`1@I1B91Cb1E<1F]1HM1In1K^1MN1O=1Pl1QW1QX1Rm1TB1UW1Vl1XD1Y\1[11\F1]^1_61`K1a`1c51dJ1e_1g41hL1id1j\1kT1li1n>1oS20h21[22G23823i25>25l26Z27A27h28R29<29j2:Q2:R2;<2;m2<W2=A2>22>X2?E2?k2@X2AB2Aa2BK2C<2C=2CY2D52DQ2E42E^2FF2Fn2GM2H32HY2I?2Ie2JK2KF2LA2Lh2MM2N;2Nb2OS2P=2Pg2QF2Ql2RR2S12SW2T=2Tc2UA2U]2V;2V`2WL2X?2Xh2YQ2Z62Z[2[A2[g2\_2]W2^b2_S2`=2`d2aD2ad2bD2c52c_2dF2e42e[2f72fZ2g62gR2h92h]S1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n2hq3dLX2dY2dZ1i2ny3SPR2F04SP1R3HTq2X03PX02Y03PY02Z03PZ02HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2FB3sp14gapn3GAP1n2hq3dLX2dY2dZ1i2ny3SPR2F04SP1R3HTq2X03PX02Y03PY02Z03PZ02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ02HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ02HB5Ha_st5Hl_stS3dLX1iS1i2ny3NY13NYIS4PHIb1n1v2HVFS3sp1S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3SPR2F04SP1R3NY12X03PX02Y03PY02Z03PZ0SS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS3sp1FS3sp1S1R2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R2X03PX02Y04NY1'3PY03PYC2Z03PZ0S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R2X03PX02Y04NY1'3PY03PYC2Z03PZ0FFFS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PY0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X04PX163PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3SPR2F04SP1R3NY12X03PX02Y04PY163PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z04PZ163PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z04PZ163PZ04PX16S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PZ0S1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3wxi2wyFFS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS3FRb1n1f2HFS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3wxi2wyS3sp14gapnS2dY2nyS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R2X03NX13PX03PXC2Y03PY02Z03PZ0S1R2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R2X03NX13PX03PXC2Y03PY02Z03PZ0S1R2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R2X03NX13PX03PXC2Y03PY02Z03PZ0FS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0FSS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S1i2ny3NY13NYIS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS2dZ1i2nyFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3wxi2wyS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PY0S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3wxi2wyS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS3sp1S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3PX0S2ra2sp2FB3sp14gapn1n3dLX2dY2dZ1i2ny3SPR2F04SP1R3NY13NYI2X03PX02Y03PY02Z03PZ0S3sp1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCFS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3wxi2wyS3sp1FFS2dY2ny3NY13NYL4LENY4NTHYS3dLX1i2ny3NY13NYI3IXL4LENX5NTHXIS3dLX1i2ny3NY13NYI3IXL4LENX5NTHXJFS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS2sp3sp13SP1FFS2ny3NY1S3dLX1iS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2nyS1n1i2ny2RNFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3SPR2F04SP1R3NY12X03PX02Y03PY02Z03PZ0FS2dA1i2ny4NA983NY13NYI3INAS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCFS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZCS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3NX13PXCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03NX13PX03PXC2Y03PY02Z03PZ03PZCS1R2ra2sp2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03NX13PX03PXC2Y03PY02Z03PZ03PZCS1R2ra2sp2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R3NY13NYL2X03PX02Y04NY1'3PY03PYC2Z03PZ0S1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R3NY13NYL2X03PX02Y04NY1'3PY03PYC2Z03PZ0S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03NX13PX03PXC2Y03PY02Z03PZ03PZCS1R2LF2ra2sp3LFB2FB3sp14gapn1n3dLX2dY2dZ2ny3ACV3SPR2F04SP1R3NY13NYL2X03PX02Y04NY1'3PY03PYC2Z03PZ0S1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3NX13PXCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3NX13PXCS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3wxi2wyS1R2LF2ra2sp3LFB2dA2FB3sp14gapn1n3dLX2dY2dZ1i2ny3ACV3SPR2F04SP1R3NY13NYI3INA2NZ2X03PX02Y03PY02Z03PZ03PZC3wxi2wyS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENZ3PZC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENZ3PZC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENX3PXC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENY3PYC2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO4LENY3PYC2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF2sp3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF3LFB2dA4gapn1n3dLX2dY2dZ1i2ny3NY13INA2NZ3wxi2wyS2LF3LFB2dA4gapn1n3dLX2dY2dZ1i2ny3NY13INA2NZS2LF3LFB3sp14gapn1n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF3LFB3sp14gapn1n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp14gapn3SP11n3dLX2dY2dZ1i2ny3ALO2F12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2ny3wxi2wyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2ny3wxi2wyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2ny3wxi2wyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyFS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2ny3wxi2wyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2ny3wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3PX0S2LF3LFB2FB4gapn1n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2ny3wxi2wyFS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2ny3wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3PX0S2LF3LFB3sp14gapn1n3dLX2dY2dZ2ny4SP1R2HBS2LF3LFB3sp14gapn1n3dLX2dY2dZ2ny4SP1R2HBS2LF3LFB2FB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2ny3NYL4NY1'S2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2ny3wxi2wyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2ny3wxi2wyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF3LFB2FB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF3LFB2FB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYIS2LF3LFB4gapn1n3dLX2dY2dZ1i2nyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ1i2nyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3wxi2wyS2LF3LFB2dA4gapn1n3dLX2dY2dZ1i2ny3NY13INA2NZS2LF3LFB2dA4gapn1n3dLX2dY2dZ1i2ny3NY13INA2NZ3wxi2wyS2LF3LFB3sp14gapn1n3dLX2dY2dZ2ny2HB5Ha_stS2LF3LFB3sp14gapn1n3dLX2dY2dZ2ny2HB5Ha_stS2LF3LFB4gapn1n3dLX2dY2dZ2ny3NYL4NY1'S2LF3LFB4gapn1n3dLX2dY2dZ2ny3NYL4NY1'S2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13IXLS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP11n3dLX2dY2dZ1i2ny2HB5Ha_st5Hl_stS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3PZ03wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ1i2ny3NY13NYI3PZ0S2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2ny3NY1S2LF3LFB4gapn1n3dLX2dY2dZ2ny3NY1S2LF3LFB4gapn1n3dLX2dY2dZ2ny3NY1S2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2ny3wxi2wyS2LF2sp2lo3LFB3sp14gapn3SP11n3dLX2dY2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2ny3wxi2wyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2ny3wxi2wyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2nyS2LF2lo3LFB3sp14gapn3LOC1n3dLX2dY2dZ2nyS2LF3LFB4gapn1n3dLX2dY2dZ2ny3NY13PY0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 GAP F64 FRSH CFB ESF LOC CSP FN64"] Lemma dv_L1 : forall n, dvL2_stmt n -> dvLH_stmt (S n).
  Proof.
    intros n K2. unfold dvLH_stmt. intros until t6. intros CST LI RN HK UW BPOS NA98 HV HF. kit_pre CST mq hq. dv_chunks CHq.
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
    edestruct K_local_facts with (mq := mq) (i := 2%nat) (d := dZ) as (MLZ & NSZ & _ & _ & _ & _ & HFZ & _ & Z8 & _ & OZs); try eassumption; [reflexivity|].
    pose proof MLZ as [(CZ & _ & Z0 & LENZ & NRZ & OWZ) SGZ]. rewrite OZH in OWZ. ddestruct OWZ as (NZ1 & INZ & PZ16 & UAZ). rewrite EAZ in CZ. unfold mpi_cells in CZ.
    ddestruct (HFZ OZH) as (PZ0 & PZC & _ & _ & PZF & _).
    assert (OPZ : aobj asegs AL (hcs asegs R HIA hq) mq (md_p dZ) (4 * md_n dZ)) by (eapply hm_aobj_block; [exact HHq| exact INZ]).
    destruct (nth_error (md_limbs dLX) (Z.to_nat i)) as [wxi|] eqn:NTHXI; [| apply nth_error_None in NTHXI; exfalso; clear - NTHXI LENX IXL NY1 NYI; lia].
    destruct (nth_error (md_limbs dLX) (Z.to_nat (i - 1))) as [wxj|] eqn:NTHXJ; [| apply nth_error_None in NTHXJ; exfalso; clear - NTHXJ LENX IXL NY1 NYI; lia].
    destruct (nth_error (md_limbs dY) (Z.to_nat (ny - 1))) as [wy|] eqn:NTHY; [| apply nth_error_None in NTHY; exfalso; clear - NTHY LENY NYL NY1; lia].
    pose proof (munch_refl [(sp1 + 48, sp1 + 88)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    unfold dvL2_stmt, dvLg in K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    replace (md_p dLX + i * 4) with (md_p dLX + 4 * i) by (clear; lia).
    zstep.
    replace (Z.b2z (0 <? md_p dLX)) with 1 by (rewrite (proj2 (Z.ltb_lt 0 (md_p dLX)) PX0); reflexivity).
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    zstep. zstep.
    shadow_chk OPX (md_p dLX + 4 * i) 4.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    match goal with |- context [Z_to_bv 64 (md_p dY + ?e)] => replace (md_p dY + e) with (md_p dY + 4 * (ny - 1)) by (clear; lia) end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep.
    pose proof (u32arr_read asegs _ (md_p dLX) (md_limbs dLX) i wxi _ UAX NTHXI ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
    shadow_chk OPY (md_p dY + 4 * (ny - 1)) 4. clear RD.
    (* [comment removed for export] *)
    pose proof (u32arr_read asegs _ (md_p dY) (md_limbs dY) (ny - 1) wy _ UAY NTHY ltac:(clear - NY1; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. zstep. rewrite (idx_word i ny) by (clear - NY1 NYI INA NA98; lia).
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (CST2 : CSTA m2 hq LBq [dLX; dY; dZ; dT] dX (DCSOb c0 c8 c16 (Z_to_bv 64 i) (Z_to_bv 64 (i - ny)) c120 ny k t2pad czp czpad gb z32 z48 z64 u0 u1 u2 jq) DV_FSH v f).
    { eapply S_cs_store with (mq := mq) (a := sp1 + 48) (b := sp1 + 88); try eassumption.
      - clear; lia.
      - left. clear - SP1. lia.
      - intros d0 Hd. cbn [In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; rewrite ?EAX, ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR ACV; lia.
      - unfold A_mpi_div_mpi_C.DCS, A_mpi_div_mpi_C.dv_sp. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - eapply S_dcs_ok; [exact OKq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    assert (UW2 : UWCD m2) by (eapply S_uwcd_store; [exact UW| exact MU| clear; lia]).
    clear MU WM.
    zstep; if_cases KB.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (md_p dZ + ?e)] => replace (md_p dZ + e) with (md_p dZ + 4 * (i - ny)) by (rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; lia) end.
      zstep. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. zstep.
      zstep. zstep.
      shadow_chk OPZ (md_p dZ + 4 * (i - ny)) 4.
      zstep.
      eapply K2 with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV'| exact HF'].
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (md_p dLX + ?e)] => tryif constr_eq e (4 * i) then fail else replace (md_p dLX + e) with (md_p dLX + 4 * (i - 1)) by (rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; lia) end.
      zstep. zstep.
      zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. zstep.
      zstep. zstep.
      shadow_chk OPX (md_p dLX + 4 * (i - 1)) 4.
      pose proof (u32arr_read asegs _ (md_p dLX) (md_limbs dLX) (i - 1) wxj _ UAX NTHXJ ltac:(clear - NY1 NYI; lia) ltac:(f_equal; clear; lia)) as RD.
      zstep. clear RD.
      zstep. zstep. zstep. zstep. zstep.
      zstep.
      zstep; if_cases KC.
      + zstep. zstep. zstep. zstep.
        match goal with |- context [Z_to_bv 64 (md_p dZ + ?e)] => replace (md_p dZ + e) with (md_p dZ + 4 * (i - ny)) by (rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; lia) end.
        zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        shadow_byte OPZ (md_p dZ + 4 * (i - ny)) 4 as kz RDz HKz.
        zstep. clear RDz. zstep. if_cases KZ; zify_cond KZ.
        * eapply K2 with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV'| exact HF'].
        * zstep. zstep. zstep.
          lazymatch goal with |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with true by (symmetry; eapply (shadow_slow_takenN (md_p dZ + 4 * (i - ny)) _ kz _ HKz KZ); qlia) end.
          cbv_concl_iota.
          eapply K2 with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV'| exact HF'].
      + zstep. zstep. zstep. zstep. zstep.
        match goal with |- context [Z_to_bv 64 (md_p dZ + ?e)] => replace (md_p dZ + e) with (md_p dZ + 4 * (i - ny)) by (rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; lia) end.
        zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        shadow_byte OPZ (md_p dZ + 4 * (i - ny)) 4 as kz RDz HKz.
        zstep. clear RDz. zstep. if_cases KZ; zify_cond KZ.
        * eapply K2 with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV'| exact HF'].
        * zstep. zstep. zstep.
          lazymatch goal with |- _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
            replace cnd with true by (symmetry; eapply (shadow_slow_takenN (md_p dZ + 4 * (i - ny)) _ kz _ HKz KZ); qlia) end.
          cbv_concl_iota.
          eapply K2 with (i := i) (ny := ny) (k := k); [exact CST2| exact LI| clear - RN; lia| repeat split; reflexivity| exact HK| exact UW2| exact BPOS| exact NA98| exact HV'| exact HF'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59309008877.400000=S1i2ny3NYI2RN". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SHL LSETNG MULNG MULI CMPR ASM ASP slo SLO1 SLO2 SSH0 PF0 FF0 KFIN"] Lemma dv_LH : forall n, dvLH_stmt n.
  Proof.
    induction n as [|n IH].
    - unfold dvLH_stmt. intros until t6. intros CST LI RN. exfalso.
      ddestruct LI as (_ & _ & _ & _ & _ & _ & _ & _ & NY1 & NYI & _). clear - RN NYI. lia.
    - apply dv_L1, dv_L2, dv_L3a, dv_L3b. intros Q. apply dv_DW.
      apply dv_L4; [apply dv_L5; exact IH| apply dv_L4c, dv_L5; exact IH].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L14808106792.1 L31813111044.6 L33324003609.10L54583660252.10L56496830848.10L56545230362.10L58192282731.6 L59757927748.1000000400J00K00V00`00l01>01IS2nxS2dA2nx2ny3NY13NYX3NXAFS2nx2ny3NYXS2dA2dT2NTS3dLX2nx3NXLS2dA2nx2ny3NY13NXAS2dA2nx3NXA". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF C24H COPYX SHL LSETNG MULNG MULI CMPR ASM ASP slo SLO1 SLO2 SSH0 PF0 FF0 KFIN"] Lemma dv_LOOP_ok : A_mpi_div_mpi_M_c24.dvLOOP_stmt R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo dX dA dB d es PHIb FRb FB sp1 w0 w1 w2 gapn
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
