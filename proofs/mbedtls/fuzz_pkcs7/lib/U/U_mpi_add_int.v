(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_add_abs_W U_mpi_add_abs U_mpi_sub_abs U_mpi_add_sub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_add_int () : Init.string Init.list := ["stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lxor"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.lor"; "sgn_of"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "Corelib.Init.Logic.or"; "U_MPI_ADD_INT"; "U_MPI_SUB_INT"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_intop_stmt"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"].


Definition U_MPI_ADD_INT : Z := 0x1fd60.
Definition U_MPI_SUB_INT : Z := 0x20b0c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31). reflexivity. Qed.

Lemma shiftr_neg_small : forall b k, 0 < k -> - 2 ^ k <= b < 0 -> Z.shiftr b k = -1.
Proof.
  intros b k Hk Hb. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod b (2^k) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^k) ltac:(lia)).
  assert (b / 2 ^ k < 0) by (apply Z.div_lt_upper_bound; lia). nia.
Qed.

Definition abs_limb_expr (b : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_int ()) "(0.&20.(1.(2.(3.O1.+10000000000000000.)(3.(0.&20.(4.(0.&20.(3.O1.+10000000000000000.))+1?.))+10000000000000000.))(3.(0.&20.(4.(0.&20.(3.O1.+10000000000000000.))+1?.))+10000000000000000.)))")
(* [comment removed for export] *).

Lemma abs_limb_val : forall b, - 2 ^ 31 <= b < 2 ^ 31 -> w32 (Z_to_bv 64 (abs_limb_expr b)) = Z.abs b.
Proof.
  intros b Hb. unfold w32, abs_limb_expr. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). change 18446744073709551616 with (2^64).
  rewrite swrap32_mod64, sxz_mod32 by (apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec b 0) as [NEG|POS].
  - assert (E1 : b mod 2^64 = 2^64 + b) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
    rewrite E1. assert (E2 : bv_swrap 32 (2^64 + b) = b).
    { rewrite swrap32_eq. replace (2^64 + b + 2^31) with ((b + 2^31) + 2^32 * 2^32) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia. }
    rewrite E2. rewrite (shiftr_neg_small b 31) by lia.
    assert (E3 : bv_swrap 32 (-1) = -1) by reflexivity. rewrite E3.
    assert (E4 : (-1) mod 2^64 = 2^64 - 1) by reflexivity. rewrite E4.
    change (2^64 - 1) with 18446744073709551615. rewrite lxor_allones64 by lia.
    replace (18446744073709551615 - (2 ^ 64 + b) - 18446744073709551615) with (- b + (- 2^32) * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
  - rewrite (Z.mod_small b) by lia.
    assert (E2 : bv_swrap 32 b = b) by (rewrite swrap32_eq; rewrite Z.mod_small; lia). rewrite E2.
    rewrite Z.shiftr_div_pow2, Z.div_small by lia. change (bv_swrap 32 0 mod 2^64) with 0.
    rewrite Z.lxor_0_r, Z.sub_0_r, Z.abs_eq by lia. apply Z.mod_small. lia.
Qed.

Definition sgn_of (b : Z) : Z := if b <? 0 then -1 else 1.

Lemma sign_half_val : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_int ()) "Pb,$5.P,(6.(7.(8.(9.+2.+1?.))R1.)(:.R1.(9.+2.+1?.)))(;.$5.(3.(<.(4.(3.R2.+10000000000000000.)+1>.)+1.)(9.+2.+10.))(3.(=.R2.)(9.+2.+10.)))")
(* [comment removed for export] *).
Proof.
  intros b Hb. unfold sgn_of. change 18446744073709551616 with (2^64).
  destruct (Z.ltb_spec b 0) as [NEG|POS].
  - assert (E1 : b mod 2^64 = 2^64 + b) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia). rewrite E1.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (K : (2^64 + b) / 2^30 = 2^34 - 1 \/ (2^64 + b) / 2^30 = 2^34 - 2).
    { pose proof (Z.div_mod (2^64 + b) (2^30) ltac:(lia)). pose proof (Z.mod_pos_bound (2^64 + b) (2^30) ltac:(lia)).
      assert ((2^64 + b) / 2^30 < 2^34) by (apply Z.div_lt_upper_bound; lia).
      assert (2^34 - 2 <= (2^64 + b) / 2^30) by (apply Z.div_le_lower_bound; lia). lia. }
    destruct K as [-> | ->]; reflexivity.
  - rewrite (Z.mod_small b) by lia. rewrite Z.shiftr_div_pow2 by lia.
    assert (K : b / 2^30 = 0 \/ b / 2^30 = 1).
    { assert (0 <= b / 2^30) by (apply Z.div_pos; lia). assert (b / 2^30 < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    destruct K as [-> | ->]; reflexivity.
Qed.

Lemma sgn_of_abs : forall b, sgn_of b * Z.abs b = b.
Proof. intros b. unfold sgn_of. destruct (Z.ltb_spec b 0); lia. Qed.

Lemma sgn_of_cases : forall b, sgn_of b = 1 \/ sgn_of b = -1.
Proof. intros b. unfold sgn_of. destruct (b <? 0); [right| left]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma cells_CB4_C4 : forall segs m A bs, rw_cells segs m A [CB 4 bs] -> rw_cells segs m A [C4 (le_bytes_to_word bs)].
Proof.
  intros segs m A bs H. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [H2 _].
  eapply rw_cells_reshape; [exact H| cbn; split; exact I|]. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact H2. reflexivity.
Qed.

Lemma rw_cells_join2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_int ()) "Psegs,(>.$?.)Pm,P,(10.&40.)(11.(10.&8.))PA,$5.Pcs1,(>.$12.)Pcs2,(>.$12.)P,(13.R5.R4.R3.R2.)P,(13.R6.R5.(14.R4.(15.(16.R3.)))R2.)(13.R7.R6.R5.(17.$12.R4.R3.))")
(* [comment removed for export] *).
Proof. intros segs m A cs1 cs2 H1 H2. apply rw_cells_app. split; assumption. Qed.

(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Lemma U_mpi_intop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_int ()) "PMSF,$5.PENTRY,$5.PFLIP,$5.P,(;.$5.R3.$18.)P,(19.(6.(;.$5.R3.$1:.)(;.$5.R2.+1.))(6.(;.$5.R3.$1;.)(;.$5.R2.-1.)))(1<.$1=.VL,VHI,R4.R5.LLB,(>.$1>.)LdX,$1?.LdA,$1?.Lb,$5.Lr,$5.LdX',$1?.(6.(19.(6.(;.$5.R2.=)(;.$5.(20.R1.)(14.(20.R4.)(21.R9.R3.))))(;.$5.R2.$22.))(23.R6.R5.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros MSF ENTRY FLIP MSFE EF. unfold mpi_intop_stmt. intros until lo.
    intros HH MX MA SXA NST OA CRA CRAL XW BB XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX as [(CX0 & XAL & X0 & LENX & NRX & OWNX) SGX]. pose proof MA as [(CA0 & AAL & A0 & LENA & NRA & OWNA) SGA].
    dpose XW as (XCW & XDW & XP). dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO HLS; lia)) as XS.
    (* [comment removed for export] *)
    assert (XHL : ownX = LHeap -> pX + 4 * nX <= alloc_ceiling).
    { intros EO. rewrite EO in OWNX. ddestruct OWNX as (_ & XIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ XIN) as (_ & _ & _ & R3 & _). exact R3. }
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HHc. pose proof (conj SOK I) as SOKc. pose proof (conj MX I) as MXc. pose proof (conj MA I) as MAc. clear HH SOK MX MA CX0 CA0.
    destruct EF as [[-> ->]|[-> ->]]; unfold U_MPI_ADD_INT, U_MPI_SUB_INT.
    all: do 15 zstep.
    all: replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in * by (clear; lia).
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    all: destruct HHc as [HH _]; destruct SOKc as [SOK _]; destruct MXc as [MX _]; destruct MAc as [MA _].
    all: fold (abs_limb_expr b) in FR.
    (* [comment removed for export] *)
    all: lazymatch type of FR with rw_cells _ _ _ [CB 4 ?j1; C4 ?vw; C8 ?pp; C2 ?sw; C2 ?one; CB 4 ?j2; C8 ?rr] =>
           pose proof (rw_cells_C2_congr usegs m1 (bv_unsigned sp - 32) [CB 4 j1; C4 vw; C8 pp] _ (sgn_of b) [C2 one; CB 4 j2; C8 rr] FR (sign_half_val b BB)) as FR';
           cbn [app] in FR'; clear FR; set (jA := j1) in FR'; set (jB := j2) in FR' end.
    all: replace (Z_to_bv 64 (bv_unsigned sp + -28)) with (Z_to_bv 64 (bv_unsigned sp - 28)) in FR' |- * by (f_equal; clear; lia).
    all: replace (Z_to_bv 64 (bv_unsigned sp + -24)) with (Z_to_bv 64 (bv_unsigned sp - 24)) by (f_equal; clear; lia).
    (* [comment removed for export] *)
    all: destruct (rw_cells_split3 usegs m1 (bv_unsigned sp - 32) [CB 4 jA] [C4 (Z_to_bv 64 (abs_limb_expr b))] _ FR') as (_ & CL & CS0).
    all: cbn [cells_size csize Nat.add] in CL, CS0.
    all: destruct (rw_cells_split3 usegs m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp - 28)); C2 (Z_to_bv 64 (sgn_of b)); C2 (Z_to_bv 64 1)] [CB 4 jB] [C8 ra] CS0) as (CS1 & CJ & _).
    all: cbn [cells_size csize Nat.add] in CS1, CJ.
    all: pose proof (cells_CB4_C4 usegs m1 _ jB CJ) as CJ'.
    all: pose proof (rw_cells_join2 usegs m1 _ _ _ CS1 CJ') as CS; cbn [cells_size csize Nat.add app] in CS; clear CS1 CJ CJ' CS0.
    all: replace (bv_unsigned sp - 32 + Z.of_nat 4 + Z.of_nat 4) with (bv_unsigned sp - 24) in CS by (clear; lia).
    all: replace (bv_unsigned sp - 32 + Z.of_nat 4) with (bv_unsigned sp - 28) in CL by (clear; lia).
    all: assert (BL : u32arr usegs m1 (bv_unsigned sp - 28) [Z_to_bv 64 (abs_limb_expr b)])
           by (eapply (u32arr_of_cells _ _ _ 4 (le4 (Z_to_bv 64 (abs_limb_expr b)))); [eapply rw_cells_reshape; [exact CL| cbn; split; [apply (length_le4 (Z_to_bv 64 (abs_limb_expr b)))| exact I]| cbn; rewrite ?app_nil_r; reflexivity]| cbn; rewrite ?app_nil_r; reflexivity]).
    all: set (dB := mkMPD (bv_unsigned sp - 24) (sgn_of b) 1 (bv_unsigned sp - 28) [Z_to_bv 64 (abs_limb_expr b)] (le_bytes_to_word jB) LStatic).
    all: assert (OB : opnd_at usegs m1 LB (bv_unsigned sp - 32) dB).
    1,3: right; unfold stack_opnd, dB; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own length];
      (split; [reflexivity|]); (split; [unfold mpi_cells; exact CS|]); (split; [clear - SPA; Z.div_mod_to_equations; lia|]);
      (split; [clear - SPB SLO HLS ACL ACP; lia|]); (split; [reflexivity|]); (split; [unfold MPI_MAX_LIMBS; clear; lia|]); (split; [clear; lia|]);
      (split; [clear - SPA; Z.div_mod_to_equations; lia|]); (split; [clear - SPB SLO HLS ACL ACP; lia|]); (split; [apply u32arr_ro; exact BL|]);
      (split; [clear; lia|]); split; [clear - SPB; lia| apply sgn_of_cases].
    (* [comment removed for export] *)
    all: assert (HH1 : HEAP usegs L HI h LB m1 mo) by
          (eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|]; intros a Ha NO; cbn in NO; left; clear - NO HTOP SLO HLS; lia).
    all: assert (SOK1 : statics_ok usegs L m1) by (eapply statics_ok_munch; [exact SOK| exact MU|]; intros a Hd NW; cbn; split; [clear - Hd DHI ACL SLO HLS; lia| exact I]).
    all: assert (MX1 : mpd_at usegs m1 LB (mkMPD X sX nX pX xs0 padX ownX)) by
      (eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn; split; [clear - XS SLO HLS; lia| exact I]|];
       cbn [md_own md_p md_n]; intros ON; cbn; split; [| exact I]; destruct (XLS ON); clear - H SLO HLS; lia).
    all: assert (MA1 : mpd_at usegs m1 LB (mkMPD Aa sA nA pA ys padA ownA)) by
      (eapply mpd_at_munch_any; [exact MA| exact MU| exact WM| cbn; split; [clear - OA4 SLO HLS; lia| exact I]|];
       cbn [md_own md_p md_n]; intros ON; cbn; split; [| exact I]; destruct (OA5 ON); clear - H SLO HLS; lia).
    (* [comment removed for export] *)
    all: zstep.
    all: eapply aevtM_cut.
    1,3: eapply (U_add_sub_mpi_spec_o L HI HFREE HCALLOC HLS SW DIMG HND ROIMG MSF MSFE) with
           (dX := mkMPD X sX nX pX xs0 padX ownX) (dA := mkMPD Aa sA nA pA ys padA ownA) (dB := dB) (lo := lo) (h := h) (LB := LB);
         unfold dB; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
         rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; try eassumption.
    all: try (left; reflexivity). all: try (right; reflexivity).
    all: try exact OB.
    all: try (right; cbn [md_addr]; clear - XS SLO HLS; lia).                                   (* [comment removed for export] *)
    all: try (right; cbn [md_addr]; clear - OA4 SLO HLS; lia).                                  (* [comment removed for export] *)
    all: try (intros C; discriminate C).
    all: try (unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
              split; [exact OA1|]; split; [exact OA2|]; split; [exact OA3|]; split; [clear - OA4; lia| intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]]).
    all: try (unfold opnd_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
              split; [intros _; clear - XS SLO HLS; lia|];
              split; [intros EO; pose proof (XHL EO); right; clear - H ACL SLO HLS; lia|];
              split; [destruct ownX; [right; left; discriminate| right; right; right; left; pose proof (XHL eq_refl); clear - H ACL SLO HLS; lia| right; left; discriminate]|];
              split; [right; clear; lia| intros _; right; clear; lia]).
    all: try (intros a Ha; left; clear - Ha SLO HLS; lia).                                     (* [comment removed for export] *)
    all: try (split; [| split; [exact XDW| exact XP]]; intros a Ha; destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C]).
    all: try (intros XN; destruct (XLS XN); [left; assumption| right; clear - H; lia]).
    all: try (clear - SLO; lia). all: try (clear - SPA; Z.div_mod_to_equations; lia). all: try (clear - HTOP; lia).
    all: cbv beta; intros ms' mo' PO; unfold mpi_binop_post in PO.
    all: ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo1 & h1 & LB1 & dX1 & r & E & PO); injection E as -> ->.
    all: rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    all: ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MX2 & OUT2 & HPX2 & SOK2 & [VAL BK]).
    all: try replace (ret_pc (Z_to_bv 64 130464)) with (Z_to_bv 64 130464) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    all: try replace (ret_pc (Z_to_bv 64 133964)) with (Z_to_bv 64 133964) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    all: assert (FR2 := heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 FR' ltac:(cbn [cells_size csize Nat.add]; apply client_range_stack; clear; lia)
                    ltac:(unfold mpd_ivs; cbn [md_addr md_own md_p md_n]; destruct ownX; cbn; (split; [clear - XS SLO HLS; lia|]); [exact I| split; [pose proof (XHL eq_refl); clear - H ACL SLO HLS; lia| exact I]| exfalso; exact (NST eq_refl)])).
    all: pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    all: pose proof (munch_refl ([] : list ivl) m') as MU'; pose proof (wmono_refl usegs m') as WM'.
    all: zstep; zstep.
    all: replace (Z_to_bv 64 (bv_unsigned sp - 32 + 32)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia); rewrite Z_to_bv_bv_unsigned.
    all: zstep.
    all: apply aevtM_done; unfold mpi_binop_post; deexists 14; dexists m', mo1, h1, LB1, dX1, r.
    all: split; [reflexivity|]. all: split; [exact MI2|].
    all: split; [eapply stk_release in FR2; [| exact ST2| clear - SLO HLS ACL ACP; lia];
                 cbn [cells_size csize Nat.add] in FR2; replace (bv_unsigned sp - 32 + Z.of_nat 32) with (bv_unsigned sp) in FR2 by (clear; lia); exact FR2|].
    all: split; [exact MF2|]. all: split; [exact HT2|]. all: split; [exact HH2|]. all: split; [exact MX2|]. all: split; [exact OUT2|].
    all: split; [eapply heap_presx_trans; [eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| clear - ACL SLO HLS; lia]|
                  eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho]]|].
    all: split; [exact SOK2|]. all: split; [| exact BK].
    all: destruct VAL as [[-> V]|V]; [left| right; exact V]. all: split; [reflexivity|].
    all: rewrite V; unfold dB, mpd_val at 2; cbn [md_sg md_limbs limbs_val].
    all: change (bv_unsigned (Z_to_bv 64 (abs_limb_expr b)) mod 2 ^ 32) with (w32 (Z_to_bv 64 (abs_limb_expr b))); rewrite (abs_limb_val b BB).
    all: pose proof (sgn_of_abs b); clear - H; lia.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_add_int_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_add_int_stmt usegs L HI U_MPI_ADD_INT MSF.
  Proof.
    intros MSF E. unfold mpi_add_int_stmt. pose proof (U_mpi_intop_walk MSF U_MPI_ADD_INT 1 E ltac:(left; split; reflexivity)) as W.
    unfold mpi_intop_stmt in W |- *. intros until lo. intros. eapply aevtM_mono; [eapply W with (dX := dX) (dA := dA) (b := b) (lo := lo) (h := h) (LB := LB); eassumption|].
    cbv beta. intros c PO. unfold mpi_binop_post, add_int_R in PO |- *.
    ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & E' & PO).
    deexists 14. dexists m', mo', h', LB', dX', r. split; [exact E'|].
    ddestruct PO as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & [V K]).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [| exact K].
    destruct V as [[-> V]|V]; [left; split; [reflexivity| rewrite V; lia]| right; exact V].
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem U_mpi_sub_int_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_sub_int_stmt usegs L HI U_MPI_SUB_INT MSF.
  Proof.
    intros MSF E. unfold mpi_sub_int_stmt. pose proof (U_mpi_intop_walk MSF U_MPI_SUB_INT (-1) E ltac:(right; split; reflexivity)) as W.
    unfold mpi_intop_stmt in W |- *. intros until lo. intros. eapply aevtM_mono; [eapply W with (dX := dX) (dA := dA) (b := b) (lo := lo) (h := h) (LB := LB); eassumption|].
    cbv beta. intros c PO. unfold mpi_binop_post, sub_int_R in PO |- *.
    ddestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & mo' & h' & LB' & dX' & r & E' & PO).
    deexists 14. dexists m', mo', h', LB', dX', r. split; [exact E'|].
    ddestruct PO as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & [V K]).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [| exact K].
    destruct V as [[-> V]|V]; [left; split; [reflexivity| rewrite V; lia]| right; exact V].
  Qed.
End Spec.
