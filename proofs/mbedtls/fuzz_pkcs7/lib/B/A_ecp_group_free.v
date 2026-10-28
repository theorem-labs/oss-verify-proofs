(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_ecp_group_free.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_platform_zeroize A_free_seq.
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
Definition A_ECP_GROUP_FREE : Z := 0xcb08c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation ECP_GROUP_FREE_STACK_A := 144 (only parsing).
Definition GF_PHI : Z := 7 * AVOL_CALL.
Definition GF_FR (d : Z) : Z := 7 * fr_charge d.

Definition ecp_group_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (g : ecp_grp) (lo d : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' mo' h',
    c = mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom segs)) mo'
    /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
    /\ presA segs R (grp_free_LB g LB) LF (bv_unsigned sp) (arl_stklo R) (hstkhi segs R HIA h) [(A, A + ECP_GROUP_SIZE)] m m'
    /\ htop segs R HIA h' = htop segs R HIA h /\ hstkhi segs R HIA h' = hstkhi segs R HIA h
    /\ hflag segs R HIA h' = hflag segs R HIA h /\ HK segs R HIA h' mo'
    /\ (forall x, hcs segs R HIA h x -> hcs segs R HIA h' x)
    /\ havol segs R HIA h' <= havol segs R HIA h + GF_PHI
    /\ hfr segs R HIA h' <= hfr segs R HIA h + GF_FR d
    /\ HM segs R HIA h' (grp_free_LB g LB) LF m'
    /\ ecp_group_at segs MT m' (grp_free_LB g LB) A (grp_zero A)
    /\ rw_cells segs m' A [CB 192 (repeat (Z_to_bv 8 0) 192)].

Definition ecp_group_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
         (A : Z) (g : ecp_grp) (lo d : Z),
    HM segs R HIA h LB LF m -> HK segs R HIA h mo ->
    ecp_group_at segs MT m LB A g -> mpds_apart (grp_mpds g) ->
    (* [comment removed for export] *)
    client_wrange (arl_L R) (grp_free_LB g LB ++ fdata LF) (bv_unsigned sp) (htop segs R HIA h) A ECP_GROUP_SIZE ->
    (A + ECP_GROUP_SIZE <= lo \/ bv_unsigned sp <= A) ->
    aobj segs (arl_AL R) (hcs segs R HIA h) m A ECP_GROUP_SIZE ->
    stk segs m lo (bv_unsigned sp) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - ECP_GROUP_FREE_STACK_A - arl_need_rt R ->
    bv_unsigned sp <= htop segs R HIA h -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) -> mem_inv segs m ->
    havol segs R HIA h + GF_PHI <= AVOL_MAX -> uw_obj R A ECP_GROUP_SIZE d -> hfr segs R HIA h + GF_FR d <= FR_MAX ->
    a0 = Z_to_bv 64 A ->
    aevtS segs (ecp_group_free_postA segs R HIA MT h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A g lo d m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo).

Section GF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MPIFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2600875857.10000009S1R5NEEDA". (* [comment removed for export] *)
  Let NRT : arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation FRAME s8 s7 s6 s5 s4 s3 s2 s1 s0 ra := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation POST h0 LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A g lo d m0 mo0 :=
    (ecp_group_free_postA asegs R HIA MT h0 LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A g lo d m0 mo0).

  Ltac gf_facts h0 :=
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := L)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    pose proof (hcs_ok asegs R HIA h0) as CSOK; pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00k0@C17025492443.126C31740276271.127D16049893661.127D37703787028.127D4425054262.127 D50796826103.127D60109446735.127D64311484648.127K43408488049.126K61093937827.126L15302269400.107L22446743512.107L24385257333.107L34423640368.6  L34705680216.107L35560117447.106L35653441506.10 L38180633941.0  L3949578456.107 L40378383505.107L41843875160.107L43412612116.3  L50790580594.7  L51454941784.107L52509853291.5  L5699067096.107 L58591023192.107L59506921496.106L60098763854.3  L61097676998.2  L67280348888.107L7348528798.1   O17025492443.126O49587672251.126P61093937827.126Q15647400598.107Q15766564435.127Q18361844886.107Q21892344565.107Q27597641366.107Q27911281013.107Q30402604533.107Q31259086870.107Q32659548566.107Q33913950197.107Q36438315125.107Q36856420847.127Q37703787028.127Q3834504053.107 Q39935505013.107Q41139692438.107Q4425054262.127 Q44652889622.107Q48217684537.127Q50840533351.127Q51223362326.107Q59830672662.107Q66534538485.107Q9839284725.107 00000100400500;00A00`00o01U01a01b01h01n02I02Z02`02f03K03L03R03X03^03_04404:04M04S04Y04_04i04j05005105205305405;05I05P05a05h06906J06Q06X06i07:07;07>07O07`07g07j08108408;08B08I08Z08kFS1AFS2sp1AS2sp1AS1R3NRT2sp1A2lo3POS3LOS3SLO3SPRS1R2sp1A2lo3LOSS1R3HIA2sp2h01h1A2lo3HTc3POS5SPTOP3SPRS2sp1A2lo2SXFS2sp1AS2sp1AS1R3NRT2sp1A2lo3POS3SLO3SPRS1R3NRT2sp2lo3SLOS2sp1AS2sp1AS1R3HIA2sp2h01h2lo3HTc5SPTOP4HTOP3HScSS2sp1AS2sp1AS2sp1AFS1R3NRT2sp2lo3LOS3SLOS2sp1AS1R3HIA2sp2h05SPTOPS2sp1AS2sp1AS2sp1AS1R2lo3LOSFS2sp1AFFFFS2sp2loS1R2lo3LOS3ALOS2sp2loS1R3NRT2sp2lo3SLOS2sp2loS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS2sp2loS2sp2loS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOFS1AS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS2sp2loS1AS2sp2loS1AS2sp2loS2sp2loS2sp2loS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG PZ NEEDA NRT"] Lemma zero_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (mo0 : Model) (h0 h : HST asegs R HIA)
      (LB LF : list blk) (A : Z) (g : ecp_grp) (lo d : Z) (hc c1 c2 c3 c4 c5 c6 c7 tc : list cell) (xra x1 x2 x3 x4 x5 : word),
    let LBf := grp_free_LB g LB in
    HM asegs R HIA h LBf LF m -> htop asegs R HIA h = htop asegs R HIA h0 -> hstkhi asegs R HIA h = hstkhi asegs R HIA h0 -> hflag asegs R HIA h = hflag asegs R HIA h0 ->
    (forall x, hcs asegs R HIA h0 x -> hcs asegs R HIA h x) ->
    havol asegs R HIA h <= havol asegs R HIA h0 + GF_PHI -> hfr asegs R HIA h <= hfr asegs R HIA h0 + GF_FR d ->
    presW asegs R HIA h0 LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m0 m ->
    rw_cells asegs m A hc -> cells_size hc = 8%nat ->
    rw_cells asegs m (A + 8) c1 -> cells_size c1 = 16%nat -> rw_cells asegs m (A + 24) c2 -> cells_size c2 = 16%nat ->
    rw_cells asegs m (A + 40) c3 -> cells_size c3 = 16%nat -> rw_cells asegs m (A + 56) c4 -> cells_size c4 = 16%nat ->
    rw_cells asegs m (A + 72) c5 -> cells_size c5 = 16%nat -> rw_cells asegs m (A + 88) c6 -> cells_size c6 = 16%nat ->
    rw_cells asegs m (A + 104) c7 -> cells_size c7 = 16%nat -> rw_cells asegs m (A + 120) tc -> cells_size tc = 72%nat ->
    A mod 8 = 0 -> 0 < A -> A + 192 <= 2^64 ->
    rw_cells asegs m (bv_unsigned sp - 80) (FRAME s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h0) A 192 ->
    (A + 192 <= lo \/ bv_unsigned sp <= A) -> aobj asegs AL (hcs asegs R HIA h0) m A 192 ->
    stk asegs m lo (bv_unsigned sp - 80) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - 144 - arl_need_rt R ->
    bv_unsigned sp <= htop asegs R HIA h0 -> bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 (arl_tp R) -> mem_inv asegs m ->
    aevtA asegs (KF asegs R HIA h mo0) (POST h0 LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A g lo d m0 mo0)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 A) x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcb228) fc None m (seg_rom asegs)).
  Proof.
    intros until x5. cbv zeta. intros HH HTc HSc HFc HCSc HV HFR PXA H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT LT AL8 POS AB FR CW SX OBJ ST LOS SLO SPTOP SPA TP MI.
    gf_facts h0. pose proof (hcs_ok asegs R HIA h) as CSOKc.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h _ LF m HH) as HTOP.
    assert (SCSc : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP HTc HSc; lia]).
    assert (SCS : crange (hcs asegs R HIA h0) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h0)| clear - LOS; lia| clear - SPTOP HTOP HTc HSc; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (grp_join _ _ _ _ _ _ _ _ _ _ _ _ H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT LT) as J.
    clear H0 H1 H2 H3 H4 H5 H6 H7 HT L0 L1 L2 L3 L4 L5 L6 L7 LT.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJ) as OBJc.
    replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in FR, ST |- * by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    try (replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ. specialize SPZ with (h := h). rewrite HTc in SPZ.
    change 192%nat with (Z.to_nat 192) in J at 1.
    acallxA_sp (bv_unsigned sp)
      (eapply SPZ with (LB := grp_free_LB g LB) (LF := LF) (A := A) (n := 192) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp)) by (clear - SPR; lia);
       first [ exact HH | exact J | exact POS | exact LOS | exact OBJc | reflexivity
             | lazymatch goal with
               | |- 0 <= 192 => clear; lia
               | |- 192 < _ => clear; lia
               | |- stk _ _ lo _ => assumption
               | |- lo <= _ => clear - SLO NEEDR NRT; lia
               | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
               | |- _ mod 16 = 0 => exact SPA
               | |- A + 192 <= lo \/ _ => exact SX
               | |- mem_inv _ _ => assumption
               | |- tp = _ => exact TP
               | |- client_wrange _ _ _ _ A 192 => eapply client_wrange_sp_mono; [| exact CW]; clear - LOS SLO NEEDR NRT; lia
               end
             | match goal with |- ?gg => idtac "PZ-LEFT:" gg end ]).
    clear SPZ.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold ecp_group_free_postA.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => deexists 15; dexists mx, mo9, h end.
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [exact MF9|].
    split; [lazymatch goal with HP : presW _ _ _ _ _ _ _ _ _ m0 _ |- _ => exact (presW_presA asegs R HIA h0 _ LF _ _ _ _ _ HP) end|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [exact HV|]. split; [exact HFR|]. split; [assumption|].
    lazymatch goal with HZ : rw_cells _ _ A [CB (Z.to_nat 192) _] |- _ =>
      change (Z.to_nat 192) with 192%nat in HZ; split; [apply ecp_group_at_zero; [exact HZ| exact AL8| exact POS]| exact HZ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L12882018115.124L24893220336.126L28331135516.126L3514724698.125 L35653441506.10 L40372073437.125L52517407388.125L60098763854.3  Q14337030671.127Q3664927755.127 Q3665042443.126 Q37742105017.125Q46775875181.126Q52271986575.126Q57568794130.126Q58902301677.127Q63198795296.126Q66355101074.125Q66357350283.126Q67567023755.12500000m01c02Y03V04704m05c05m06`07S08F0990:;0:n0;a0<c0=V0>I0?<0?oS2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L73POS2ABS2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L73POS2ABS1R3HIA2sp2h01h2lo3HTc5SPTOP4HTOPS2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1R2lo3LOSS1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L73AL83POS3SPRS1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L73AL83POS3SPRS1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7". (* [comment removed for export] *)
  #[using="IMG PZ NEEDA NRT"] Lemma tail_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (mo0 : Model) (h0 h : HST asegs R HIA)
      (LB LF : list blk) (A : Z) (g : ecp_grp) (lo d : Z) (hc c1 c2 c3 c4 c5 c6 c7 : list cell) (xra x1 x2 x3 x4 : word),
    let LBf := grp_free_LB g LB in
    HM asegs R HIA h LBf LF m -> htop asegs R HIA h = htop asegs R HIA h0 -> hstkhi asegs R HIA h = hstkhi asegs R HIA h0 -> hflag asegs R HIA h = hflag asegs R HIA h0 ->
    (forall x, hcs asegs R HIA h0 x -> hcs asegs R HIA h x) ->
    havol asegs R HIA h <= havol asegs R HIA h0 + GF_PHI -> hfr asegs R HIA h <= hfr asegs R HIA h0 + GF_FR d ->
    presW asegs R HIA h0 LBf LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m0 m ->
    rw_cells asegs m A hc -> cells_size hc = 8%nat ->
    rw_cells asegs m (A + 8) c1 -> cells_size c1 = 16%nat -> rw_cells asegs m (A + 24) c2 -> cells_size c2 = 16%nat ->
    rw_cells asegs m (A + 40) c3 -> cells_size c3 = 16%nat -> rw_cells asegs m (A + 56) c4 -> cells_size c4 = 16%nat ->
    rw_cells asegs m (A + 72) c5 -> cells_size c5 = 16%nat -> rw_cells asegs m (A + 88) c6 -> cells_size c6 = 16%nat ->
    rw_cells asegs m (A + 104) c7 -> cells_size c7 = 16%nat ->
    rw_cells asegs m (A + 120) (grp_tail_cells g) -> g_Tsize g = 0 -> 0 <= g_T g < 2^64 ->
    A mod 8 = 0 -> 0 < A -> A + 192 <= 2^64 ->
    rw_cells asegs m (bv_unsigned sp - 80) (FRAME s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h0) A 192 ->
    (A + 192 <= lo \/ bv_unsigned sp <= A) -> aobj asegs AL (hcs asegs R HIA h0) m A 192 ->
    stk asegs m lo (bv_unsigned sp - 80) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - 144 - arl_need_rt R ->
    bv_unsigned sp <= htop asegs R HIA h0 -> bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 (arl_tp R) -> mem_inv asegs m ->
    aevtA asegs (KF asegs R HIA h mo0) (POST h0 LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A g lo d m0 mo0)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 A) x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 (al_sb AL)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xcb140) fc None m (seg_rom asegs)).
  Proof.
    intros until x4. cbv zeta. intros HH HTc HSc HFc HCSc HV HFR PXA H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT TS TB AL8 POS AB FR CW SX OBJ ST LOS SLO SPTOP SPA TP MI.
    gf_facts h0. pose proof (hcs_ok asegs R HIA h) as CSOKc. pose proof (cs_ok_sb _ _ CSOKc) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h _ LF m HH) as HTOP.
    assert (SCSc : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP HTc HSc; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJ) as OBJc.
    pose proof HT as HT'. unfold grp_tail_cells in HT. rewrite TS in HT.
    replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in FR, ST |- * by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0.
    all: cycle 1.
    (* [comment removed for export] *)
    1: zstep; zstep; zstep; zstep; zstep; zstep; zstep; try (if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by (clear; lia); clear - K1; lia]).
    all: replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in * by lia.
    all: eapply zero_walk; try eassumption; try reflexivity.
    all: match goal with |- ?gg => idtac "TAIL-LEFT:" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac to_tailA sp EQF :=
    replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in * by lia;
    lazymatch type of EQF with _ = ?rhs =>
      lazymatch goal with HH : HM _ _ _ _ ?l _ _ |- _ => try (change l with rhs in HH; rewrite <- EQF in HH) end;
      lazymatch goal with PXA : presW _ _ _ _ ?l _ _ _ _ _ _ |- _ => try (change l with rhs in PXA; rewrite <- EQF in PXA) end;
      lazymatch goal with CW : client_wrange _ (?l ++ _) _ _ _ 192 |- _ => try (change l with rhs in CW; rewrite <- EQF in CW) end
    end;
    eapply tail_walk; first [eassumption | reflexivity | unfold GF_PHI, GF_FR, AVOL_CALL, fr_charge in *; lia | match goal with |- ?gg => idtac "TAILSIDE" gg end].

  Ltac fsA_in ::= cbn; inl.
  Ltac fsA_addr ::= cbn [md_addr];
    match goal with EP : md_addr (g_P ?g) = _, EA : md_addr (g_A ?g) = _, EB : md_addr (g_B ?g) = _, EN : md_addr (g_N ?g) = _,
                     EX : md_addr (pt_X (g_G ?g)) = _, EY : md_addr (pt_Y (g_G ?g)) = _, EZ : md_addr (pt_Z (g_G ?g)) = _ |- _ =>
      rewrite ?EP, ?EA, ?EB, ?EN, ?EX, ?EY, ?EZ | _ => idtac end.

  (* [comment removed for export] *)
  Ltac gfA_free1 spo md X FRl rest :=
    lazymatch goal with
    | HH : HM _ _ _ ?xhc ?xLBc _ ?xmc, PXA : presW _ _ _ ?xh0 ?xLBf _ ?xSP _ [(?xA, _)] ?xm0 _, UWO : uw_obj _ _ 192 ?xd, ST : stk _ _ ?xlo _, HBR : blkfacts _ (?xLB ++ _) |- _ =>
        eapply (free_stepA R HIA A_MPI_FREE MPIFREE NEEDR DIMG) with
          (d0 := md) (X0 := X) (A := xA) (sz := 192) (d := xd) (SP := xSP) (h0 := xh0) (m0 := xm0) (LBf := xLBf) (lo := xlo) (LBall := xLB) (FR := FRl);
        [ fsA_side spo rest .. | ]
    end;
    lazymatch goal with
    | |- forall _, _ =>
        lazymatch goal with HH : HM _ _ _ _ _ _ _, LIV : Forall (mpdr_at _ _ _) _, CH : Forall _ _, PXA : presW _ _ _ _ _ _ _ _ _ _ _,
                            HTc : htop _ _ _ _ = _, HSc : hstkhi _ _ _ _ = _, HFc : hflag _ _ _ _ = _, HCSc : (forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x),
                            HV : havol _ _ _ _ <= _, HFR : hfr _ _ _ _ <= _, OBJ : aobj _ _ _ _ _ 192, ST : stk _ _ _ _, MI : mem_inv _ _ |- _ =>
          first [ fsA_post HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI
                | match goal with |- ?gg => idtac "fsA_post FAILED at" gg end ]
        end
    | |- ?gg => idtac "gfA_free1: free_stepA left goal" gg
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "03c0@D3399625391.127 D3399625391.128 D35881667587.127D35881667587.128K28586572680.127K28586572680.128K54978542206.127K54978542206.128L1042584046.120 L10501060432.275L13107166054.3  L13125606570.134L13127871518.229L13132193737.154L13132193737.172L13132193737.190L13132193737.208L13132193737.247L14397332440.154L14397332440.172L14407456955.134L15302269400.124L16729099351.154L16729099351.172L16729099351.190L16729099351.208L16739749684.134L16742088576.229L21405280640.229L22333560167.247L22446743512.124L22718396937.229L22725723689.9  L22797768588.239L2351528779.154 L2351528779.172 L2351528779.190 L2351528779.208 L2351528779.247 L2364491932.229 L24893298128.141L24893347280.239L24895446738.275L25214214772.124L25583542932.275L26056580736.134L26058452532.229L26070900195.154L26070900195.172L26070900195.190L26070900195.208L26070900195.226L26070900195.247L26070900195.265L27319118884.141L27484167020.154L27484167020.172L27484167020.190L27484167020.208L27494357007.134L27496360123.229L28576112895.2  L28771657273.134L28814043710.124L28908231544.190L2931019866.247 L2952290424.123 L2952475664.124 L2952475664.229 L30315877466.190L30993508591.154L30993508591.172L30993508591.190L30993508591.208L30993508591.247L30997830456.229L31000030092.134L31225147636.124L31240845022.172L33306151620.154L33306151620.172L33306151620.190L33306151620.208L33306151620.247L33316800935.134L33318877459.229L34699358651.134L34705621368.208L34705680216.124L34709680856.154L34709680856.172L34709680856.190L34750747870.208L35653441506.7  L37029553204.134L37040400215.154L37246946676.123L38660014872.229L38662222764.134L38664614095.154L38664614095.172L38664614095.190L38664614095.208L38664614095.247L3949578456.123 L40338610792.239L40373543808.124L40374333670.123L40834179097.126L41596348845.7  L41843875160.124L43057599553.121L43294563806.154L453342713.239  L453424633.141  L455442171.275  L46546467976.229L46550781791.154L46550781791.172L46550781791.190L46550781791.208L46807610334.190L48132467214.7  L49283344500.124L50619922919.172L50972137959.154L51454941784.124L52112434664.134L53441991143.190L54968017161.2  L55310518004.124L55328521149.134L55854801383.226L56141740378.208L56282532327.208L5699067096.124 L57317629527.154L57317629527.172L57317629527.190L57317629527.208L57319365940.134L57818804596.124L58591023192.124L59244667299.141L59308628179.3  L59589960295.265L60098763854.3  L609056346.154  L61321319284.124L62018535662.1  L62893530908.124L62893530908.229L63255574177.154L63255574177.172L63255574177.190L63255574177.208L63255574177.247L63259886966.229L63262094786.134L63829069812.124L66099424948.4  L66300092866.134L67280348888.124L67351568884.124L67371059166.247L6934185150.134 L6936130570.229 L6940182493.154 L6940182493.172 L6940182493.190 L6940182493.208 L6940182493.247 L7360489780.134 L7401899957.130 L7404240257.129 L8807059875.141 L920885645.229  L9311609690.172 Q15643324129.123Q17530203490.126Q17530203490.127Q18235909853.126Q18365925601.124Q18694146040.126Q21798041355.126Q21879645826.124Q22712450012.127Q22712450012.128Q25157988860.126Q25513505925.126Q25513505925.127Q25662358575.126Q26295627581.125Q26295627581.230Q27584944865.124Q27907200258.124Q30415036802.124Q31228709292.126Q31271525473.124Q31394594844.126Q32655500769.124Q33918256002.124Q34362328320.127Q34362328320.128Q35014437530.126Q36425882626.124Q3830427394.124 Q39768207371.122Q39771500367.124Q39772451766.125Q39772451766.230Q39772454703.227Q39773597451.229Q39939554818.124Q41152393185.124Q44648843873.124Q49698585326.125Q49698585326.126Q50458135125.125Q50458135125.230Q50655452946.229Q50657550166.124Q51235796833.124Q52380505067.227Q52393073871.122Q5300226131.124 Q5300226131.125 Q53969758199.126Q54057591853.126Q55145603483.127Q55145603483.128Q55732611192.125Q55732611192.230Q59843137889.124Q6416456232.126 Q66522067074.124Q66908511645.125Q66908511645.230Q67528989526.127Q67528989526.128Q8943573310.227 Q8956270106.122 Q9843367298.123 00000d01m02V03T04?05?05j06j07307S07\07e07n08708@08I08R08[08d08m09609?09H09Q09Z09c09l0:50:>0:G0:P0:Y0;10;H0;I0;J0;K0;L0;a0;b0;k0<40<=0<F0<i0=O0>50>[0?A0?g0@M0A30AY0B?0B]0CI0D50Da0EM0F90Fe0Ff0Fo0G<0GE0GN0G[0Gh0H>0HG0I<0J10Jf0K[0LV0MQ0NF0NO0NX0Nj0O<0ON0O`0P20PD0PV0P_0Ph0Q10Q:0QC0QL0QU0Qo0R80RA0RJ0RK0RL0RM0RN0RO0RP0Rh0S10SV0S_0Sh0T30T?0TH0Tf0To0U80UA0US0Uh0V=0VR0Vg0W<0WE0W`0Wi0X20X;0XD0XY0Xb0Xc0Xl0Y50Y>0YG0YP0YY0Yb0Yk0Z40Z=0ZF0ZO0ZX0Za0Zk0[40[>0[G0[P0[S0[\0[e0\O0]90]c0^M0_70_a0`K0`T0`_0``0`i0a20a;0aD0aM0aV0a_0ah0b10b:0bC0bL0bU0b^0bg0c00c<0cd0da0db0dn0e;0e<0eR0em0f]0fj0gH0h;0h<0hB0hH0hT0hj0i@0iM0iY0i_0ik0jA0jB0jC0jP0jf0k<0kB0kH0kN0kT0kZ0k`0l60lB0lN0ld0m:0m@0mF0mL0mR0m^0md0mj0n60nB0nO0nP0o@10E10O10Y10e11211H11N11T12<13913?13E13[S1R3NRT2ra2sp1A2lo3POS3LOS3SLO3SPR2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo3POS3LOS3SLO3SPR2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3HIA1h2ra2sp1A5SPTOP2TB2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01A5SPTOP2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3NRT2ra2sp1A2lo2SX3SLO2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo2SX3SLO2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3NRT2ra2sp1A2lo2SX3SLO2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo2SX3SLO2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp1A2TBS1R3HIA1h2sp1A1g2TB2H13H2'2h62HVS1R3HIA1hS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS1R2sp2lo3LOS3ALO1a1n2HnS1R3HIA1h2sp1A2TB2h42HVFFFFS1R3HIA1h2sp1A3BUD2TBFS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS1R3HIA1h2sp1A1g1d2TB2H13H2'2h63HFRS1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A1g3POS3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A3POS3ACV3SPR2TB5ACLsp1g2H13H2'S1R2sp1A1g3POS3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3ACV3SPR2TB5ACLsp2H13H2'S1R3HIA1h2sp1A1d3POS3SPR2D02TBS1R3HIA1h2sp1A1d3POS4BUDF3SPR2D02TB1g2H13H2'S1R3HIA1h2sp1A1d3POS4BUDF3SPR2D02TB1g2H13H2'S1R3HIA1h2sp1A1d3POS4BUDF3SPR2D02TB1g2H13H2'S1R3HIA1h2sp1A1d3POS4BUDF3SPR2D02TB1g2H13H2'S1R3HIA1h2sp1A1d3POS4BUDF3SPR2D02TB1g2H13H2'S1R3HIA1h2sp1A1g1d3POS4BUDF3SPR2D02TB2H13H2'FS2sp1A2TBS2sp1A3POS2TBS2sp1A2TBS2sp1A2TBS2sp1A3POS2TBS2sp1A3POS2TBS2sp1A3POS2TB1g2H13H2'S2sp1A2TBS2sp1A2TB1R3NRT2lo3AL83POS2SX3SLO3SPA3SPR1g2H12H23H2'S2sp1A2TB1R3NRT2lo3AL83POS2SX3SLO3SPA3SPR1g2H12H23H2'S2sp1A2TB1R3NRT2lo3AL83POS2SX3SLO3SPA3SPR1g2H12H23H2'S2sp1A2TB1R3NRT2lo3AL83POS2SX3SLO3SPA3SPR1g2H12H23H2'S2sp1A2TB1R3NRT1g2lo3AL83POS2SX3SLO3SPA3SPR2K12H12H23H2'2K2S2sp1A2TB1R3NRT1g2lo3AL83POS2SX3SLO3SPA3SPR2K12H12H23H2'2K2S2sp1A2TB1R3NRT2lo3AL83POS2SX3SLO3SPA3SPR1g2H12H23H2'S2sp1A2TBS2sp1A2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS1R2sp1A2lo3SLO2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS1R3HIA1h2sp2lo5SPTOP4HTOPS2sp1A2TBS2sp1A2TBS2sp1A2TBFFFFFFS1R3HIA1h2sp1A1d4BUDF2TBS2sp1A2TBS1R3HIA1h2sp1A1d3POS3SPR2D02TB2h43HFRS2sp1A2TBS2sp1A2TBS1R2sp1A2TBS2sp1A2lo2SXS2sp1A2TBS1R3NRT2sp1A2lo3POS3SLO3SPR2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A1g2TB2H13H2'S1R3HIA1h2sp1A3BUD2TBS1R3HIA1h2sp1A3BUD2TBS1R3HIA1h2sp1A3BUD2TBS1R3HIA1h2sp1A3BUD2TBS1R3HIA1h2sp1A3BUD2TBS2sp1A2TBS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS1R3HIA1h2sp1A3BUD2TBS2sp1A2TBFS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS1A3POS2K0S2sp1A2TBS1R2lo3LOSS2sp1A2TBS2sp1A2TBS1RS2sp1A2TBS2sp1A2TBS1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S1R2sp1A1g3POS3SPA3ACV3SPR2TB5ACLsp2H13H2'S2sp1A2TBS1R3HIA1h1dFS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2TBS2sp1A2lo2TBS1R3NRT2ra2sp1A2lo3SLO2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo3SLO2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS2sp1A2lo2TBS1R1A4IMG'2TBFS1R3NRT2sp1A2lo3SLO2TBS2ra2sp1A2TB2HB5Ha_st5Hl_stS2sp2s01A2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R1A4IMG'2TBS2ra2sp1A2lo2TB2HB5Ha_st5Hl_stS2sp2s01A2lo2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1A2TBS1A2TBS2sp1A2lo2TBS1R3NRT2sp1A2lo3SLO2TBS1R3NRT2sp1A2lo3SLO2TBS1R1A4IMG'2TBS2sp1A2lo2TBS1A2TBS2sp1A2lo2TBS1R3NRT2sp1A2lo3SLO2TBFFS1R1A4IMG'2TBS1R3NRT2sp1A2lo3SLO2TBS1R3NRT2sp1A2lo3SLO2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1A2TBS1R3NRT2sp1A2lo3SLO2TBS2sp1A2lo2TBS2sp1A2lo2TBS2sp1A3SPR2TB2HB5Ha_stS2sp1A3SPR2TB2HB5Ha_stS1A2TBS1A2TBS1A2TBS1A2TBS2sp1A2lo2TBS1A2TBS1A2TBS2sp1A2TB2HBS2sp1A2TB2HBS1R1A4IMG'2TBFS1R3NRT2ra2sp1A2lo3LOS3SLO3ALO2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo3LOS3SLO3ALO2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1A3POS2TBS1A3POS2TBS2sp1A2lo2TBS1R1A4IMG'2TBS1R3NRT2sp1A2lo3SLO2TBS1A2TBS1A2TBS1R3NRT2ra2sp1A2lo3SLO2TB2HB5Ha_st5Hl_stS1R3NRT2sp2s01A2lo3SLO2TB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1A2TBS1A2TBS1R3NRT2sp1A2lo3SLO2TB". (* [comment removed for export] *)
  #[using="IMG MPIFREE PZ NEEDR NEEDA DIMG HMND NRT"] Lemma A_ecp_group_free_walk : ecp_group_free_stmtA asegs R HIA MT A_ECP_GROUP_FREE.
  Proof.
    unfold ecp_group_free_stmtA, A_ECP_GROUP_FREE. intros until d.
    intros HH HK0 G DIS CW SX OBJ ST LOS SLO SPTOP SPA TP MI BUD UWO BUDF ->.
    gf_facts h.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. change (blkfacts L (LB ++ LF)) in HBR.
    unfold ECP_GROUP_SIZE in CW, SX, OBJ, UWO.
    ddestruct G as (HD & AL8 & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & Bid & Bpb & Bnb & Bh & Bmp & Btp & Btq & Btd & BT & TS & FRB & KEPT & MODP).
    unfold grp_head_cells in HD. unfold grp_tail_cells in HT.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length grp_tail_cells] in TB.
    assert (SUBF : forall b, In b (grp_free_LB g LB) -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    (* [comment removed for export] *)
    assert (GIN : forall dd, In dd (grp_free_mpds g) -> In dd (grp_mpds g)).
    { intros dd Hd. unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h g =? 1); [destruct Hd|]. destruct (g_h g =? 2); cbn in Hd |- *; tauto. }
    assert (DISF : mpds_apart (grp_free_mpds g)) by (eapply mpds_apart_sub; [exact DIS| exact GIN]).
    assert (ALLM : forall dd, In dd (grp_mpds g) -> mpdr_at asegs m LB dd).
    { intros dd Hd. unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    assert (NI : forall dd, In dd (grp_free_mpds g) -> md_own dd = LHeap -> ~ In (md_p dd, 4 * md_n dd) (grp_free_LB g LB)).
    { intros dd Hd O. unfold grp_free_LB. apply lb_free_mpds_notin; assumption. }
    assert (ACLsp : alloc_ceiling <= bv_unsigned sp) by (clear - ALO LOS SLO NEEDR; lia).
    pose proof (free_facts_introA asegs R HIA h LB LF (grp_free_LB g LB) m (bv_unsigned sp) _ A 192 (grp_free_mpds g) HH NDL
                  ltac:(intros dd Hd; apply ALLM, GIN, Hd) CW SUBF NI ACLsp ltac:(lia) DI1 DI2) as FF1.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB (grp_free_LB g LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 192)] HH ltac:(clear; lia)) SUBF) as PXA.
    pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj MI I) as MIbox. clear MP MA MB MX MY MZ MN.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS AB; lia); clear - K0 POS; lia|]. clear K0.
    (* [comment removed for export] *)
    zstep.
    assert (AL7 : Z.land A 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact AL8 | clear - AL8; Z.div_mod_to_equations; lia]).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
        pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct MIbox as [MIm _].
    assert (LIV : Forall (mpdr_at asegs m1 LB) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g]).
    { eapply (lives_munchA asegs L m m1 LB (LB ++ LF)); [| exact MU0| exact WM0| exact MIm| assumption| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| | intros a n Ha Hn; cbn; clear - Ha Hn ALO LOS; lia].
      - repeat apply Forall_cons; try apply Forall_nil; apply ALLM; unfold grp_mpds, pt_mpds; cbn; tauto.
      - repeat apply Forall_cons; try apply Forall_nil; rewrite ?EP, ?EA, ?EB, ?EX, ?EY, ?EZ, ?EN; cbn; clear - SX ALO LOS; lia. }
    clear ALLM MU0 WM0 MIm.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ (fun x Hx => Hx) OBJ) as OBJ0.
    lazymatch goal with OBJx : aobj _ _ _ m1 A 192 |- _ => shadow_chk OBJx (A + 136) 4 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with HDx : rw_cells _ m1 A _, F : rw_cells _ m1 (bv_unsigned sp + -80) ?cs |- _ =>
      lazymatch type of HT with rw_cells _ _ _ ?tcs =>
        assert (CH : Forall (fun ac => rw_cells asegs m1 (fst ac) (snd ac)) [(A, [C4 (Z_to_bv 64 (g_id g)); C4 (g_idpad g)]); (A + 120, tcs); (bv_unsigned sp - 80, cs)])
          by (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact HDx| exact HT| replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; exact F]);
        clear HDx F HT end end.
    pose proof (eq_refl (htop asegs R HIA h)) as HTc. pose proof (eq_refl (hstkhi asegs R HIA h)) as HSc. pose proof (eq_refl (hflag asegs R HIA h)) as HFc.
    assert (HCSc : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h x) by (intros x Hx; exact Hx).
    assert (HV : havol asegs R HIA h <= havol asegs R HIA h + 0 * AVOL_CALL) by (clear; lia).
    assert (HFR : hfr asegs R HIA h <= hfr asegs R HIA h + 0 * fr_charge d) by (clear; lia).
    unfold GF_PHI in BUD. unfold GF_FR in BUDF.
    lazymatch goal with STx : stk _ m1 lo _, MIx : mem_inv _ m1 |- _ => rename STx into ST; rename MIx into MI end.
    if_cases K1; zify_cond K1.
    all: cycle 1.
    { (* [comment removed for export] *)
      assert (H1 : (g_h g =? 1) = false).
      { apply Z.eqb_neq. intros E. apply K1. apply (proj2 (sx32_small_eq (g_h g) 1 Bh ltac:(lia))). exact E. }
      destruct (Z.eq_dec (g_h g) 2) as [H2|H2].
      - (* [comment removed for export] *)
        pose proof H2 as H2'. apply Z.eqb_eq in H2'.
        unfold grp_free_mpds, grp_kept_mpds in FRB, KEPT. rewrite H1, H2' in FRB, KEPT. cbn [app pt_mpds] in FRB, KEPT.
        assert (EQM : grp_free_mpds g = [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)]) by (unfold grp_free_mpds; rewrite H1, H2'; reflexivity).
        assert (EQF : grp_free_LB g LB = lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] LB) by (unfold grp_free_LB; rewrite EQM; reflexivity).
        rewrite EQM in FF1, DISF, NI. rewrite EQF in CW, PXA, NI, SUBF.
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_A g) (A + 24) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] [g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_B g) (A + 40) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] [pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_X (g_G g)) (A + 56) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] [pt_Y (g_G g); pt_Z (g_G g)].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_Y (g_G g)) (A + 72) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] [pt_Z (g_G g)].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_Z (g_G g)) (A + 88) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] ([] : list mpd).
        (* [comment removed for export] *)
        fa_get CH 6%nat HT.
        lazymatch goal with OBJx : aobj _ _ _ _ A 192 |- _ => shadow_chk OBJx (A + 136) 4 end.
        zstep. clear HT. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; apply K2; apply (proj2 (sx32_small_eq (g_h g) 2 Bh ltac:(lia))); exact H2].
        fa_get CH 0%nat CZ. fa_get CH 1%nat CY. fa_get CH 2%nat CX. fa_get CH 3%nat CB_. fa_get CH 4%nat CA_. fa_get CH 5%nat CHD. fa_get CH 6%nat CTL. fa_get CH 7%nat CFR.
        pose proof (proj1 (Forall_inv LIV)) as CN. rewrite EN in CN. pose proof (proj1 (Forall_inv (Forall_inv_tail LIV))) as CP. rewrite EP in CP.
        to_tailA sp EQF.
      - (* [comment removed for export] *)
        pose proof H2 as H2'. apply Z.eqb_neq in H2'.
        unfold grp_free_mpds, grp_kept_mpds in FRB, KEPT. rewrite H1, H2' in FRB, KEPT. cbn [app pt_mpds] in FRB, KEPT.
        assert (EQM : grp_free_mpds g = [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g]) by (unfold grp_free_mpds; rewrite H1, H2'; reflexivity).
        assert (EQF : grp_free_LB g LB = lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] LB) by (unfold grp_free_LB; rewrite EQM; reflexivity).
        rewrite EQM in FF1, DISF, NI. rewrite EQF in CW, PXA, NI, SUBF.
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_A g) (A + 24) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_B g) (A + 40) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_X (g_G g)) (A + 56) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_Y (g_G g)) (A + 72) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [pt_Z (g_G g); g_N g; g_P g].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (pt_Z (g_G g)) (A + 88) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [g_N g; g_P g].
        (* [comment removed for export] *)
        fa_get CH 6%nat HT.
        lazymatch goal with OBJx : aobj _ _ _ _ A 192 |- _ => shadow_chk OBJx (A + 136) 4 end.
        zstep. clear HT. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; apply H2; apply (proj1 (sx32_small_eq (g_h g) 2 Bh ltac:(lia))); exact K2|].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_N g) (A + 104) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] [g_P g].
        zstep. zstep. gfA_free1 (bv_unsigned sp + -80) (g_P g) (A + 8) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] ([] : list mpd).
        fa_get CH 0%nat CP. fa_get CH 1%nat CN. fa_get CH 2%nat CZ. fa_get CH 3%nat CY. fa_get CH 4%nat CX. fa_get CH 5%nat CB_. fa_get CH 6%nat CA_.
        fa_get CH 7%nat CHD. fa_get CH 8%nat CTL. fa_get CH 9%nat CFR.
        to_tailA sp EQF. }
    (* [comment removed for export] *)
    assert (H1 : g_h g = 1) by (apply (proj1 (sx32_small_eq (g_h g) 1 Bh ltac:(lia))); exact K1).
    assert (EQF : grp_free_LB g LB = LB).
    { unfold grp_free_LB, grp_free_mpds. rewrite (proj2 (Z.eqb_eq _ _) H1). reflexivity. }
    fa_get CH 0%nat CHD. fa_get CH 1%nat CTL. fa_get CH 2%nat CFR.
    fa_get LIV 0%nat LA. fa_get LIV 1%nat LB_. fa_get LIV 2%nat LX. fa_get LIV 3%nat LY. fa_get LIV 4%nat LZ. fa_get LIV 5%nat LN. fa_get LIV 6%nat LP.
    apply proj1 in LA. apply proj1 in LB_. apply proj1 in LX. apply proj1 in LY. apply proj1 in LZ. apply proj1 in LN. apply proj1 in LP.
    rewrite EA in LA. rewrite EB in LB_. rewrite EX in LX. rewrite EY in LY. rewrite EZ in LZ. rewrite EN in LN. rewrite EP in LP.
    replace (A + 56 + 16) with (A + 72) in LY by lia. replace (A + 56 + 32) with (A + 88) in LZ by lia.
    to_tailA sp EQF.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GF.

Lemma A_ecp_group_free_spec : forall R (HIA : artA asegs R) MT,
  asan_img_ok (arl_AL R) -> mpi_free_stmtA asegs R HIA A_MPI_FREE -> platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE ->
  0 <= arl_need_rt R -> 0 <= arl_need_amem R ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  (forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  ecp_group_free_stmtA asegs R HIA MT A_ECP_GROUP_FREE.
Proof. intros. eapply A_ecp_group_free_walk; eauto. Qed.
