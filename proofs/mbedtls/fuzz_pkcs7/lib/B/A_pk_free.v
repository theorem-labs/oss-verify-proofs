(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa RepCrt RepPk CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_rsa_free P_ecp_group_free P_ecp_keypair_free P_pk_wrap_rsa P_pk_wrap_eckey P_pk_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_platform_zeroize
     A_free_seq A_rsa_free A_ecp_group_free A_ecp_keypair_free A_pk_wrap_free A_pk_defs A_oid A_crt_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.
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
Definition A_PK_FREE : Z := 0x0b1740.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STKpk (R : art_layout) : Z := 192 + arl_need_rt R.
Definition PHIpk (k : Z) : Z := 14 * AVOL_CALL.
Definition FFRpk (k d : Z) : Z := 13 * fr_charge 0 + Z.max 0 (fr_charge d).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PKA_inst (MT : list modp_ent) : pk_class asegs := PKC_inst asegs A_RSA_INFO A_EC_INFOS MT.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59315527917.2000001S". (* [comment removed for export] *)
Lemma PHIpk0 : forall k, 0 <= k -> 0 <= PHIpk k. Proof. intros. unfold PHIpk, AVOL_CALL. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L26180797511.4000006S1d2H0". (* [comment removed for export] *)
Lemma FFRpk0 : forall k d, 0 <= k -> 0 <= d -> 0 <= FFRpk k d. Proof. intros. unfold FFRpk, fr_charge. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L37672506388.3000001S". (* [comment removed for export] *)
Lemma PHIpk_mono : forall k k', 0 <= k <= k' -> PHIpk k <= PHIpk k'. Proof. intros. unfold PHIpk. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11563869264.4000003S1d". (* [comment removed for export] *)
Lemma FFRpk_mono : forall k k' d, 0 <= k <= k' -> FFRpk k d <= FFRpk k' d. Proof. intros. unfold FFRpk. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b17e8]).
Local Ltac zchk_new ::= constr:([0x0b1750; 0x0b1754; 0x0b177c; 0x0b1780]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section PKF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variable MT : list modp_ent.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis RSAW : rsa_free_wrap_stmtA asegs R HIA A_RSA_FREE_WRAP.
  Hypothesis ECW : eckey_free_wrap_stmtA asegs R HIA MT A_ECKEY_FREE_WRAP.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2613541441.12000009S1R5NEEDA". (* [comment removed for export] *)
  Let NRT : arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation POST h0 LBo LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PKA owned lo d m0 mo0 :=
    (pk_free_postA asegs R HIA PHIpk FFRpk h0 LBo LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PKA owned lo d m0 mo0).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@C17025492443.119C18101512239.120D4438115357.121 D60109446735.121K42840361841.119K61093937827.119L1207681809.1   L14840251550.1  L20427738366.101L31399144472.100L32049487064.101L34423640368.6  L35653441506.10 L3828130586.101 L38948636245.0  L42843969812.3  L50560326147.1  L52509853291.5  L55978761415.100L56552377779.101L60098763854.3  L61097676998.2  L881835912.0    O17025492443.119O67666899643.119P61093937827.119Q15636964089.101Q15766564435.120Q32074401846.120Q32074401846.121Q3828130586.101 Q41575055087.120Q47233263673.120Q50554033684.120Q50554033684.121Q50840533351.120Q51229703033.101Q9845526938.101 00000100600700O00d00e00j00k01:01I01X01i02O03303403503:03M03\03k04504604704804904:04H04]04i05505M05N05Z05f06206@06N06fFS3PKAFS1R2sp3PKA2lo2cs3HSZ3LOSS2sp3PKA2lo2cs3HSZ2SXFS3PKAFS2sp3PKA2cs3HSZS2sp3PKA2cs3HSZS2sp3PKA2cs3HSZS1R3NRT2sp2lo3SLOS1R3HIA2sp2h02hc2lo3HTc3HSc5SPTOP4HTOPS1R3NRT2sp3PKA2lo2cs3HSZ3POS3SLO3SPRSFS3PKAS1R3HIA2sp2h05SPTOPS2sp3PKA2cs3HSZS2sp3PKA2cs3HSZS1R2lo3LOSFSFFFS2sp2lo2cs3HSZS1R2lo2cs3HSZ3LOS3ALOS3PKA2cs3HSZS3PKA2cs3HSZS1R3NRT2sp2lo2cs3HSZ3SLOFS3PKA2cs3HSZS3PKA2cs3HSZS3PKA2cs3HSZS2sp2lo2cs3HSZS2sp2lo2cs3HSZS1R3NRT2sp2lo2cs3HSZ3SLO". (* [comment removed for export] *)
  #[using="PZ NEEDA NRT"] Lemma tail_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xra xs0 : word) (m0 mm : mem) (mo0 : Model) (h0 hc : HST asegs R HIA)
      (LBo LB LF LBo' owned : list blk) (PKA lo d : Z) (cs : list cell),
    HM asegs R HIA hc (LBo' ++ LB) LF mm ->
    htop asegs R HIA hc = htop asegs R HIA h0 -> hstkhi asegs R HIA hc = hstkhi asegs R HIA h0 -> hflag asegs R HIA hc = hflag asegs R HIA h0 ->
    (forall x, hcs asegs R HIA h0 x -> hcs asegs R HIA hc x) ->
    havol asegs R HIA hc <= havol asegs R HIA h0 + PHIpk (Z.of_nat (length owned)) ->
    hfr asegs R HIA hc <= hfr asegs R HIA h0 + FFRpk (Z.of_nat (length owned)) d ->
    rw_cells asegs mm PKA cs -> cells_size cs = 16%nat -> PKA mod 8 = 0 -> 0 < PKA ->
    rw_cells asegs mm (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
    presW asegs R HIA h0 (LBo' ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] m0 mm ->
    client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h0) PKA 16 -> (PKA + 16 <= lo \/ bv_unsigned sp <= PKA) ->
    aobj asegs AL (hcs asegs R HIA h0) mm PKA 16 ->
    stk asegs mm lo (bv_unsigned sp - 16) -> arl_stklo R <= lo -> lo <= bv_unsigned sp - STKpk R ->
    bv_unsigned sp <= htop asegs R HIA h0 -> bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 (arl_tp R) -> mem_inv asegs mm ->
    (forall b, In b LBo' -> In b LBo) -> (forall b, In b LBo -> ~ In (fst b) (map fst owned) -> In b LBo') ->
    (forall b, In b LBo' -> ~ In (fst b) (map fst owned)) -> List.NoDup (map fst (LBo' ++ LB)) ->
    aevtA asegs (KF asegs R HIA hc mo0) (POST h0 LBo LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PKA owned lo d m0 mo0)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 xs0 s1 (Z_to_bv 64 PKA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb17c4) fc None mm (seg_rom asegs)).
  Proof.
    intros until cs. intros HH HTc HSc HFc HCSc HV HFR HPK HSZ AL8 POS FR PXA CW SX OBJ ST LOS SLO SPTOP SPA TP MI SUB KEEP GONE NDL.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_ok asegs R HIA h0) as CSOK. pose proof (hcs_ok asegs R HIA hc) as CSOKc. unfold STKpk in SLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA hc _ LF mm HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h0) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h0)| clear - LOS; lia| clear - SPTOP HTOP HTc HSc; lia]).
    pose proof (crange_mono _ _ _ _ HCSc SCS) as SCSc.
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo0) as KINV.
    pose proof (hm_wlow asegs R HIA hc _ _ mm HH) as WL.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJ) as OBJc.
    pose proof (rw_cells_CB_of asegs mm PKA cs ltac:(rewrite HSZ; clear; lia) HPK) as J. rewrite HSZ in J. change 16%nat with (Z.to_nat 16) in J at 1. clear HPK.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in FR, ST |- * by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ. specialize SPZ with (h := hc). rewrite HTc in SPZ.
    acallxA_sp (bv_unsigned sp)
      (eapply SPZ with (LB := LBo' ++ LB) (LF := LF) (A := PKA) (n := 16) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp)) by (clear - SPR; lia);
       first [ exact HH | exact J | exact POS | exact LOS | exact OBJc | exact SX | exact SPA | exact TP | reflexivity
             | lazymatch goal with
               | |- 0 <= 16 => clear; lia
               | |- 16 < _ => clear; lia
               | |- stk _ _ lo _ => assumption
               | |- lo <= _ => clear - SLO NEEDR NRT; lia
               | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
               | |- mem_inv _ _ => assumption
               | |- client_wrange _ _ _ _ PKA 16 =>
                   eapply (client_wrange_weak L); [exact CW| apply lb_sub_app with (L1 := LBo' ++ LB) (L1' := LB); intros b Hb; apply in_app_iff; right; exact Hb| clear - LOS; lia| clear; lia| clear; lia]
               end
             | match goal with |- ?gg => idtac "PZ-LEFT:" gg end ]).
    clear SPZ.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold pk_free_postA.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => deexists 15; dexists mx, mo9, hc, LBo' end.
    split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [exact MF9|].
    split; [lazymatch goal with HP : presW _ _ _ _ _ _ _ _ _ m0 _ |- _ => exact (presW_presA asegs R HIA h0 _ LF _ _ _ _ _ HP) end|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [exact HV|]. split; [exact HFR|]. split; [assumption|].
    split; [exact SUB|]. split; [exact KEEP|]. split; [exact GONE|]. split; [exact NDL|].
    lazymatch goal with HZ : rw_cells _ _ PKA [CB (Z.to_nat 16) _] |- _ =>
      apply (rw_cells_zeros asegs _ PKA 16 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in HZ; [exact HZ| cbn; repeat split; reflexivity | reflexivity] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "03X0@D13156179990.101D13156179990.126D13156179990.132D31501237935.100D31501237935.125D31501237935.131D35881667587.100D35881667587.101D35881667587.125D35881667587.126D35881667587.131D35881667587.132K64113782398.100K64113782398.101K64113782398.125K64113782398.126K64113782398.131K64113782398.132L11774327555.121L11774327555.127L11774327555.97 L17236181202.7  L17377155252.4  L19579855574.148L19579855574.153L19592621266.97 L20433961190.121L20433961190.127L20433961190.96 L22184330147.2  L24028945090.6  L2826134040.122 L2826430984.126 L29010380273.121L29010380273.127L29010380273.97 L32049487064.120L32049487064.126L32049487064.96 L33394907792.3  L34061135516.1  L3523383060.9   L35653441506.7  L36012194261.121L36012194261.127L39433892856.2  L39972690504.6  L40281191306.3  L40834179097.123L40834179097.129L40834179097.99 L41598571912.8  L42121540001.0  L42243864624.5  L4233431390.5   L43057222721.119L43057632321.125L43059266357.94 L4584282030.4   L46321906721.1  L46748113268.120L46748113268.126L46748113268.96 L48223984434.125L49530003784.1  L49950606476.2  L49952869148.120L49952869148.126L49952869148.96 L49953061438.121L49953061438.127L49953061438.97 L50560326147.1  L52564138800.5  L53735577720.120L53735577720.124L56552377779.121L56552377779.127L56552377779.97 L56828088003.123L56828088003.127L59308628179.3  L59308631400.1  L59308631400.3  L60033831730.120L60098763854.3  L62018535662.1  L62705181399.5  L64116126217.2  L66151427842.16 L6667565768.12  L68379241549.7  P22183709222.131P22183709222.132Q10057150483.125Q10057150483.129Q10883745538.122Q10883745538.126Q13296972522.123Q13296972522.129Q13296972522.98 Q14525642139.100Q14525642139.125Q14525642139.131Q15643324129.121Q15643324129.127Q15643324129.96 Q16223813922.130Q1772245131.124 Q1772542107.128 Q18694146040.124Q18694146040.130Q18694146040.99 Q20685106778.101Q20685106778.126Q20685106778.132Q21798041355.124Q21798041355.130Q21798041355.99 Q22712450012.100Q22712450012.101Q22712450012.125Q22712450012.126Q22712450012.131Q22712450012.132Q22985421705.128Q22985653145.124Q25157988860.124Q25157988860.130Q25157988860.99 Q25513505925.100Q25513505925.124Q25513505925.125Q25513505925.130Q25513505925.131Q25513505925.99 Q25662358575.124Q25662358575.130Q25662358575.99 Q29312881484.123Q29312881484.129Q29312881484.98 Q31228709292.124Q31228709292.130Q31228709292.99 Q31255363106.123Q31255363106.129Q31255363106.98 Q31394594844.124Q31394594844.130Q31394594844.99 Q35014437530.124Q35014437530.130Q35014437530.99 Q36171140397.124Q36171140397.130Q36171140397.99 Q36801578553.100Q36801578553.125Q36801578553.131Q37426957269.122Q37426957269.128Q37426957269.97 Q3830427394.122 Q3830427394.128 Q3830427394.97  Q38799620956.125Q38799620956.129Q39841439690.130Q41638316336.122Q41638316336.126Q42024716493.122Q42024716493.128Q42024716493.97 Q42304915680.128Q42305124802.125Q42305124802.129Q42305143024.124Q43852298839.129Q45629951761.130Q45914037331.122Q45914037331.128Q45914037331.97 Q49125254656.100Q49125254656.101Q49125254656.125Q49125254656.126Q49125254656.131Q49125254656.132Q49241094109.124Q49241094109.130Q49241094109.99 Q49698585326.123Q49698585326.124Q49698585326.129Q49698585326.130Q49698585326.98 Q49698585326.99 Q50558264496.123Q50558264496.129Q50558264496.98 Q50558457234.122Q50558457234.128Q50558457234.97 Q51235796833.122Q51235796833.128Q51235796833.97 Q53440817419.123Q53440817419.127Q53441140777.122Q53441140777.126Q53969758199.124Q53969758199.130Q53969758199.99 Q54520642575.123Q54520642575.127Q58146298210.124Q58146298210.130Q58146298210.99 Q61720189051.130Q63116570093.123Q63116570093.127Q6416456232.124 Q6416456232.130 Q6416456232.99  Q67528989526.125Q67528989526.126Q67528989526.131Q67528989526.132Q9843367298.121 Q9843367298.127 Q9843367298.96  00000c01]02^03Q04K05L06406\07H08408e09V0:@0:j0;g0<d0=[0>R0>^0>o0?70?M0?Z0?f0@70@?0@K0@\0@d0@e0A80AZ0B00B<0BM0BU0Ba0C20C:0CC0CG0Cj0DD0Df0E<0EE0E\0Ee0F30FF0FP0Fg0Fh0G50GC0Gg0HR0Ho0I00I50IA0IR0IZ0Ik0Io0J80JL0Je0K50KI0Kb0L20L70LD0LX0M10M=0MN0MV0Mg0N80ND0NH0NV0Nb0Nl0No0OA0OB0O\0PA0PZ0QS0RL0Rn0SR0SW0S\0Sc0Sj0T10T\0UG0V20V90V@0VG0VY0V_0Ve0Vm0W50W=0Wh0XS0Y>0Y?0Y@0YA0YW0Ym0ZC0ZY0Zo0[E0[K0[Q0[Y0[a0[i0\B0\[0]40]M0]f0^?0^@0^A0^B0^]0_?0_S0_\0_e0_n0`30`80`=0`>0`?0`@0`I0`R0`[0`\0`]0`^0aA0ad0bG0bL0bQ0bV0bg0c80cI0cO0cU0c`0ce0cj0co0d40d90d?0dE0dK0dQ0dR0dS0dZ0da0dh0di0dj0dk0dl0dm0dn0do0e00e10eB0eS0ed0f50fF0fW0f\0fa0ff0fk0g00g50g<0gC0gJ0gO0gT0gY0g^0gg0h00h90h>0hC0hf0iI0il0im0jH0jj0k20k:0kB0ke0lH0lk0mN0m_0n00nAS1R3NRT2sp2s03PKA2lo3POS3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R3NRT2sp2s03PKA3ctx2lo3POS3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3NRT2sp2s03PKA4info3ctx2lo3POS3LOS3SLO3SPR4INFB2HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA2lo3POS3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA3ctx2lo3POS3LOS3SLO3SPR2C02HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA4info3ctx2lo3POS3LOS3SLO3SPR4INFB2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp3PKA5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03PKA5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp3PKA3ctx5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03PKA3ctx5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp3PKA4info3ctx5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s03PKA4info3ctx5SPTOP2HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA2lo2SX3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s03PKA2lo2SX3SLO2HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA4info2lo4EINF2NI2SX3SLO5EINF'2HB5Ha_st5Hl_stS1R3NRT2sp2s03PKA4info2lo4EINF2NI2SX3SLO5EINF'2HB5Ha_st5Hl_stS1R3NRT2ra2sp3PKA4info2lo2NI2SX3SLO4INFB2HB5Ha_st5Hl_stS1R3NRT2sp2s03PKA4info2lo2NI2SX3SLO4INFB2HB5Ha_st5Hl_stS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS1R3HIA1h1d2D02h54HFR5S1R3HIA1h3BUDS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAFS1R3HIA1h1d4BUDF2D0S2sp3PKA4info3ctx3POS3SPR5EINF'2C0S2sp3PKA4info3ctx4INFBS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS1R3HIA1hS2spS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACP3SPRS1R3HIA1h2sp2lo5SPTOP4HTOPS2sp3PKA4info3ctx3POS3SPR5EINF'2C0S2sp3PKA4info3ctx4INFBS4info2EIS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1hS1R2sp3PKA3ctxS1R2sp3PKA4info3ctxS1R2sp3PKAS1R2sp2lo3LOS3ALO2dd2I4SS1R2sp2lo3SLOS1R3HIA1h1d2D0S1R3NRT2sp3PKA3ctx2lo3POS3SLO3SPR2C0S1R3NRT2sp3PKA4info3ctx2lo3POS3SLO3SPR4INFBS1R3NRT2sp3PKA2lo3POS3SLO3SPRFS3PKAS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS2sp3PKA4info3ctxS2spS3PKA3PKBS2sp3PKA3ctx3POS3PKBS2sp3PKA4info3ctx3POS3PKBS2sp3PKA3POS3PKBS2sp3PKA3ctx3POS3PKBS2sp3PKA4info3ctx3POS3PKBS2sp3PKA3POS3PKBS3PKAS1R2sp2lo3SLOS2sp3PKA3ctx3POS3PKBS2sp3PKA4info3ctx3POS3PKBS2sp3PKA3ctxS2sp3PKA4info3ctxS2sp3PKAS2sp3PKA4info3ctxS2sp3PKA4info3ctxS3PKA3POS2K0S2KIS4info4INFB2KIS2sp3PKA3ctxS1R2lo3LOSS1RS1R3HIA1h2sp5SPTOPFS2sp2r03SPA1q1r1H2H02q02H4S1R3HIA1h2sp3PKA2lo2SX3SPx2HS1a2Ha2HsS1R2sp3ctx2lo3LOS3ALO3CCES1R3NRT2ra2sp4info2lo3LOS3SLO3ALO3ACV4INFB2HB5Ha_st5Hl_stS1R3NRT2sp2s04info2lo3LOS3SLO3ALO3ACV4INFB2HB5Ha_st5Hl_stS2sp3PKA4info3ctx3POS3SPR5EINF'2C0S2sp3PKA4info3ctx3POS3SPR4INFB5INFALS3PKAS3PKAS2sp2HBS2sp2HBS2sp2HBS1R3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2sp2loS2sp2loS2sp2loS1R4info4IMG'4INFBS4infoS4infoS1R4IMG'S1R4IMG'S1R4IMG'S1R3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stFFFS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS4infoS4infoS1R4IMG'S1R4IMG'S1R4IMG'S2sp2s02lo2HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stFFFS2sp3PKA3ctx3AL83POS3SPR2C0S2sp3PKA4info3ctx3AL83POS3SPR4INFBS2sp3PKA3AL83POS3SPRS1R5ALWF'S1R5ALWF'S1R5ALWF'S3PKAS3PKAS3PKASSSS1R5ALWF'S1R5ALWF'S1R5ALWF'FFFS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS3PKAS3PKAS3PKAS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS4infoS4infoS4info4INFBS3PKAS3PKAS3PKAS3PKAS3PKAS4infoS4infoS4infoS4infoFFS2sp2HBS2sp2HBS2sp2HBFFFFFFFFFS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS3PKAS3PKAS3PKAS3PKAS3PKAS3PKAS2sp2loS2sp2loS2sp2loS3PKAS3PKAS3PKAS3PKAS1R5ALWF'S1R5ALWF'S1R5ALWF'S3PKAS3PKAS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stFS2sp3PKA3ctx3AL83POS3SPR2C0S2sp3PKA4info3ctx3AL83POS3SPR4INFBS1R4IMG'S1R4IMG'S1R4IMG'S1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLOS1R3NRT2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG RTC PZ RSAW ECW NEEDR NEEDA DIMG HMND NRT"] Theorem A_pk_free_walk : pk_free_stmtA asegs R HIA (PKA_inst MT) PHIpk FFRpk (STKpk R) A_PK_FREE.
  Proof.
    unfold pk_free_stmtA, A_PK_FREE. intros until d.
    intros HH HK0 HPKA AL8 POS REP OWN NDL OBJ CW SX ST LOS SLO SPTOP SPA MI TP BUD UWO BUDF ->.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h _ LF m HH) as HTOP. unfold STKpk in SLO.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact (hcs_stack asegs R HIA h)| clear - LOS; lia| clear - SPTOP HTOP; lia]).
    pose proof DIMG as [DI1 DI2]. pose proof (uw_obj_nonneg _ _ _ _ UWO) as D0.
    destruct (hm_apart asegs R HIA h _ LF m HH) as [HBR HAP]. change (blkfacts L ((LBo ++ LB) ++ LF)) in HBR.
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    cbn [PKA_inst PKC_inst pk_rep] in REP.
    (* [comment removed for export] *)
    destruct REP as [(-> & -> & ->)|[(EINF & NI & MIr & r & RA & EO)|(EI & NI & MIr & k & KP & CIN & APT & PNE & AL16 & CB256 & EO)]].
    - (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (presW_init asegs R HIA h (LBo ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] HH ltac:(clear; lia)) as PXA.
      pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
      carve_frame 16%nat ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS PKB; lia); clear - K0 POS; lia|]. clear K0.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
          pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
      zstep. zstep. zstep. clear GOT GSB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in * by lia.
      eapply tail_walk with (LBo' := LBo) (owned := []); first [eassumption | reflexivity | match goal with |- ?gg => idtac "T0-LEFT:" gg end].
      all: try (intros b Hb; exact Hb). all: try (intros b Hb _; exact Hb). all: try (intros b _ Hin; exact Hin).
      all: try (intros x Hx; exact Hx).
      all: try (unfold PHIpk, AVOL_CALL; clear; lia). all: try (unfold FFRpk, fr_charge; clear - D0; lia).
      all: match goal with |- ?gg => idtac "T0-LEFT2:" gg end.
    - (* [comment removed for export] *)
      pose proof (map_fst_iff _ _ EO) as EOf. pose proof EINF as EINF'. unfold A_RSA_INFO in EINF'.
      pose proof RA as RAc. ddestruct RAc as (_ & _ & _ & _ & _ & _ & _ & ALL & CAL & C0 & CBr & CINr & _). unfold RSA_CTX_SIZE in CBr, CINr.
      destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact CINr)) as (_ & _ & CCE & CIM).
      (* [comment removed for export] *)
      assert (NOL : forall a, In a (map fst ((ctx, 232) :: rsa_limb_blocks r)) -> ~ In a (map fst LB)).
      { intros a Ha. eapply NoDup_app_notin; [exact NDL|]. apply in_map_iff in Ha. ddestruct Ha as (b & <- & Hb).
        apply in_map_iff. exists b. split; [reflexivity| apply OWN; apply EO; exact Hb]. }
      assert (LEQ : lb_remove ctx (rsa_free_LB r (LBo ++ LB)) = lb_remove ctx (rsa_free_LB r LBo) ++ LB).
      { unfold rsa_free_LB. rewrite !lb_free_mpd_app. 1: apply lb_remove_app.
        - apply NOL. left. reflexivity.
        - intros HO. apply NOL. right. unfold rsa_limb_blocks. rewrite map_app. apply in_or_app. left. unfold mpd_blk. rewrite HO. left. reflexivity.
        - intros HO. apply NOL. right. unfold rsa_limb_blocks. rewrite map_app. apply in_or_app. right. unfold mpd_blk. rewrite HO. left. reflexivity. }
      set (LBo' := lb_remove ctx (rsa_free_LB r LBo)) in *.
      assert (SUBo : forall b, In b LBo' -> In b LBo).
      { intros b Hb. subst LBo'. apply lb_remove_sub in Hb. unfold rsa_free_LB in Hb. do 2 apply lb_free_mpd_sub in Hb. exact Hb. }
      assert (SUB' : forall b, In b (LBo' ++ LB) -> In b (LBo ++ LB)) by (apply lb_sub_app; exact SUBo).
      assert (OCR : forall LBx SPx, (forall b, In b LB -> In b LBx) -> SPx <= bv_unsigned sp -> client_range L (LBx ++ fdata LF) SPx PKA 16).
      { intros LBx SPx HI HS a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]].
        - left. clear - Hs Ha SX HS. lia.
        - right; left. exact Hd.
        - right; right. exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI, Hb| right; exact Hb]. }
      apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (presW_sub_blocks asegs R HIA h (LBo ++ LB) (LBo' ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] m m
                    (presW_init asegs R HIA h (LBo ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] HH ltac:(clear; lia)) SUB') as PXA.
      pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
      pose proof (conj MI I) as MIbox. pose proof (conj RA ALL) as RAbox. clear RA ALL MIr.
      carve_frame 16%nat ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS PKB; lia); clear - K0 POS; lia|]. clear K0.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
          pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
      zstep. zstep. zstep. clear GOT GSB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KI; zify_cond KI; [exfalso; clear - KI EINF; subst info; unfold A_RSA_INFO in KI; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      (* [comment removed for export] *)
      lazymatch goal with HHx : HM _ _ _ h _ LF m1 |- _ =>
        pose proof (aobj_img asegs _ (hcs asegs R HIA h) m1 (A_RSA_INFO + 80) 8 (hcs_img_cs R HIA h IMG (proj2 (proj2 (proj2 IMG')))) (hm_img_shadow asegs R HIA h _ LF m1 HHx) ltac:(vm_compute; reflexivity)) as OI;
        pose proof (asan_rtc_const m1 (A_RSA_INFO + 80) [Z_to_bv 8 116; Z_to_bv 8 31; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
                      (RTC m1 (hm_rtc asegs R HIA h _ LF m1 HHx)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as TB end.
      cbn [length] in TB. rewrite <- EINF in OI, TB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. try (if_cases KF; zify_cond KF; [exfalso; revert KF; clear; intros KF; rewrite ?unsigned_lit in KF by lia; cbn in KF; lia|]; clear KF).
      clear OI TB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      destruct MIbox as [MIm _]. destruct RAbox as [RA ALL].
      assert (RA1 : rsa_at asegs m1 (LBo ++ LB) ctx r).
      { eapply rsa_at_munch; [exact RA| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - CCE ALO LOS; lia|].
        intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m (LBo ++ LB) ((LBo ++ LB) ++ LF) dd) as (_ & _ & I3 & I4 & _);
          [apply (proj1 (Forall_forall _ _) ALL); exact Hd| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia]. }
      clear MU0 WM0 MIm RA ALL.
      (* [comment removed for export] *)
      zstep.
      pose proof RSAW as SG. unfold rsa_free_wrap_stmtA, A_RSA_FREE_WRAP in SG.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SG with (h := h) (LB := LBo ++ LB) (LF := LF) (C := ctx) (r := r) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by (clear - SPR SLO NEEDR LOS ALO ACP; lia); rewrite ?(unsigned_lit PKA) by (clear - PKB; lia);
          first [ exact HK1 | exact RA1 | exact LOS | exact TP | reflexivity
                | lazymatch goal with
                  | |- HM _ _ _ h _ LF _ => assumption
                  | |- stk _ _ lo _ => assumption
                  | |- lo <= _ => clear - SLO NEEDR; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                  | |- mem_inv _ _ => assumption
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold PHIpk in BUD; unfold RSA_FREE_WRAP_PHI, RSA_FREE_PHI, AVOL_CALL in *; clear - BUD; lia
                  | |- uw_obj _ _ 1 d => eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRpk in BUDF; unfold RSA_FREE_WRAP_FR, RSA_FREE_FR, fr_charge in *; clear - BUDF D0; lia
                  end
                | match goal with |- ?gg => idtac "RW-LEFT:" gg end ]. }
      cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m5 & mo5 & h5 & E & PO).
      injection E as -> ->.
      ddestruct PO as (MI5 & ST5 & MF5 & PX5 & HT5 & HS5 & HF5 & HK5 & HCS5 & HV5 & HFR5 & HH5).
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST5, PX5 by (clear - SPR SLO NEEDR LOS ALO ACP; lia).
      rewrite LEQ in HH5, PX5.
      replace (ret_pc (Z_to_bv 64 0xb17c0)) with (Z_to_bv 64 0xb17c0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ =>
        pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m5 _ _ PX5 FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(exact I)) as FR5; clear FRx end.
      lazymatch goal with HPx : rw_cells _ m1 PKA _ |- _ =>
        pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m5 _ _ PX5 HPx ltac:(apply OCR; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]) ltac:(exact I)) as HPKA5; clear HPx end.
      lazymatch goal with OBJx : aobj _ _ (hcs _ _ _ h) m1 PKA 16 |- _ =>
        pose proof (presA_aobj asegs R (hcs asegs R HIA h) _ _ _ _ _ _ m1 m5 PKA 16 CSOK PX5 OBJx ltac:(apply OCR; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]) ltac:(clear - LOS SLO NEEDR; lia) ltac:(intros x Hx; eapply hcs_below_top; exact Hx)) as OBJ5; clear OBJx end.
      assert (PXA5 : presW asegs R HIA h (LBo' ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] m m5).
      { eapply presW_call; [exact PXA| exact PX5| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
      pose proof (HMND _ _ _ _ HH5) as NDL5.
      clear PXA PX5 SG RA1.
      repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                           | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H end.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h5 mo) _ _ mo5 (conj HK5 (mo_frame_trans _ _ _ MF1 MF5))).
      pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo) as KINV.
      zstep.
      replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in * by lia.
      assert (KEEP1 : forall b, In b LBo -> ~ In (fst b) (map fst owned) -> In b LBo').
      { intros [B kk] Hb Hn0. cbn [fst] in Hn0. assert (Hn : ~ In B (map fst ((ctx, 232) :: rsa_limb_blocks r))) by (intros X; exact (Hn0 (proj2 (EOf B) X))).
        cbn [map fst] in Hn. subst LBo'. apply In_lb_remove_keep; [| intros ->; apply Hn; left; reflexivity].
        unfold rsa_free_LB. apply lb_free_mpd_keep; [apply lb_free_mpd_keep; [exact Hb|]|];
          intros HO E; apply Hn; right; unfold rsa_limb_blocks; rewrite map_app; apply in_or_app;
          [right| left]; unfold mpd_blk; rewrite HO; left; cbn; symmetry; exact E. }
      assert (GONE1 : forall b, In b LBo' -> ~ In (fst b) (map fst owned)).
      { intros [B kk] Hb Hin0. cbn [fst] in Hin0. pose proof (proj1 (EOf B) Hin0) as Hin. cbn [fst map] in Hin.
        assert (ND1 : List.NoDup (map fst LBo)) by (rewrite map_app in NDL; exact (List.NoDup_app_remove_r _ _ NDL)).
        subst LBo'. destruct Hin as [E|Hin].
        * symmetry in E. revert E. eapply lb_remove_gone; [| exact Hb]. unfold rsa_free_LB. do 2 apply NoDup_lb_free_mpd. exact ND1.
        * apply lb_remove_sub in Hb. unfold rsa_free_LB in Hb. unfold rsa_limb_blocks in Hin. rewrite map_app in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin|Hin].
          -- unfold mpd_blk in Hin. destruct (md_own (r_N r)) eqn:HO; cbn in Hin; try tauto. destruct Hin as [E|[]].
             revert E. apply not_eq_sym. eapply lb_free_mpd_gone; [apply NoDup_lb_free_mpd; exact ND1| exact Hb| exact HO].
          -- unfold mpd_blk in Hin. destruct (md_own (r_E r)) eqn:HO; cbn in Hin; try tauto. destruct Hin as [E|[]].
             apply lb_free_mpd_sub in Hb. revert E. apply not_eq_sym. eapply lb_free_mpd_gone; [exact ND1| exact Hb| exact HO]. }
      eapply tail_walk with (LBo' := LBo') (owned := owned);
        first [ eassumption | reflexivity
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => unfold PHIpk; unfold RSA_FREE_WRAP_PHI, RSA_FREE_PHI, AVOL_CALL in *; clear - HV5; lia
                | |- hfr _ _ _ _ <= _ => unfold FFRpk; unfold RSA_FREE_WRAP_FR, RSA_FREE_FR, fr_charge in *; clear - HFR5 D0; lia
                end
              | match goal with |- ?gg => idtac "T1-LEFT:" gg end ].
    - (* [comment removed for export] *)
      pose proof (map_fst_iff _ _ EO) as EOf.
      assert (INFB : 991744 <= info <= 992000).
      { clear - EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. lia. }
      assert (INFAL : info mod 64 = 0).
      { clear - EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. destruct EI as [<-|[<-|[<-|[]]]]; reflexivity. }
      (* [comment removed for export] *)
      assert (OI : aobj asegs AL (hcs asegs R HIA h) m (info + 80) 8).
      { pose proof (hm_img_shadow asegs R HIA h _ LF m HH) as ISH. pose proof (hcs_img_cs R HIA h IMG (proj2 (proj2 (proj2 IMG')))) as ICS.
        clear - EI ISH ICS. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]]; (eapply aobj_img; [exact ICS| exact ISH| vm_compute; reflexivity]). }
      assert (TB : ro_cells asegs m (info + 80) [CB 8 [Z_to_bv 8 240; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
      { pose proof (RTC m (hm_rtc asegs R HIA h _ LF m HH)) as RT.
        clear - EI RT. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]];
          [ exact (asan_rtc_const m (991744 + 80) [Z_to_bv 8 240; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
          | exact (asan_rtc_const m (991872 + 80) [Z_to_bv 8 240; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
          | exact (asan_rtc_const m (992000 + 80) [Z_to_bv 8 240; Z_to_bv 8 34; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RT ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) ]. }
      clear EI.
      destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact CIN)) as (_ & _ & CCE & CIM).
      (* [comment removed for export] *)
      assert (NOL : forall a, In a (map fst ((ctx, 256) :: kp_blocks k)) -> ~ In a (map fst LB)).
      { intros a Ha. eapply NoDup_app_notin; [exact NDL|]. apply in_map_iff in Ha. ddestruct Ha as (b & <- & Hb).
        apply in_map_iff. exists b. split; [reflexivity| apply OWN; apply EO; exact Hb]. }
      assert (NOLd : forall dd, In dd (kp_mpds k) -> md_own dd = LHeap -> ~ In (md_p dd) (map fst LB)).
      { intros dd Hd HO. apply NOL. right. rewrite kp_blocks_eq. apply in_map_iff. exists (md_p dd, 4 * md_n dd). split; [reflexivity|].
        apply in_flat_map_mpd_blk; [exact Hd| exact HO]. }
      assert (LEQ : lb_remove ctx (kp_free_LB k (LBo ++ LB)) = lb_remove ctx (kp_free_LB k LBo) ++ LB).
      { unfold kp_free_LB, grp_free_LB. rewrite !lb_free_mpds_app. 1: apply lb_remove_app.
        - apply NOL. left. reflexivity.
        - intros dd Hd HO. apply NOLd; [first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]| exact HO].
        - intros dd Hd HO. apply NOLd; [first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]| exact HO]. }
      set (LBo' := lb_remove ctx (kp_free_LB k LBo)) in *.
      assert (SUBo : forall b, In b LBo' -> In b LBo).
      { intros b Hb. subst LBo'. apply lb_remove_sub in Hb. unfold kp_free_LB, grp_free_LB in Hb. do 2 apply lb_free_mpds_sub in Hb. exact Hb. }
      assert (SUB' : forall b, In b (LBo' ++ LB) -> In b (LBo ++ LB)) by (apply lb_sub_app; exact SUBo).
      assert (OCR : forall LBx SPx, (forall b, In b LB -> In b LBx) -> SPx <= bv_unsigned sp -> client_range L (LBx ++ fdata LF) SPx PKA 16).
      { intros LBx SPx HI HS a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]].
        - left. clear - Hs Ha SX HS. lia.
        - right; left. exact Hd.
        - right; right. exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI, Hb| right; exact Hb]. }
      assert (KEEP1 : forall b, In b LBo -> ~ In (fst b) (map fst owned) -> In b LBo').
      { intros [B kk] Hb Hn0. cbn [fst] in Hn0. assert (Hn : ~ In B (map fst ((ctx, 256) :: kp_blocks k))) by (intros X; exact (Hn0 (proj2 (EOf B) X))).
        cbn [map fst] in Hn. subst LBo'. apply In_lb_remove_keep; [| intros ->; apply Hn; left; reflexivity].
        unfold kp_free_LB, grp_free_LB. apply lb_free_mpds_keep; [apply lb_free_mpds_keep; [exact Hb|]|];
          intros dd Hd HO E; apply Hn; right; rewrite kp_blocks_eq; apply in_map_iff; exists (md_p dd, 4 * md_n dd); (split; [cbn; symmetry; exact E|]);
          (apply in_flat_map_mpd_blk; [| exact HO]); first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]. }
      assert (GONE1 : forall b, In b LBo' -> ~ In (fst b) (map fst owned)).
      { assert (ND1 : List.NoDup (map fst LBo)) by (rewrite map_app in NDL; exact (List.NoDup_app_remove_r _ _ NDL)).
        intros [B kk] Hb Hin0. cbn [fst] in Hin0. pose proof (proj1 (EOf B) Hin0) as Hin. cbn [fst map] in Hin. subst LBo'. destruct Hin as [E|Hin].
        * symmetry in E. revert E. eapply lb_remove_gone; [| exact Hb]. unfold kp_free_LB, grp_free_LB. do 2 apply NoDup_lb_free_mpds. exact ND1.
        * apply lb_remove_sub in Hb. rewrite kp_blocks_eq in Hin. apply in_map_iff in Hin. ddestruct Hin as (b & Eb & Hbk). cbn in Eb.
          destruct (flat_map_mpd_blk_inv _ _ Hbk) as (dd & Hd & HO & ->). cbn in Eb. subst B.
          unfold kp_free_LB, grp_free_LB in Hb. unfold kp_mpds in Hd. apply in_app_or in Hd. destruct Hd as [Hd|Hd].
          -- apply lb_free_mpds_sub in Hb.
             refine (lb_free_mpds_gone _ _ _ _ dd ND1 Hb _ HO eq_refl).
             destruct KP as (HG & _). eapply grp_heap_in_free; [exact HG| exact Hd| exact HO].
          -- refine (lb_free_mpds_gone _ _ _ _ dd _ Hb _ HO eq_refl); [apply NoDup_lb_free_mpds; exact ND1| exact Hd]. }
      apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (presW_sub_blocks asegs R HIA h (LBo ++ LB) (LBo' ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] m m
                    (presW_init asegs R HIA h (LBo ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] HH ltac:(clear; lia)) SUB') as PXA.
      pose proof (hm_wlow asegs R HIA h _ _ m HH) as WL.
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
      pose proof (conj MI I) as MIbox. pose proof (conj KP I) as KPbox. clear KP MIr.
      carve_frame 16%nat ST.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - POS PKB; lia); clear - K0 POS; lia|]. clear K0.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with HHx : HM _ _ _ h _ LF mx |- _ =>
          pose proof (abase_got _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GOT; pose proof (abase_gsb _ _ _ (hm_abase asegs R HIA h _ LF mx HHx)) as GSB; rewrite (proj1 IMG') in GOT end end.
      zstep. zstep. zstep. clear GOT GSB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KI; zify_cond KI; [exfalso; clear - KI INFB; rewrite ?unsigned_lit in KI by lia; lia|]. clear KI.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. try (if_cases KF; zify_cond KF; [exfalso; revert KF; clear; intros KF; rewrite ?unsigned_lit in KF by lia; cbn in KF; lia|]; clear KF).
      clear OI TB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      destruct MIbox as [MIm _]. destruct KPbox as [KP _].
      assert (KP1 : ecp_keypair_at asegs MT m1 (LBo ++ LB) ctx k).
      { eapply ecp_keypair_at_munch; [exact KP| exact MU0| exact WM0| exact MIm| assumption| cbn; clear - CCE ALO LOS; lia|].
        intros dd Hd O. ddestruct (mpdr_blk_factsA asegs L m (LBo ++ LB) ((LBo ++ LB) ++ LF) dd) as (_ & _ & I3 & I4 & _);
          [eapply kp_mpds_mpdr; [exact KP| exact Hd]| exact O| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| cbn; clear - I3 I4 ALO LOS; lia]. }
      clear MU0 WM0 MIm.
      (* [comment removed for export] *)
      zstep.
      pose proof ECW as SG. unfold eckey_free_wrap_stmtA, A_ECKEY_FREE_WRAP in SG.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply SG with (h := h) (LB := LBo ++ LB) (LF := LF) (A := ctx) (k := k) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by (clear - SPR SLO NEEDR LOS ALO ACP; lia); rewrite ?(unsigned_lit PKA) by (clear - PKB; lia);
          first [ exact HK1 | exact KP1 | exact CIN | exact APT | exact PNE | exact AL16 | exact CB256 | exact LOS | exact TP | reflexivity
                | lazymatch goal with
                  | |- HM _ _ _ h _ LF _ => assumption
                  | |- stk _ _ lo _ => assumption
                  | |- lo <= _ => clear - SLO NEEDR; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SPA; Z.div_mod_to_equations; lia
                  | |- mem_inv _ _ => assumption
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold PHIpk in BUD; unfold ECKEY_FREE_WRAP_PHI, KF_PHI, GF_PHI, AVOL_CALL in *; clear - BUD; lia
                  | |- uw_obj _ _ 1 d => eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRpk in BUDF; unfold ECKEY_FREE_WRAP_FR, KF_FR, GF_FR, fr_charge in *; clear - BUDF D0; lia
                  end
                | match goal with |- ?gg => idtac "EW-LEFT:" gg end ]. }
      cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m5 & mo5 & h5 & E & PO).
      injection E as -> ->.
      ddestruct PO as (MI5 & ST5 & MF5 & PX5 & HT5 & HS5 & HF5 & HK5 & HCS5 & HV5 & HFR5 & HH5).
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST5, PX5 by (clear - SPR SLO NEEDR LOS ALO ACP; lia).
      rewrite LEQ in HH5, PX5.
      replace (ret_pc (Z_to_bv 64 0xb17c0)) with (Z_to_bv 64 0xb17c0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -16) _ |- _ =>
        pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m5 _ _ PX5 FRx ltac:(apply client_range_stack; cbn; clear; lia) ltac:(exact I)) as FR5; clear FRx end.
      lazymatch goal with HPx : rw_cells _ m1 PKA _ |- _ =>
        pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m1 m5 _ _ PX5 HPx ltac:(apply OCR; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]) ltac:(exact I)) as HPKA5; clear HPx end.
      lazymatch goal with OBJx : aobj _ _ (hcs _ _ _ h) m1 PKA 16 |- _ =>
        pose proof (presA_aobj asegs R (hcs asegs R HIA h) _ _ _ _ _ _ m1 m5 PKA 16 CSOK PX5 OBJx ltac:(apply OCR; [intros b Hb; apply in_app_iff; right; exact Hb| clear; lia]) ltac:(clear - LOS SLO NEEDR; lia) ltac:(intros x Hx; eapply hcs_below_top; exact Hx)) as OBJ5; clear OBJx end.
      assert (PXA5 : presW asegs R HIA h (LBo' ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(PKA, PKA + 16)] m m5).
      { eapply presW_call; [exact PXA| exact PX5| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
      pose proof (HMND _ _ _ _ HH5) as NDL5.
      clear PXA PX5 SG KP1.
      repeat match goal with H : aobj _ _ _ m1 _ _ |- _ => clear H | H : stk _ m1 _ _ |- _ => clear H | H : mem_inv _ m1 |- _ => clear H | H : HM _ _ _ _ _ _ m1 |- _ => clear H
                           | H : ainv_laws _ _ |- _ => clear H | H : kinv_laws _ _ _ |- _ => clear H end.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h5 mo) _ _ mo5 (conj HK5 (mo_frame_trans _ _ _ MF1 MF5))).
      pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo) as KINV.
      zstep.
      replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in * by lia.
      eapply tail_walk with (LBo' := LBo') (owned := owned);
        first [ eassumption | reflexivity
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => unfold PHIpk; unfold ECKEY_FREE_WRAP_PHI, KF_PHI, GF_PHI, AVOL_CALL in *; clear - HV5; lia
                | |- hfr _ _ _ _ <= _ => unfold FFRpk; unfold ECKEY_FREE_WRAP_FR, KF_FR, GF_FR, fr_charge in *; clear - HFR5 D0; lia
                end
              | match goal with |- ?gg => idtac "T2-LEFT:" gg end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PKF.

(* [comment removed for export] *)
Lemma A_pk_free_spec : forall R (HIA : artA asegs R) MT,
  asan_img_ok (arl_AL R) -> (forall m, arl_rtc R m -> asan_rtc m) ->
  platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE ->
  rsa_free_wrap_stmtA asegs R HIA A_RSA_FREE_WRAP -> eckey_free_wrap_stmtA asegs R HIA MT A_ECKEY_FREE_WRAP ->
  0 <= arl_need_rt R -> 0 <= arl_need_amem R ->
  hl_img_lo (arl_L R) <= hl_data_lo (arl_L R) /\ hl_data_hi (arl_L R) <= hl_img_hi (arl_L R) ->
  (forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB)) ->
  pk_free_stmtA asegs R HIA (PKA_inst MT) PHIpk FFRpk (STKpk R) A_PK_FREE.
Proof. intros. eapply A_pk_free_walk; eauto. Qed.
