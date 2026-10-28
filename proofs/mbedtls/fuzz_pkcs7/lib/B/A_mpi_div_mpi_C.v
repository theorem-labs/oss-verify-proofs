(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_div_stmtA A_mpi_div_mpi_P.
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

Section WalkC.
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L45094400112.7600000JS2LF2ra2sp3LFB2FB1n2B01j1K". (* [comment removed for export] *)
  #[using="ra sp LFB"] Lemma fresh_apart_relist_m : forall h3 LB' m3 FB n,
    fresh_apart R LB LF FB n -> HM asegs R HIA h3 LB' ((FB, n) :: LF) m3 -> fresh_apart R LB' LF FB n.
  Proof.
    (intros h3 LB' m3 FB n dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros HH). split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B0 j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
    destruct (hm_apart asegs R HIA h3 _ _ _ HH) as [_ BA].
    pose proof (blocks_apart_app2 LB' ((FB, n) :: LF) (B0, j) (FB, n) BA Hb ltac:(left; reflexivity)) as K. cbn [fst snd] in K. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L15320239295.2L15353296831.5L24166965860.1L26892418956.1L37594587805.2L40281191306.3L59314955108.3L62018535662.1L978037823.5  00000600H00L00P00T00]00e00h019S1r2HRS1R3HIA1h4PHIb3HV0S2dXS2spS2dXS1R3HIA1hS1r2HR1ES1RS1R3HIA1h3FRb3HF0". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB NST XW W0BLK"] Lemma dv_EPI0 : forall (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (w0 w1 w2 : word) (r : Z)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s10v,
    bv_unsigned sp - 336 <= sp1 <= bv_unsigned sp - 320 -> sp1 mod 32 = 0 ->
    HM asegs R HIA h1 LB ((FB, 256) :: LF) m1 -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> hflag asegs R HIA h1 = hflag asegs R HIA h ->
    havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) ->
    FB mod 64 = 0 -> fresh_apart R LB LF FB 256 -> crange CS FB 256 -> (forall B0 j, In (B0, j) LF -> FB + 256 <= B0 \/ B0 + j <= FB) ->
    rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2] -> rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) DV_FSH ->
    rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp + -104) -> mem_inv asegs m1 ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1 ->
    mpd_at asegs m LB dX -> client_range L (LB ++ fdata LF) lo (md_addr dX) 16 -> mem_inv asegs m ->
    -2^31 < r < 0 -> 0 <= PHIb -> 0 <= FRb ->
    aevtA asegs (KF asegs R HIA h1 mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) s4v (Z_to_bv 64 (-8)) s6v s7v s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f93c) fc None m1 (seg_rom asegs)).
  Proof.
    intros until s10v. intros SP1 SP1M HH1 Ehcs ET1 ES1 EF1 EV1 EFR1 HKI F64 FRSH CFB APF FHD SHq SAVE STall MI1 PRES MX CRX MI0 HR HV0 HF0. rt_facts.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m _ PRES HCS1 ES1) as PRES1.
    pose proof (presW_init_at R HIA h1 _ _ LB LF m1 (bv_unsigned sp) (arl_stklo R) [] h HH1
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCS1 ES1 ltac:(clear; lia)) as PRES2.
    pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { eapply (A_mpi_div_mpi_P.epi_walk R HIA IMG NEEDR h LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LOS SLO TOP LFB) with (h3 := h1) (LBa := LB) (LBb := LB) (r := r) (WA := []) (WB := []) (m0 := m) (m2x := m1);
        first [ exact HH1 | exact HCS1 | exact PRES1 | exact PRES2 | exact FRSH | exact CFB | exact APF | exact STall | exact SAVE | exact FHD | exact SHq
              | exact ET1 | exact ES1 | exact SP1 | exact SP1M | exact F64 | exact MI1 | (intros b' Hb; exact Hb)
              | match goal with |- ?g => idtac "EPI0-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA.
    deexists 14. dexists m9, mo9, h4, LB, dX, r.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split.
    { pose proof (presW_presA asegs R HIA h1 _ LF _ _ _ _ _ PRES9) as HPF. rewrite ES1 in HPF.
      eapply presA_weaken; [exact HPF| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
    split; [rewrite E4top; exact ET1|]. split; [rewrite E4stk; exact ES1|]. split; [rewrite E4flag; exact EF1|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCS1 x Hx)|].
    split; [rewrite E4vol, EV1; clear - HV0; lia|].
    split; [rewrite E4fr, EFR1; clear - HF0; lia|].
    split; [exact HH4|].
    split.
    { pose proof MX as [(CX3 & _ & _ & _ & _ & OWN3) _].
      eapply (mpd_at_heap_presx asegs L) with (LBp := LB ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MX| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h1 _ LF _ _ _ _ _ PRES9))| exact MI0| exact MI9| | | exact I| intros _; exact I|].
      - eapply client_range_of_w. exact (proj1 XW).
      - intros EO. rewrite EO in OWN3. ddestruct OWN3 as (N1 & XIN & _). eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dX) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. ddestruct OWN3 as (_ & XIN & _). exact XIN. }
    split; [apply mpd_out_refl; exact NST|]. split; [intros b Hb; left; exact Hb|].
    split; [split; [split; [clear - HR; lia| intros E; exfalso; clear - HR E; lia]|]|].
    - split; [reflexivity|]. split; [reflexivity|]. split; [intros b Hb; left; exact Hb| clear; lia].
    - unfold div_mpi_nz. apply Z.le_max_l.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  (* [comment removed for export] *)
  Definition dv_sp (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 : word) : list cell := [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; C8 c104; C8 c112; C8 c120; C8 c128; C8 c136; C8 c144; C8 c152; C8 c160].
  (* [comment removed for export] *)
  Definition DCS (spc t2c zc czc : list cell) (gb : list byte) (z32 z48 z64 : list byte) (tpc : list cell) (jq : list byte) : list (Z * list cell) :=
    [(sp1, spc); (sp1 + 168, t2c); (sp1 + 184, zc); (sp1 + 200, czc); (sp1 + 216, [CB gapn gb]); (bv_unsigned sp + -104, SAVEL); (FB, [C8 w0; C8 w1; C8 w2]);
     (FB + 32, [CB 8 z32]); (FB + 48, [CB 8 z48]); (FB + 64, [CB 8 z64]); (FB + 176, tpc); (FB + 188, [CB 4 jq])].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L11421004839.8L123035966.5  L12620360201.5L16313239463.8L2163886857.5 L22937440672.1L26773224885.5L26892418956.1L41155479456.1L51046083488.2L55798526857.1L62018535662.1L7007546227.2 00000J00]00i01C01O01T01`01d01i02102502802<S1R3HIA1h3FRb2hq1f2HF4HFRqS2sp2lo3sp13SP13LOCS2lo3sp13LOCS1R3HIA1h4PHIb2hq1v2HV3HVqS2lo3sp13LOCS3sp1S2lo3sp13LOCS2spS3sp1S2sp3sp1S2dWS1RS2dW". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M XW SP1 SP1M GAP F64 FRSH CFB APF LOC"] Lemma dv_EPIK : forall mq hq LBq dW v f (r : Z) spc t2c zc czc gb z32 z48 z64 tpc jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s10v,
    CSTA mq hq LBq [] dW (DCS spc t2c zc czc gb z32 z48 z64 tpc jq) DV_FSH v f ->
    cells_size spc = 168%nat -> cells_size t2c = 16%nat -> cells_size zc = 16%nat -> cells_size czc = 16%nat ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v <= PHIb -> f <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) s4v (Z_to_bv 64 (-8)) s6v s7v s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f93c) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST SZ1 SZ2 SZ3 SZ4 HR HRB HSZ HV HF. rt_facts.
    assert (NUL : Forall (fun dl : mpd => md_own dl = LNull) []) by apply Forall_nil.
    destruct (A_mpi_client2.cs_final asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST NUL)
      as (HHq & HTq & HSq & HFq & HCSq & HVq & HFRq & MWq & OUTq & BKq & FRWq & PXq & MIq & STq & CHq & SHq).
    unfold DCS in CHq.
    apply Forall_cons_iff in CHq. destruct CHq as [SPC CHq]. apply Forall_cons_iff in CHq. destruct CHq as [T2C CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [ZC CHq]. apply Forall_cons_iff in CHq. destruct CHq as [CZC CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [GAPC CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [SAVE CHq]. apply Forall_cons_iff in CHq. destruct CHq as [FHD _].
    cbn [fst snd] in SPC, T2C, ZC, CZC, GAPC, SAVE, FHD.
    assert (STall : stk asegs mq lo (bv_unsigned sp + -104)).
    { pose proof (stk_of_rw_cells asegs mq _ _ SPC) as K1. rewrite SZ1 in K1. change (Z.of_nat 168) with 168 in K1.
      pose proof (stk_of_rw_cells asegs mq _ _ T2C) as K2. rewrite SZ2 in K2. change (Z.of_nat 16) with 16 in K2.
      pose proof (stk_of_rw_cells asegs mq _ _ ZC) as K3. rewrite SZ3 in K3. change (Z.of_nat 16) with 16 in K3.
      pose proof (stk_of_rw_cells asegs mq _ _ CZC) as K5. rewrite SZ4 in K5. change (Z.of_nat 16) with 16 in K5.
      pose proof (stk_of_rw_cells asegs mq _ _ GAPC) as K4. cbn [cells_size csize Nat.add] in K4. rewrite Nat.add_0_r, GAP in K4.
      replace (sp1 + 168 + 16) with (sp1 + 184) in K2 by (clear; lia). replace (sp1 + 184 + 16) with (sp1 + 200) in K3 by (clear; lia).
      replace (sp1 + 200 + 16) with (sp1 + 216) in K5 by (clear; lia).
      replace (sp1 + 216 + (bv_unsigned sp + -104 - (sp1 + 216))) with (bv_unsigned sp + -104) in K4 by (clear; lia).
      eapply (stk_merge asegs); [| exact K4| clear - SP1 LOC; lia]. eapply (stk_merge asegs); [| exact K5| clear - SP1 LOC; lia].
      eapply (stk_merge asegs); [| exact K3| clear - SP1 LOC; lia].
      eapply (stk_merge asegs); [| exact K2| clear - SP1 LOC; lia]. eapply (stk_merge asegs); [exact STq| exact K1| clear - SP1 LOC; lia]. }
    pose proof (fresh_apart_relist_m hq LBq mq FB 256 FRSH HHq) as FRSH3.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] H0M ltac:(clear; lia)) as PRES0.
    pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF _ _ _ m m PRES0 ltac:(intros b' Hb; eapply In_mpd_keep; exact Hb)) as (_ & C1 & C2 & C3).
    assert (PRESb : presW asegs R HIA h (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) [(md_addr dX, md_addr dX + 16)] m mq)
      by (split; [exact PXq| split; [exact C1| split; [exact C2| exact C3]]]).
    pose proof (presW_hmono R HIA h hq (mpd_keep LB dX) LF _ _ _ m _ PRESb HCSq HSq) as PRESb3.
    pose proof (presW_init_at R HIA hq _ _ LBq LF mq (bv_unsigned sp) (arl_stklo R) [] h HHq
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSq HSq ltac:(clear; lia)) as PRES2.
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply (A_mpi_div_mpi_P.epi_walk R HIA IMG NEEDR h LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LOS SLO TOP LFB) with (h3 := hq) (LBa := mpd_keep LB dX) (LBb := LBq) (r := r) (WA := [(md_addr dX, md_addr dX + 16)]) (WB := []) (m0 := m) (m2x := mq);
        first [ exact HHq | exact HCSq | exact PRESb3 | exact PRES2 | exact FRSH3 | exact CFB | exact APF | exact STall | exact SAVE | exact FHD | exact SHq
              | exact HTq | exact HSq | exact SP1 | exact SP1M | exact F64 | exact STq | exact MIq
              | lazymatch goal with
                | |- fresh_apart _ (mpd_keep LB dX) LF FB 256 => apply fresh_apart_keep; exact FRSH
                | |- forall b', In b' (mpd_keep LB dX) -> In b' LBq => intros b' Hb; eapply mpd_keep_out; [exact OUTq| exact Hb]
                end
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA.
    deexists 14. dexists m9, mo9, h4, LBq, dW, r.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES9) as HPF; rewrite HSq in HPF; exact HPF|].
    split; [rewrite E4top; exact HTq|]. split; [rewrite E4stk; exact HSq|]. split; [rewrite E4flag; exact HFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; clear - HVq HV; lia|].
    split; [rewrite E4fr; clear - HFRq HF; lia|].
    split; [exact HH4|].
    dpose OUTq as (OU1 & OU2 & OU3 & OU4 & OU5).
    split.
    { pose proof MWq as [(CX3 & _ & _ & _ & _ & OWN3) _].
      eapply (mpd_at_heap_presx asegs L) with (LBp := LBq ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MWq| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29))| exact MIq| exact MI9| | | exact I| intros _; exact I|].
      - rewrite OU1. eapply client_range_temp; [eapply client_range_of_w; eapply mpd_writableA_keep; exact XW| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUTq| exact Hb]| right; exact Hb].
      - intros EO. rewrite EO in OWN3. ddestruct OWN3 as (N1 & XIN & _). eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dW) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. ddestruct OWN3 as (_ & XIN & _). exact XIN. }
    split; [exact OUTq|]. split; [exact FRWq|].
    split; [split; [split; [exact HR| exact HRB]| exact BKq]|].
    exact HSZ.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L24543956951.94L25499688259.94L5231112239.94 L55937250651.9400000Y01B01k02TS2LF2ra2sp3LFB2FB3sp14gapn2A01n1k1x2Hx2L1S2LF2ra2sp3LFB2FB3sp14gapn2A01n1k1a2Ha2L1S2LF2ra2sp3LFB2FB3sp14gapn2A01n1k1x2Hx2L1S2LF2ra2sp3LFB2FB3sp14gapn2A01n1k1a2Ha2L1". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma aobj_merge_dv : forall (CSx : Z -> Prop) mx A0 n k, 0 <= n -> 0 <= k ->
    aobj asegs AL CSx mx A0 n -> aobj asegs AL CSx mx (A0 + n) k -> aobj asegs AL CSx mx A0 (n + k).
  Proof.
    intros CSx mx A0 n k Hn Hk [C1 S1] [C2 S2]. split.
    - intros x Hx. destruct (Z_lt_le_dec x (A0 + n)) as [L1|L1]; [apply C1; lia| apply C2; lia].
    - intros a Ha. destruct (Z_lt_le_dec a (A0 + n)) as [L1|L1]; [apply S1; lia| apply S2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L10764937445.14 L11553410088.1  L13157033923.1  L14861536540.14 L17092503979.1  L18788269472.1  L20964124776.1  L2408537193.19  L27650499371.1  L28187807723.14 L29162521377.0  L31744184555.14 L32269442061.5  L32596543859.5  L33595343993.6  L3480250179.19  L34915349256.1  L35663928186.7  L36520337934.1  L36525207280.19 L37558967096.14 L38235734261.1  L38264889751.1  L38551529394.0  L39268637205.0  L39332637397.0  L39513730120.1  L42091889404.6  L44628305607.14 L47410864422.1  L48161827075.1  L487318866.2    L49508988902.1  L50794195360.5  L51725509627.1  L52806978339.3  L53463048683.14 L53873674960.19 L55879915635.5  L56654045851.19 L58782645332.1  L60098763854.3  L61968151637.1  L62018535662.1  L6203936179.1   L66151427842.16 L68664817267.5  L6961803708.6   L9080220944.4   L9356559676.11  L9631767084.2   Q15022709143.184Q45989664010.223Q58026207754.184Q67304644247.22300000^00b00f01L01P01T01X02I02M03;03<03j04;04L04M05>05?05T05X06D06M06Q06U06V06W06X06Y06Z06c06g06k07107507F07J07T08B08M08^09[09_09i09m0:00:50:O0:`0:a0;00;[0;b0<L0=30=Z0>DS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S2FBS2FBS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F02F14NRAmS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1SS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2sp3sp14gapn3SP1S2sp3sp14gapn3SP1FS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP14SP1M3ALO2F02F1FS1R3HIA1h2sp2lo3TOP1HS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F02F1S2FB4gapnS2loS2FBSSSFFS2FB4gapnS2FBS2FBS1i2HiS2FBS2sp3sp14gapn3SP1S2FBS1R3HIA2hqS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FB3sp12F0S2sp3sp14gapn3SP1S1R3HIA5NEEDR1h2sp2lo3LOS3SLO3TOP2FB3sp13SP12hq3ALO3HTq2F02F1S2FBS1R2lo3LOSS2FBS1RS3sp1S2FB2r03F641q1r1H2H02q02H4S2sp3sp14gapn3GAPFS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2FB2F0S2LF2sp2lo3LFB3sp14gapn3SP13t2c2zc3SZ23SZ3S2LF2lo3LFB3sp14gapn3LOC3t2c2zc3SZ23SZ3S2LF2lo3LFB3sp14gapn3LOC3t2c2zc3SZ23SZ3S2LF2sp2lo3LFB3sp14gapn3SP13t2c2zc3SZ23SZ3". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ"] Lemma dv_PZ : forall mq hq LBq dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 (u0 u1 u2 : word) jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s10v,
    CSTA mq hq LBq [] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160) t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f ->
    cells_size t2c = 16%nat -> cells_size zc = 16%nat -> cells_size czc = 16%nat ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v <= PHIb -> f <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) s4v (Z_to_bv 64 (-8)) s6v s7v s8v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f930) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST SZ2 SZ3 SZ4 HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    unfold DCS in CHq.
    apply Forall_cons_iff in CHq. destruct CHq as [SPC CHq]. apply Forall_cons_iff in CHq. destruct CHq as [T2C CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [ZC CHq]. apply Forall_cons_iff in CHq. destruct CHq as [CZC CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [GAPC CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [SAVE CHq]. apply Forall_cons_iff in CHq. destruct CHq as [FHD CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [Z32C CHq]. apply Forall_cons_iff in CHq. destruct CHq as [Z48C CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [Z64C CHq].
    apply Forall_cons_iff in CHq. destruct CHq as [TPC CHq]. apply Forall_cons_iff in CHq. destruct CHq as [TPQ _].
    cbn [fst snd] in SPC, T2C, ZC, CZC, GAPC, SAVE, FHD, Z32C, Z48C, Z64C, TPC, TPQ. unfold dv_sp in SPC.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    assert (TPB : rw_cells asegs mq (FB + 176) [CB 12 (le4 u0 ++ le4 u1 ++ le4 u2)]).
    { eapply rw_cells_reshape; [exact TPC| |].
      - cbn -[le4]. repeat split; try (rewrite ?length_app, !length_le4; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc, ?app_nil_r. reflexivity. }
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 176) 12) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    assert (OTP : aobj asegs AL (hcs asegs R HIA hq) mq (FB + 176) 12).
    { replace 12 with (8 + 4) by reflexivity. apply aobj_merge_dv; [clear; lia| clear; lia| |].
      - eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 176) 22 1 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| reflexivity|].
        intros i Hi. assert (i = 0%nat) as -> by (clear - Hi; lia). reflexivity.
      - eapply (A_mpi_add_int.aobj_of_partial_shadow_sh asegs AL (hcs asegs R HIA hq) mq FB DV_FSH (FB + 176 + 8) 23 4 CSOKq SHq); [eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| clear; lia| clear; lia| reflexivity]. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ.
      eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (A := FB + 176) (n := 12) (lo := lo) (junk := le4 u0 ++ le4 u1 ++ le4 u2);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
      all: try (pose proof (arl_need_rt_amem R) as NRAm; clear - F0 F1 ALO LOS SLO SP1 NEEDR SP1M HTq TOP NRAm; lia).
      all: match goal with |- ?g => idtac "PZ-PRE-LEFT:" g end. }
    cbv beta. intros ms' PO. unfold platform_zeroize_postA in PO. destruct_exs PO.
    rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
    ddestruct PO as (-> & MU2 & WM2 & MI2 & TPZ & ST2 & HH2).
    lazymatch goal with |- aevtA _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ ?mx _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr : word) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]); rename mx into m2 end.
    (* [comment removed for export] *)
    set (CS7 := [(sp1, dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160); (sp1 + 168, t2c); (sp1 + 184, zc); (sp1 + 200, czc); (sp1 + 216, [CB gapn gb]); (bv_unsigned sp + -104, SAVEL);
                 (FB, [C8 w0; C8 w1; C8 w2]); (FB + 32, [CB 8 z32]); (FB + 48, [CB 8 z48]); (FB + 64, [CB 8 z64]); (FB + 188, [CB 4 jq])]).
    assert (OK7 : forall tpc', cells_size tpc' = 12%nat -> Forall (A_mpi_client2.chunk_okA (bv_unsigned sp) sp1 FB 256 []) (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160) t2c zc czc gb z32 z48 z64 tpc' jq)).
    { intros tpc' SZT. unfold DCS, A_mpi_client2.chunk_okA, dv_sp.
      repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; rewrite ?SZ2, ?SZ3, ?SZ4, ?SZT; split; [| intros d' []]|]); [ | | | | | | | | | | | | apply Forall_nil].
      all: try (left; clear - SP1 GAP; lia). all: try (right; left; clear; lia). all: try (right; right; clear; lia). }
    assert (CSTa : CSTA mq hq LBq [] dW CS7 DV_FSH v f).
    { eapply (A_mpi_client2.cs_set_cells asegs R HIA) with (CS := DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160) t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq); [exact CST| |].
      - subst CS7. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - pose proof (OK7 [C4 u0; C4 u1; C4 u2] eq_refl) as K. unfold DCS in K. subst CS7.
        repeat (apply Forall_cons_iff in K; destruct K as [?K K]). repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
    replace (FB + 176 + 12) with (FB + 188) in MU2 by (clear; lia).
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 176, FB + 188)] mq m2).
    { eapply (presA_drop_below asegs R HIA hq LBq LF1 _ lo sp1 mq mq m2 sp1 HHq); [| clear; lia| exact LOS].
      eapply (presA_weaken asegs R LBq LBq LF1 LF1 sp1 sp1 (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA hq) (hstkhi asegs R HIA hq) [(FB + 176, FB + 188); (lo, sp1)] [(lo, sp1); (FB + 176, FB + 188)]);
        [| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| cbn [outside]; clear; intros y Hy; tauto].
      eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HHq| | exact Hc]; clear; lia| exact MU2| exact WM2].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]|].
      apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSq| clear; lia| clear - SP1; lia]| apply Forall_nil]. }
    assert (CSTb : CSTA m2 hq LBq [] dW CS7 DV_FSH v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(FB + 176, FB + 188)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. split; [right; clear; lia| intros d' []].
      - subst CS7. unfold dv_sp. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; rewrite ?SZ2, ?SZ3, ?SZ4; split; [| exact I]|]); [ | | | | | | | | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CSTb) as (CHb & _).
    subst CS7. repeat (apply Forall_cons_iff in CHb; destruct CHb as [?K CHb]). cbn [fst snd] in *.
    assert (CSTc : CSTA m2 hq LBq [] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160) t2c zc czc gb z32 z48 z64 [CB 12 (repeat (Z_to_bv 8 0) 12)] jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_set_cells asegs R HIA) with (mq := m2); try eassumption.
      - unfold DCS. repeat (apply Forall_cons; [cbn [fst snd]; first [assumption | exact TPZ]|]). apply Forall_nil.
      - exact (OK7 [CB 12 (repeat (Z_to_bv 8 0) 12)] eq_refl). }
    unfold dv_sp in *.
    (* [comment removed for export] *)
    clear MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    eapply (dv_EPIK m2 hq LBq dW v f r) with (tpc := [CB 12 (repeat (Z_to_bv 8 0) 12)]); [exact CSTc| reflexivity| exact SZ2| exact SZ3| exact SZ4| exact HR| exact HRB| exact HSZ| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation SH4 := (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)).
  Local Notation DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 tpc jq := (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 (Z_to_bv 64 (FB + 176)) c152 c160) t2c zc czc gb z32 z48 z64 tpc jq).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00W0@D12596279903.181D12596279903.182D49412573216.182D58165489299.181L11727838551.1  L11879002598.1  L12469921329.0  L14424556008.1  L16025859627.14 L1685717371.0   L18421991047.14 L25190023391.177L25333246874.177L28013770460.14 L33162376934.1  L37753112363.14 L41311586347.14 L44314625912.14 L47277099470.177L52978356238.1  L58748427563.1  L59585116965.14 L61366595865.177L62018535662.1  L62383522360.14 Q11801279589.181Q11801279589.182Q17064285623.178Q37327240849.181Q49413559012.181Q49415575780.182Q49698585326.180Q52744951088.181Q52747231024.182Q58368740407.179Q58694915926.179Q58748148646.178Q64772098048.178Q9391256593.178 00000h01`02X03P03T03X03Y03]04K04L04U05>05g06M06Q07?07m08608_08c08g09U0:>0:A0:J0;80;f0<E0=30=a0>O0?70?e0@S0A80A]0B<0B[0C:S2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2FBS2FBFS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1SS2FB4gapnS2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ3S2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ3S1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FB4gapnS2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ3S2FBS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn3t2c2zc3SZ23SZ3S1RS2FB4gapnS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32F02HBS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ32F02HBS2LF3LFB2FB4gapn3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn3t2c2zc3SZ23SZ3". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB DIMG H0M XW W0AS SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ"] Lemma dv_TAIL_T : forall mq hq LBq dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 (u0 u1 u2 : word) jq (tp0 ts0 tn0 : Z) (tpad : word)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s8v s10v,
    CSTA mq hq LBq [] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f ->
    rw_cells asegs mq (FB + 144) [C8 (Z_to_bv 64 tp0); C2 (Z_to_bv 64 ts0); C2 (Z_to_bv 64 tn0); C4 tpad] ->
    cells_size t2c = 16%nat -> cells_size zc = 16%nat -> cells_size czc = 16%nat ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v <= PHIb -> f <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) s7v s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f928) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST TC SZ2 SZ3 SZ4 HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 144) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (TC' : rw_cells asegs mq (FB + 144) [C8 (Z_to_bv 64 tp0); CB 4 (le2 (Z_to_bv 64 ts0) ++ le2 (Z_to_bv 64 tn0)); C4 tpad]).
    { eapply rw_cells_reshape; [exact TC| |].
      - cbn -[le2]. repeat split; try (rewrite ?length_app, !length_le2; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc. reflexivity. }
    clear TC.
    pose proof (munch_refl [(FB + 144, FB + 160)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 144, FB + 160)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq [] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(FB + 144, FB + 160)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. split; [right; clear; lia| intros d' []].
      - unfold DCS, dv_sp. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; rewrite ?SZ2, ?SZ3, ?SZ4; split; [| exact I]|]); [ | | | | | | | | | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    eapply (dv_PZ m2 hq LBq dW v f r); [exact CST2| exact SZ2| exact SZ3| exact SZ4| exact HR| exact HRB| exact HSZ| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.
  Local Notation UWCD mq := (uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0@L11879002598.1  L12193668186.3  L12422032636.1  L13843160408.3  L14424556008.1  L18364504529.4  L23142903418.194L2405434805.3   L2406438837.30  L27686805496.2  L3482348703.30  L3483319967.1   L35663928186.7  L37624261558.229L37667476202.6  L38327628946.30 L39172636981.0  L39261862547.30 L40889598521.3  L46495921149.30 L46497395674.1  L5376886168.5   L56641043079.4  L56643561799.30 L59308972243.3  L60098763854.3  L61366595865.187L6203936179.1   L67337568515.3  L67574615286.187L67574694761.193L67576760568.2  L9356559676.11  Q17064285623.189Q57175321612.197Q58748148646.189Q68710687261.19700000400?00C00N00R00S01?01@01U01]01g01h02=02i03<03a03b04D04E04U04V04e04f05E05O05Y06E06J06W06X07H07P08;08]09?09a0:CS2FBS2FB2dT3BFTS2dTS4PHIb1v2HVS2FBFS2LF2ra2sp3LFB2FB3sp14gapn2dT3t2c2zc3SZ23SZ3FS1R2sp2lo3SLO3sp13SP1S2dT3NRTS3sp14SP1MFS1R3HIA1h2sp2lo3TOP1HS2LF2ra2sp3LFB2FB3sp14gapn2dT3t2c2zc3SZ23SZ3S1R2dT3ACV2P02PC2N1S1R3HIA1h1d3FRb3sp14BUDF2hq1f2HF4HFRqSS1R3HIA1h4PHIb3sp13BUD2hq1v2HV3HVqFS3sp12dT3NRT3NT1FS1d3FRb2D01f2HFFS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS2dT2KZ2P0S1R2lo3LOSS2LF2ra2sp3LFB2FB3sp14gapn2dT3t2c2zc3SZ23SZ3S3sp1S2dT4LENT3NT1FS2LF2ra2sp3LFB2FB3sp14gapn2dT3t2c2zc3SZ23SZ33NRTS2dT3NRTS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF3LFB2FB4gapn2dT3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn2dT3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn2dT3t2c2zc3SZ23SZ3S2LF3LFB2FB4gapn2dT3t2c2zc3SZ23SZ3". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_CLEAN_T : forall mq hq LBq dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 (u0 u1 u2 : word) jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s8v s10v,
    CSTA mq hq LBq [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dT = FB + 144 ->
    cells_size t2c = 16%nat -> cells_size zc = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + AVOL_CALL <= PHIb -> f + fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 1) s7v s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f914) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAD SZ2 SZ3 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dT) as (MT & NST' & _ & _ & _ & _ & HFT & _); try eassumption; [reflexivity|].
    pose proof MT as [(CT & _ & _ & LENT & NRT & OWNT) SGT]. rewrite EAD in CT. unfold mpi_cells in CT. unfold MPI_MAX_LIMBS in NRT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dT = LNull).
      { destruct (md_own dT) eqn:EOT; [reflexivity| | exfalso; exact (NST' eq_refl)]. exfalso.
        ddestruct (HFT eq_refl) as (P0 & PC & _ & N1 & _). rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      assert (CST0 : CSTA mq hq LBq [] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
      { change (@nil mpd) with (remove_nth 0 [dT]).
        eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dT); try eassumption; reflexivity. }
      eapply (dv_TAIL_T mq hq LBq dW v f r); [exact CST0| exact CT| exact SZ2| exact SZ3| exact SZ4| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in HV. clear - HV. lia.
      + unfold fr_charge in HF. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dT = LHeap).
      { destruct (md_own dT) eqn:EOT; [exfalso; destruct OWNT as [EP _]; apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NST' eq_refl)]. }
      rewrite EO in OWNT. ddestruct OWNT as (NT1 & INT & PAL & ARRT).
      ddestruct (HFT EO) as (P0 & PC & _ & _ & BFT & _).
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dT))) with (Z_to_bv 64 (md_n dT))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRT; lia); rewrite Z.mod_small by (clear - NRT; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dT))%nat with (Z.to_nat (4 * md_n dT)) in ZCH by (clear - LENT NT1; lia).
      pose proof (conj CT I) as CTb. clear CT.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dT) (len := 4 * md_n dT) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dT));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold fr_charge in *; unfold AVOL_CALL in *;
             clear - NRT NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      destruct CTb as [CT _].
      assert (CT4 : rw_cells asegs m4 (FB + 144) [C8 (Z_to_bv 64 (md_p dT)); C2 (Z_to_bv 64 (md_sg dT)); C2 (Z_to_bv 64 (md_n dT)); C4 (md_pad dT)]).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact CT| | ].
        - cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16. eapply (client_range_block (arl_L R) _ _ _ _ (FB + 32) 216); [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia].
        - cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 16) with 16. split; [clear - BFT; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dT) LBq) [] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zc czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change (@nil mpd) with (remove_nth 0 [dT]).
        eapply (A_mpi_client2.cs_drop asegs R HIA) with (i := 0%nat) (d := dT) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (dv_TAIL_T m4 h4 _ dW _ _ r); [exact CST4| exact CT4| exact SZ2| exact SZ3| exact SZ4| exact HR| exact HRB| exact HSZ| exact HV| exact HF].
    all: match goal with |- ?g => idtac "CLEANT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma uwc_raise_dv : forall mx LO' TOP' vv F0' F1' dd, uwc asegs mx LO' TOP' vv F0' dd -> F1' + 16 <= vv -> uwc asegs mx LO' TOP' vv F1' dd.
  Proof.
    intros mx LO' TOP' vv F0' F1' dd HU HF. inversion HU; subst; [apply uwc_stop; assumption| eapply uwc_link; eassumption| apply uwc_cap; assumption].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@D1100763746.189 D1100763746.190 D58960229810.190D60744044777.189L12469921329.0  L13157033923.1  L13483787457.1  L14202940435.3  L1512969377.8   L15828247874.6  L158508144.13   L1685717371.0   L18754192755.11 L18754192755.13 L21112221608.6  L21618476121.6  L26496199141.3  L28631320926.13 L29131270687.6  L30142377448.6  L30790725235.13 L32269442061.5  L32596543859.5  L33595343993.6  L33695652639.6  L34915349256.1  L34969210063.14 L35663928186.7  L38183441766.6  L38515102159.14 L39513730120.1  L40206404204.14 L416349868.14   L41753535948.6  L42091889404.6  L44107246460.185L45346338532.13 L45486317454.7  L46839732335.185L46875643032.14 L48161827075.1  L50794195360.5  L51005809078.7  L52101693566.6  L54869881971.13 L55879915635.5  L55990716303.185L56386624752.185L60098763854.3  L60246552271.14 L61968151637.1  L62018535662.1  L62037211595.7  L63994780891.14 L66002853406.13 L68664817267.5  L6961803708.6   L7181165107.4   L7872928577.14  L8931608776.1   L9356559676.11  L9366540546.10  Q11801279589.189Q11801279589.190Q24471895157.187Q25513505925.189Q26130604464.189Q39085863854.187Q44994836908.186Q46493710897.186Q48084872841.190Q49472925079.186Q49698585326.188Q51003780618.186Q60133849205.189Q64315378647.19000000a01R02C03403503903>03J03i03j04X04Y05B06006106:06F06O06P06Q07?07P07a07b07c07d07n08C08D08N08O09=09k09l09m0:O0;50;M0;o0<@0<D0<U0=00=B0>00>A0>c0?E0?O0?Y0?]0?`0@;0@i0A20AC0AD0AS0A]0Ab0BM0C40C\0DD0De0EW0FF0Fg0GG0Gj0Hl0IO0J10JQ0K@0LLS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stFS2FBS3sp1S2sp3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP1FS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1SS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1FS2FB4gapnS2sp3sp13SP1S2FB4gapnFFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2sp3sp14gapn3SP1S2sp3sp14gapn3SP1FFFS3sp14gapnS1R3HIA1h2sp2lo3TOP1HFS3sp14gapnFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1FFS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S1R3HIA1h2sp3TOP3sp13SP1S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2sp3sp14gapn3SP1S2FBS2sp3sp14gapn3SP1S1R5NEEDR2sp2lo3SLO3sp13SP1S1R3HIA1h3sp11a2HaS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2sp3sp14gapn3SP1S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S1R2lo3LOSS3sp14gapnS2FBS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FB4gapnS2sp3sp14gapn3GAPFS2sp2lo3sp13SP1S3sp14gapnS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF3LFB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3t2c3SZ24SP1R2HBS2LF2sp2lo3LFB3sp14gapn3SP13t2c3SZ22HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOC3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB3sp14gapn3t2c3SZ24SP1R2HBS2LF2lo3LFB3sp14gapn3LOC3t2c3SZ2S2LF2sp2lo3LFB3sp14gapn3SP13t2c3SZ2S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp14gapn3SP13t2c3SZ22HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP13t2c3SZ2S2LF3LFB3sp14gapn3t2c3SZ22HB5Ha_stS2LF2lo3LFB3sp14gapn3LOC3t2c3SZ2S2LF2lo3LFB3sp14gapn3LOC3t2c3SZ22HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3TOP3LFB3sp14gapn3GAP2hq3t2c3SZ23HTq3HSq5HTOPq2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_TAIL_Z : forall mq hq LBq dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq (tp0 ts0 tn0 : Z) (tpad : word)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s7v s8v s10v,
    CSTA mq hq LBq [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dT = FB + 144 ->
    rw_cells asegs mq (sp1 + 184) [C8 (Z_to_bv 64 tp0); C2 (Z_to_bv 64 ts0); C2 (Z_to_bv 64 tn0); C4 tpad] ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + AVOL_CALL <= PHIb -> f + fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) s6v s7v s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f908) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAD TC SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (hcs_stack asegs R HIA hq) as SCS0q. pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (sp1 + 184) 16) by (apply client_wrange_stack; [clear - SP1 SLO LOS NEEDR; lia| rewrite HTq; clear - SP1 TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (TC' : rw_cells asegs mq (sp1 + 184) [C8 (Z_to_bv 64 tp0); CB 4 (le2 (Z_to_bv 64 ts0) ++ le2 (Z_to_bv 64 tn0)); C4 tpad]).
    { eapply rw_cells_reshape; [exact TC| |].
      - cbn -[le2]. repeat split; try (rewrite ?length_app, !length_le2; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc. reflexivity. }
    clear TC.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl [(sp1 + 184, sp1 + 200)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(sp1 + 184, sp1 + 200)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCSq| clear - SP1 SLO NEEDR; lia| clear - SP1; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(sp1 + 184, sp1 + 200)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. split; [left; clear - SP1; lia| intros d' [<-|[]]; right; rewrite EAD; clear - F1 ALO LOS SLO SP1 NEEDR; lia].
      - unfold DCS, dv_sp. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; rewrite ?SZ2, ?SZ4; split; [| exact I]|]); [ | | | | | | | | | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    assert (UW2 : UWCD m2).
    { eapply uwc_floor with (F := sp1 + 200); [| clear; lia].
      eapply uwc_munch; [eapply uwc_raise_dv; [exact UW| clear - SP1; lia]| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I]. }
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST2) as (CH2 & _).
    unfold DCS in CH2. repeat (apply Forall_cons_iff in CH2; destruct CH2 as [?K CH2]). cbn [fst snd] in *.
    match goal with ZN : rw_cells asegs m2 (sp1 + 184) ?zcn |- _ => lazymatch zcn with _ :: _ => idtac end;
      assert (CST3 : CSTA m2 hq LBq [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c zcn czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f);
      [ eapply (A_mpi_client2.cs_set_cells asegs R HIA) with (mq := m2); try eassumption;
        [ unfold DCS; repeat (apply Forall_cons; [cbn [fst snd]; first [assumption | exact ZN]|]); apply Forall_nil
        | unfold DCS, dv_sp, A_mpi_client2.chunk_okA;
          repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; rewrite ?SZ2, ?SZ4; split; [| intros d' [<-|[]]; rewrite EAD]|]); [ | | | | | | | | | | | | | | | | | | | | | | | | apply Forall_nil];
          first [ left; clear - SP1 GAP; lia | right; left; clear; lia | right; right; clear; lia | right; clear - F1 ALO LOS SLO SP1 NEEDR GAP; lia | left; clear; lia ] ]
      | eapply (dv_CLEAN_T m2 hq LBq dT dW v f r) with (zc := zcn); [exact CST3| exact EAD| exact SZ2| reflexivity| exact SZ4| exact UW2| exact HR| exact HRB| exact HSZ| exact HV| exact HF] ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L56765667309.102L6667563486.102 00000]01LS2LF2ra2sp3LFB2FB3sp14gapn4TOPx2Fx2HF2HT1a2HaS2LF2ra2sp3LFB2FB3sp14gapn3SPx4TOPx2Fx3HSP1a2Ha". (* [comment removed for export] *)
  #[using="LF ra sp LFB FB sp1 gapn"] Lemma uwc_presA_dv : forall LBx LFx SPx SSPx TOPx Wx mx mx' vv Fx dd,
    presA asegs R LBx LFx SPx SSPx TOPx Wx mx mx' -> uwc asegs mx (arl_stklo R) TOPx vv Fx dd -> SPx <= Fx ->
    (forall a, Fx <= a < TOPx -> outside Wx a) -> 0 <= Fx -> TOPx <= 2^64 -> uwc asegs mx' (arl_stklo R) TOPx vv Fx dd.
  Proof.
    intros LBx LFx SPx SSPx TOPx Wx mx mx' vv Fx dd [P _] UW HSP HW HF HT.
    eapply uwc_transport; [exact UW|]. intros a Ha. apply (proj1 (P a ltac:(lia) ltac:(left; lia) (HW a Ha))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@L12235790964.3  L16227185990.1  L16813669302.230L17740065110.6  L18364504529.4  L19341177905.3  L2405434805.3   L2406438837.30  L27364556572.195L28613873500.2  L32041114270.11 L32170520668.2  L32172569682.188L32172719053.194L3482348703.30  L3483319967.1   L35663928186.7  L38327628946.30 L39172636981.0  L39261862547.30 L40889598521.3  L44215930101.5  L46495921149.30 L46497395924.1  L52101693566.15 L55990716303.188L56641043079.4  L56643561799.30 L58154135234.5  L59308972243.3  L60098763854.3  L62037211595.7  L6203936179.1   L65614147016.1  L67337568515.3  L9356559676.11  L9840620873.10  Q48916680945.198Q49472925079.190Q51003780618.190Q61046497836.19800000;00?00d01701801C01D01Y02>02F02o03703803a03k03l04A04i04j05L05M05Y05i05j06_07D07E07d08308=08G08b08g08l09909d0:K0:n0;T0<70<]S4PHIb1v2HVS2dZS2LF2ra2sp3LFB2FB3sp14gapn2dZ3t2c3SZ2S1R2dZ3ACV2P02PC2N1FS4PHIb1v2HVFS1R2sp2lo3SLO3sp13SP1S2LF2ra2sp3LFB2FB3sp14gapn2dZ3t2c3SZ2S2dZ3NRTS1R5NEEDR2sp2lo3LOS3SLO3sp13SP12dZ3ALO2PCS2dZ3NRTFS2LF2ra2sp3LFB2FB3sp14gapn2dZ3t2c3SZ23NRTS3sp14SP1MFS1R3HIA1h2sp2lo3TOP1HS1R3HIA1h1d3FRb2D03sp14BUDF2hq1f2HF4HFRqSS1R3HIA1h4PHIb3sp13BUD2hq1v2HV3HVqFS1d3FRb1f2HFS3sp12dZ3NRT3NT1FS1R3HIA5NEEDR2sp2lo3LOS3SLO3sp13SP12hq2dZ3ALO2PC1a2HaS2LF2ra2sp3LFB2FB3sp14gapn2dZ3t2c3SZ2FS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS1d3FRb2D01f2HFS2dZ2KZ2P0S1R2lo3LOSS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp1S2dZ4LENT3NT1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF2lo3LFB3sp14gapn3LOC2dZ3t2c3SZ2S2LF2sp2lo3LFB3sp14gapn3SP12dZ3t2c3SZ2S2LF2lo3LFB3sp14gapn3LOC2dZ3t2c3SZ2S2LF2sp2lo3LFB3sp14gapn3SP12dZ3t2c3SZ2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_CLEAN_Z : forall mq hq LBq dZ dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s7v s8v s10v,
    CSTA mq hq LBq [dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + 2 * AVOL_CALL <= PHIb -> f + 2 * fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) s6v s7v s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f8f4) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAZ EAD SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dZ) as (MT & NST' & _ & _ & _ & _ & HFT & _); try eassumption; [reflexivity|].
    pose proof MT as [(CT & _ & _ & LENT & NRT & OWNT) SGT]. rewrite EAZ in CT. unfold mpi_cells in CT. unfold MPI_MAX_LIMBS in NRT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dZ = LNull).
      { destruct (md_own dZ) eqn:EOT; [reflexivity| | exfalso; exact (NST' eq_refl)]. exfalso.
        ddestruct (HFT eq_refl) as (P0 & PC & _ & N1 & _). rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      assert (CST0 : CSTA mq hq LBq [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
      { change [dT] with (remove_nth 0 [dZ; dT]).
        eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dZ); try eassumption; reflexivity. }
      eapply (dv_TAIL_Z mq hq LBq dT dW v f r); [exact CST0| exact EAD| exact CT| exact SZ2| exact SZ4| exact UW| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dZ = LHeap).
      { destruct (md_own dZ) eqn:EOT; [exfalso; destruct OWNT as [EP _]; apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NST' eq_refl)]. }
      rewrite EO in OWNT. ddestruct OWNT as (NT1 & INT & PAL & ARRT).
      ddestruct (HFT EO) as (P0 & PC & _ & _ & BFT & _).
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dZ))) with (Z_to_bv 64 (md_n dZ))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRT; lia); rewrite Z.mod_small by (clear - NRT; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dZ))%nat with (Z.to_nat (4 * md_n dZ)) in ZCH by (clear - LENT NT1; lia).
      pose proof (conj CT I) as CTb. clear CT.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dZ) (len := 4 * md_n dZ) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dZ));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold fr_charge in *; unfold AVOL_CALL in *;
             clear - NRT NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      destruct CTb as [CT _].
      assert (CT4 : rw_cells asegs m4 (sp1 + 184) [C8 (Z_to_bv 64 (md_p dZ)); C2 (Z_to_bv 64 (md_sg dZ)); C2 (Z_to_bv 64 (md_n dZ)); C4 (md_pad dZ)]).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact CT| | ].
        - apply client_range_stack. clear. lia.
        - cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 16) with 16. split; [clear - PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (UW4 : UWCD m4).
      { rewrite <- HSq. eapply uwc_presA_dv; [exact HP4| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [clear - Ha PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dZ) LBq) [dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change [dT] with (remove_nth 0 [dZ; dT]).
        eapply (A_mpi_client2.cs_drop asegs R HIA) with (i := 0%nat) (d := dZ) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (dv_TAIL_Z m4 h4 _ dT dW _ _ r); [exact CST4| exact EAD| exact CT4| exact SZ2| exact SZ4| exact UW4| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    all: match goal with |- ?g => idtac "CLEANZ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@D11138851872.187D1162412691.186 D67430489183.186D67430489183.187L12469921329.0  L15269365847.11 L1685717371.0   L17507800040.1  L2324235832.14  L23617285646.1  L25204003039.182L27725576747.14 L32354394574.182L33880637158.1  L34673485611.1  L372066202.182  L41663468825.182L46072199973.14 L46603401559.1  L49446538027.14 L5034628706.11  L52101693566.15 L52974828408.14 L53002918955.14 L56523586534.1  L59918119559.14 L62018535662.1  L62037211595.7  L9050757852.14  L9840620873.10  Q1107808484.186 Q1109727972.187 Q11710219793.183Q11801279589.186Q11801279589.187Q17002805393.186Q34673729958.183Q38272766294.184Q40699172352.183Q49698585326.185Q522700727.183  Q52744951088.186Q52747231024.187Q9961343543.184 00000a01R02C03403503903:03>03G03K03m04[05=05A05E05g06I07707;07i08R09F09O0:=0:A0:J0:M0:h0;N0<50<\0=C0=[0>B0>i0?P0?h0@F0@^0A?0AW0B>0Be0CCS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stFS2FBSS2FBS2FB4gapnS2FBS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2FBS2FBS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R3HIA5NEEDR1h2sp2lo3LOS3SLO2FB3sp13SP13ALO2F11a2HaS2FB4gapnS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBS2FB4gapnS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22F02HBS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_stS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22F02HB". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_TAIL_Y : forall mq hq LBq dZ dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq (tp0 ts0 tn0 : Z) (tpad : word)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s10v,
    CSTA mq hq LBq [dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    rw_cells asegs mq (FB + 112) [C8 (Z_to_bv 64 tp0); C2 (Z_to_bv 64 ts0); C2 (Z_to_bv 64 tn0); C4 tpad] ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + 2 * AVOL_CALL <= PHIb -> f + 2 * fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) s7v (Z_to_bv 64 1) SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f8ec) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAZ EAD TC SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 112) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (TC' : rw_cells asegs mq (FB + 112) [C8 (Z_to_bv 64 tp0); CB 4 (le2 (Z_to_bv 64 ts0) ++ le2 (Z_to_bv 64 tn0)); C4 tpad]).
    { eapply rw_cells_reshape; [exact TC| |].
      - cbn -[le2]. repeat split; try (rewrite ?length_app, !length_le2; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc. reflexivity. }
    clear TC.
    pose proof (munch_refl [(FB + 112, FB + 128)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 112, FB + 128)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq [dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(FB + 112, FB + 128)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. split; [right; clear; lia|].
        intros d' [<-|[<-|[]]]; left; rewrite ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR; lia.
      - unfold DCS, dv_sp. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; rewrite ?SZ2, ?SZ4; split; [| exact I]|]); [ | | | | | | | | | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    assert (UW2 : UWCD m2).
    { eapply uwc_munch; [exact UW| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a Ha. cbn [outside]. split; [clear - Ha F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    eapply (dv_CLEAN_Z m2 hq LBq dZ dT dW v f r); [exact CST2| exact EAZ| exact EAD| exact SZ2| exact SZ4| exact UW2| exact HR| exact HRB| exact HSZ| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@L10376580238.3  L17507800040.1  L18364504529.4  L1921887436.5   L2405434805.3   L2406438837.30  L24950277666.2  L28506226867.195L28506345260.189L28508490530.2  L3482348703.30  L3483319967.1   L35526939379.5  L35663928186.7  L38327628946.30 L39172636981.0  L39261862547.30 L40889598521.3  L41663468825.189L44302467580.6  L46495921149.30 L46497395797.1  L50334814006.231L5156091514.196 L52101693566.15 L56021237231.3  L56523586534.1  L56641043079.4  L56643561799.30 L59308972243.3  L60098763854.3  L62037211595.7  L6203936179.1   L62590478541.1  L67337568515.3  L67420286195.3  L9356559676.11  L9840620873.10  Q10469735948.199Q28096359191.191Q34673729958.191Q44621047837.199Q52017248394.191Q522700727.191  00000;00?00@00O00P00e00m01V01W01_01i01j02602K03303403V03W04<04O04_04`05E05j06_06j06n06o07N07X07b08=08B08F08S08^09I0:00:K0;10;L0;g0<J0<eS4PHIb1v2HVS2FBFS1d3FRb2D01f2HFFS1R2sp2lo3SLO3sp13SP1S2dY3NRTS2LF2ra2sp3LFB2FB3sp14gapn2dY3t2c3SZ23NRTFS2dY3NRTS3sp14SP1MFS1d3FRb1f2HFS1R3HIA1h2sp2lo3TOP1HS1R3HIA1h1d3FRb2D03sp14BUDF2hq1f2HF4HFRqSS1R3HIA1h4PHIb3sp13BUD2hq1v2HV3HVqFS2LF2ra2sp3LFB2FB3sp14gapn2dY3t2c3SZ2S1R2dY3ACV2P02PC2N1S3sp12dY3NRT3NT1FS2LF2ra2sp3LFB2FB3sp14gapn2dY3t2c3SZ2S2LF2ra2sp3LFB2FB3sp14gapn2dY3t2c3SZ2S1R3HIA5NEEDR2sp2lo3LOS3SLO3sp13SP12hq2dY3ALO2PC1a2HaS2FB2dY3BFTS2FBFS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS2dY2KZ2P0S1R2lo3LOSS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S2dYS2dY4LENT3NT1S4PHIb1v2HVS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF3LFB2FB4gapn2dY3t2c3SZ2S2LF2sp2lo3LFB3sp14gapn3SP12dY3t2c3SZ2S2LF3LFB2FB4gapn2dY3t2c3SZ2S2LF3LFB2FB4gapn2dY3t2c3SZ2S2LF2lo3LFB3sp14gapn3LOC2dY3t2c3SZ2S2LF3LFB2FB4gapn2dY3t2c3SZ2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_CLEAN_Y : forall mq hq LBq dY dZ dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v s10v,
    CSTA mq hq LBq [dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + 3 * AVOL_CALL <= PHIb -> f + 3 * fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) s7v (Z_to_bv 64 1) SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f8d8) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAY EAZ EAD SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dY) as (MT & NST' & _ & _ & _ & _ & HFT & _); try eassumption; [reflexivity|].
    pose proof MT as [(CT & _ & _ & LENT & NRT & OWNT) SGT]. rewrite EAY in CT.
    unfold DCS in CHq. pose proof (proj1 (Forall_cons_iff _ _ _) CHq) as [SPC _]. cbn [fst snd] in SPC. unfold dv_sp in SPC. unfold mpi_cells in CT. unfold MPI_MAX_LIMBS in NRT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dY = LNull).
      { destruct (md_own dY) eqn:EOT; [reflexivity| | exfalso; exact (NST' eq_refl)]. exfalso.
        ddestruct (HFT eq_refl) as (P0 & PC & _ & N1 & _). rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      assert (CST0 : CSTA mq hq LBq [dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
      { change [dZ; dT] with (remove_nth 0 [dY; dZ; dT]).
        eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dY); try eassumption; reflexivity. }
      eapply (dv_TAIL_Y mq hq LBq dZ dT dW v f r); [exact CST0| exact EAZ| exact EAD| exact CT| exact SZ2| exact SZ4| exact UW| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dY = LHeap).
      { destruct (md_own dY) eqn:EOT; [exfalso; destruct OWNT as [EP _]; apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NST' eq_refl)]. }
      rewrite EO in OWNT. ddestruct OWNT as (NT1 & INT & PAL & ARRT).
      ddestruct (HFT EO) as (P0 & PC & _ & _ & BFT & _).
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dY))) with (Z_to_bv 64 (md_n dY))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRT; lia); rewrite Z.mod_small by (clear - NRT; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dY))%nat with (Z.to_nat (4 * md_n dY)) in ZCH by (clear - LENT NT1; lia).
      pose proof (conj CT I) as CTb. clear CT.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dY) (len := 4 * md_n dY) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dY));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold fr_charge in *; unfold AVOL_CALL in *;
             clear - NRT NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      destruct CTb as [CT _].
      assert (CT4 : rw_cells asegs m4 (FB + 112) [C8 (Z_to_bv 64 (md_p dY)); C2 (Z_to_bv 64 (md_sg dY)); C2 (Z_to_bv 64 (md_n dY)); C4 (md_pad dY)]).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact CT| | ].
        - cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16. eapply (client_range_block (arl_L R) _ _ _ _ (FB + 32) 216); [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia].
        - cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 16) with 16. split; [clear - BFT; lia| exact I]. }
      assert (UW4 : UWCD m4).
      { rewrite <- HSq. eapply uwc_presA_dv; [exact HP4| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [clear - Ha PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dY) LBq) [dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change [dZ; dT] with (remove_nth 0 [dY; dZ; dT]).
        eapply (A_mpi_client2.cs_drop asegs R HIA) with (i := 0%nat) (d := dY) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (dv_TAIL_Y m4 h4 _ dZ dT dW _ _ r); [exact CST4| exact EAZ| exact EAD| exact CT4| exact SZ2| exact SZ4| exact UW4| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    all: match goal with |- ?g => idtac "CLEANY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@D43080244883.188D53578774111.188D53578774111.189D64280614944.189L10596430123.1  L12469921329.0  L12627737381.14 L16183094286.1  L1685717371.0   L17491410731.14 L21054062635.14 L21928177762.11 L2545017055.184 L26530157006.184L2803942888.1   L32454903270.1  L33051185016.14 L35803202647.11 L38877380316.14 L43394434695.14 L44491235046.1  L51122178616.14 L52101693566.15 L53530622874.184L576250137.184  L59880000087.11 L62018535662.1  L62037211595.7  L64496004651.14 L66668189015.1  L9840620873.10  Q10596710310.185Q11801279589.188Q11801279589.189Q15686330807.185Q16625851392.185Q17757173815.186Q21538057956.188Q21540267236.189Q30802955094.186Q49698585326.187Q52744951088.188Q52747231024.189Q65424847505.188Q9075011601.185 00000a01R02C03403803903g03k03l04Z05H06106S07507907=07F07J08008908=08F09:09\0:>0:B0:E0:`0;N0;R0<90<Q0=80=_0>70>O0>m0?T0@;0@Y0A:0Aa0BH0Bo0CGS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ22HB5Ha_st5Hl_stS2FBFS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBSS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2FBS2FBS2FB4gapnS2FBS1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S2FB4gapnS2FBS2FB4gapnS1R3HIA5NEEDR1h2sp2lo3LOS3SLO2FB3sp13SP13ALO2F11a2HaS2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2LF2ra2sp3LFB2FB3sp14gapn3t2c3SZ2S2FBS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ2S2LF3LFB2FB4gapn3t2c3SZ22F02HBS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22F02HBS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ22HB5Ha_st5Hl_stS2LF3LFB2FB4gapn3t2c3SZ2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_TAIL_X : forall mq hq LBq dY dZ dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq (tp0 ts0 tn0 : Z) (tpad : word)
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s8v s10v,
    CSTA mq hq LBq [dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    rw_cells asegs mq (FB + 80) [C8 (Z_to_bv 64 tp0); C2 (Z_to_bv 64 ts0); C2 (Z_to_bv 64 tn0); C4 tpad] ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + 3 * AVOL_CALL <= PHIb -> f + 3 * fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) (Z_to_bv 64 (FB + 80)) s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f8cc) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAY EAZ EAD TC SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (IND : In (FB + 32, 216) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 80) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (TC' : rw_cells asegs mq (FB + 80) [C8 (Z_to_bv 64 tp0); CB 4 (le2 (Z_to_bv 64 ts0) ++ le2 (Z_to_bv 64 tn0)); C4 tpad]).
    { eapply rw_cells_reshape; [exact TC| |].
      - cbn -[le2]. repeat split; try (rewrite ?length_app, !length_le2; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc. reflexivity. }
    clear TC.
    pose proof (munch_refl [(FB + 80, FB + 96)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 80, FB + 96)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq [dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
    { eapply (A_mpi_client2.cs_nop asegs R HIA) with (mq := mq) (WX := [(FB + 80, FB + 96)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. split; [right; clear; lia|].
        intros d' [<-|[<-|[<-|[]]]]; left; rewrite ?EAY, ?EAZ, ?EAD; clear - F1 ALO LOS SLO SP1 NEEDR; lia.
      - unfold DCS, dv_sp. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; rewrite ?SZ2, ?SZ4; split; [| exact I]|]); [ | | | | | | | | | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    assert (UW2 : UWCD m2).
    { eapply uwc_munch; [exact UW| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a Ha. cbn [outside]. split; [clear - Ha F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    eapply (dv_CLEAN_Y m2 hq LBq dY dZ dT dW v f r); [exact CST2| exact EAY| exact EAZ| exact EAD| exact SZ2| exact SZ4| exact UW2| exact HR| exact HRB| exact HSZ| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0@L10711524986.198L18364504529.4  L18615654630.3  L2405434805.3   L2406438837.30  L2803942888.1   L28852399192.1  L29690133430.233L32454903270.1  L3482348703.30  L3483319967.1   L34898139424.2  L34899808945.197L34900155694.191L35663928186.7  L38327628946.30 L39172636981.0  L39261862547.30 L40889598521.3  L44124421155.5  L46495301590.1  L46495921149.30 L52101693566.15 L53536261571.3  L56641043079.4  L56643561799.30 L57091752990.3  L576250137.191  L59308972243.3  L60098763854.3  L60283232188.5  L62037211595.7  L6203936179.1   L63744388128.2  L66082189042.6  L67337568515.3  L9356559676.11  L9840620873.10  Q10596710310.193Q15686330807.193Q20546156061.201Q4182517772.201 00000V00W00c00d01901=01B01h01l02602702@02j02k03@03h03i04K04L04X04Y04j05`05k05l06K06V07<07G07Q07`08;08@08I08]08k09V0:=0:Y0;50;Q0;mS2LF2ra2sp3LFB2FB3sp14gapn3dLX3t2c3SZ2FS2FB3dLX3BFTFS1R2sp2lo3SLO3sp13SP1S2FBS3dLXS2LF2ra2sp3LFB2FB3sp14gapn3dLX3t2c3SZ2S2FBS3sp14SP1MFS3dLX3NRTS2LF2ra2sp3LFB2FB3sp14gapn3dLX3t2c3SZ23NRTFS1R3HIA1h2sp2lo3TOP1HS1R3HIA1h1d3FRb2D03sp14BUDF2hq1f2HF4HFRqSS1R3HIA1h4PHIb3sp13BUD2hq1v2HV3HVqFS1d3FRb1f2HFFS3sp13dLX3NRT3NT1S1R3HIA5NEEDR2sp2lo3LOS3SLO3sp13SP12hq3dLX3ALO2PC1a2HaS4PHIb1v2HVFS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS4PHIb1v2HVS2LF2ra2sp3LFB2FB3sp14gapn3dLX3t2c3SZ2S3dLX2KZ2P0S1R2lo3LOSS1d3FRb2D01f2HFS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3dLX3NRTS1R3dLX3ACV2P02PC2N1S3dLX4LENT3NT1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF3LFB2FB4gapn3dLX3t2c3SZ2S2LF3LFB2FB4gapn3dLX3t2c3SZ2S2LF3LFB2FB4gapn3dLX3t2c3SZ2S2LF3LFB2FB4gapn3dLX3t2c3SZ2". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP TPV LFB HNDk DIMG H0M XW W0AS D0 SP1 SP1M GAP F64 FRSH CFB APF ESF LOC CSP FN64 FB8 PZ ZF BUD BUDF"] Lemma dv_CLEAN_X : forall mq hq LBq dLX dY dZ dT dW v f (r : Z) c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c czc gb z32 z48 z64 (u0 u1 u2 : word) jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s8v s10v,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f -> md_addr dLX = FB + 80 -> md_addr dY = FB + 112 -> md_addr dZ = sp1 + 184 -> md_addr dT = FB + 144 ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> UWCD mq ->
    -2^31 < r <= 0 -> (r = 0 -> 0 < mpd_abs dB) -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v + 4 * AVOL_CALL <= PHIb -> f + 4 * fr_charge (d + 1) <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FB + 112)) (Z_to_bv 64 (FB + 80)) s8v SH4 s10v (Z_to_bv 64 r) t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f8b8) fc None mq (seg_rom asegs)).
  Proof.
    intros until s10v. intros CST EAX EAY EAZ EAD SZ2 SZ4 UW HR HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dLX) as (MT & NST' & _ & _ & _ & _ & HFT & _); try eassumption; [reflexivity|].
    pose proof MT as [(CT & _ & _ & LENT & NRT & OWNT) SGT]. rewrite EAX in CT.
    unfold DCS in CHq. pose proof (proj1 (Forall_cons_iff _ _ _) CHq) as [SPC _]. cbn [fst snd] in SPC. unfold dv_sp in SPC. unfold mpi_cells in CT. unfold MPI_MAX_LIMBS in NRT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dLX = LNull).
      { destruct (md_own dLX) eqn:EOT; [reflexivity| | exfalso; exact (NST' eq_refl)]. exfalso.
        ddestruct (HFT eq_refl) as (P0 & PC & _ & N1 & _). rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      assert (CST0 : CSTA mq hq LBq [dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH v f).
      { change [dY; dZ; dT] with (remove_nth 0 [dLX; dY; dZ; dT]).
        eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dLX); try eassumption; reflexivity. }
      eapply (dv_TAIL_X mq hq LBq dY dZ dT dW v f r); [exact CST0| exact EAY| exact EAZ| exact EAD| exact CT| exact SZ2| exact SZ4| exact UW| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dLX = LHeap).
      { destruct (md_own dLX) eqn:EOT; [exfalso; destruct OWNT as [EP _]; apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NST' eq_refl)]. }
      rewrite EO in OWNT. ddestruct OWNT as (NT1 & INT & PAL & ARRT).
      ddestruct (HFT EO) as (P0 & PC & _ & _ & BFT & _).
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dLX))) with (Z_to_bv 64 (md_n dLX))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRT; lia); rewrite Z.mod_small by (clear - NRT; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dLX))%nat with (Z.to_nat (4 * md_n dLX)) in ZCH by (clear - LENT NT1; lia).
      pose proof (conj CT I) as CTb. clear CT.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dLX) (len := 4 * md_n dLX) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dLX));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold fr_charge in *; unfold AVOL_CALL in *;
             clear - NRT NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
      destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      destruct CTb as [CT _].
      assert (CT4 : rw_cells asegs m4 (FB + 80) [C8 (Z_to_bv 64 (md_p dLX)); C2 (Z_to_bv 64 (md_sg dLX)); C2 (Z_to_bv 64 (md_n dLX)); C4 (md_pad dLX)]).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact CT| | ].
        - cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16. eapply (client_range_block (arl_L R) _ _ _ _ (FB + 32) 216); [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| clear; lia| clear; lia].
        - cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 16) with 16. split; [clear - BFT; lia| exact I]. }
      assert (UW4 : UWCD m4).
      { rewrite <- HSq. eapply uwc_presA_dv; [exact HP4| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [clear - Ha PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dLX) LBq) [dY; dZ; dT] dW (DCSQ c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c152 c160 t2c [] czc gb z32 z48 z64 [C4 u0; C4 u1; C4 u2] jq) DV_FSH (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change [dY; dZ; dT] with (remove_nth 0 [dLX; dY; dZ; dT]).
        eapply (A_mpi_client2.cs_drop asegs R HIA) with (i := 0%nat) (d := dLX) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (dv_TAIL_X m4 h4 _ dY dZ dT dW _ _ r); [exact CST4| exact EAY| exact EAZ| exact EAD| exact CT4| exact SZ2| exact SZ4| exact UW4| exact HR| exact HRB| exact HSZ| |].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    all: match goal with |- ?g => idtac "CLEANX-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L13157033923.1  L32269442061.5  L32596543859.5  L33595343993.6  L34915349256.1  L35663928186.7  L39513730120.1  L42091889404.6  L48161827075.1  L50794195360.5  L55879915635.5  L60098763854.3  L61968151637.1  L68664817267.5  L6961803708.6   L9356559676.11  Q45989664010.196Q67304644247.19600000400E00V00W00X00m00n00o01301D01U01_01c02402502`03H043S2FBS2sp3sp14gapn3SP1S2sp3sp14gapn3SP1FFS1R3HIA1h2sp2lo3TOP1HFFS2FBS2sp3sp14gapn3SP1S2sp3sp14gapn3SP1S1R2lo3LOSS2FBS2sp3sp14gapn3GAPFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB3sp14gapn3LOC3t2c3tpc3SZ23SZTS2LF2sp2lo3LFB3sp14gapn3SP13t2c3tpc3SZ23SZT". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO TOP LFB H0M XW SP1 SP1M GAP F64 FRSH CFB APF LOC CSP FN64"] Lemma dv_EXIT0 : forall mq hq LBq dLX dY dZ dT dW v f c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 t2c czc gb z32 z48 z64 tpc jq
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s4v s6v s7v s8v s10v s11v,
    CSTA mq hq LBq [dLX; dY; dZ; dT] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c [] czc gb z32 z48 z64 tpc jq) DV_FSH v f ->
    md_addr dZ = sp1 + 184 -> md_own dLX = LNull -> md_own dY = LNull -> md_own dZ = LNull -> md_own dT = LNull ->
    cells_size t2c = 16%nat -> cells_size czc = 16%nat -> cells_size tpc = 12%nat ->
    0 < mpd_abs dB -> md_n dW <= div_mpi_nz (md_n dX) (md_n dA) (md_n dB) -> v <= PHIb -> f <= FRb ->
    aevtA asegs (KF asegs R HIA hq mo0) POSTD
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 FB) (Z_to_bv 64 FB) s4v (Z_to_bv 64 (-8)) s6v s7v s8v SH4 s10v s11v t3 t4 t5 t6)
          F (Z_to_bv 64 0x9fab0) fc None mq (seg_rom asegs)).
  Proof.
    intros until s11v. intros CST EAZ OX0 OY0 OZ0 OT0 SZ2 SZ4 SZT HRB HSZ HV HF. rt_facts.
    destruct (A_mpi_client2.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (CHq & SHq & MIq & STq & HHq).
    destruct (A_mpi_client2.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es _ _ _ _ _ _ _ _ _ CST) as (HTq & HSq & HFq & HCSq & HVq & HFRq).
    dpose FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    edestruct (A_mpi_client2.cs_local_facts asegs R HIA) with (i := 2%nat) (d := dZ) as (MZ & _); try eassumption; [reflexivity|].
    pose proof MZ as [(CZ & _) _]. rewrite EAZ in CZ. unfold mpi_cells in CZ.
    assert (CSTa : CSTA mq hq LBq [dY; dZ; dT] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c [] czc gb z32 z48 z64 tpc jq) DV_FSH v f).
    { change [dY; dZ; dT] with (remove_nth 0 [dLX; dY; dZ; dT]). eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dLX); try eassumption; reflexivity. }
    assert (CSTb : CSTA mq hq LBq [dZ; dT] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c [] czc gb z32 z48 z64 tpc jq) DV_FSH v f).
    { change [dZ; dT] with (remove_nth 0 [dY; dZ; dT]). eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dY); try eassumption; reflexivity. }
    assert (CSTc : CSTA mq hq LBq [dT] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c [] czc gb z32 z48 z64 tpc jq) DV_FSH v f).
    { change [dT] with (remove_nth 0 [dZ; dT]). eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dZ); try eassumption; reflexivity. }
    assert (CSTd : CSTA mq hq LBq [] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c [] czc gb z32 z48 z64 tpc jq) DV_FSH v f).
    { change (@nil mpd) with (remove_nth 0 [dT]). eapply (A_mpi_client2.cs_drop_null asegs R HIA) with (i := 0%nat) (d := dT); try eassumption; reflexivity. }
    clear CST CSTa CSTb CSTc.
    unfold DCS in CHq. repeat (apply Forall_cons_iff in CHq; destruct CHq as [?K CHq]). cbn [fst snd] in *.
    lazymatch type of CZ with rw_cells _ _ _ ?zcn =>
      assert (CSTe : CSTA mq hq LBq [] dW (DCS (dv_sp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160) t2c zcn czc gb z32 z48 z64 tpc jq) DV_FSH v f);
      [ eapply (A_mpi_client2.cs_set_cells asegs R HIA) with (mq := mq); try eassumption;
        [ unfold DCS; repeat (apply Forall_cons; [cbn [fst snd]; first [assumption | exact CZ]|]); apply Forall_nil
        | unfold DCS, dv_sp, A_mpi_client2.chunk_okA;
          repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add]; rewrite ?SZ2, ?SZ4, ?SZT; split; [| intros d' []]|]); [ | | | | | | | | | | | | apply Forall_nil];
          first [ left; clear - SP1 GAP; lia | right; left; clear; lia | right; right; clear; lia ] ]
      | ] end.
    unfold dv_sp in *.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply (dv_EPIK mq hq LBq dW v f 0); [exact CSTe| reflexivity| exact SZ2| reflexivity| exact SZ4| clear; lia| intros _; exact HRB| exact HSZ| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma presA_munch_shadow : forall (CSx : Z -> Prop) LBx LFx SPx SSPx TOPx Wx (m0x mx m2x : mem) c n,
    cs_ok AL CSx -> (forall c', cshd R LBx LFx SSPx TOPx c' -> CSx c') ->
    (forall x, CSx x -> hl_data_hi L <= shadow_of AL x < alloc_ceiling) -> alloc_ceiling <= SPx ->
    (forall B k, In (B, k) (LBx ++ fdata LFx) -> crange CSx B k) ->
    presA asegs R LBx LFx SPx SSPx TOPx Wx m0x mx ->
    munch [(shadow_of AL c, shadow_of AL c + n)] mx m2x -> wmono asegs mx m2x ->
    c mod 8 = 0 -> crange CSx c (8 * n) -> shadow_free R LBx LFx SSPx TOPx c (8 * n) ->
    presA asegs R LBx LFx SPx SSPx TOPx Wx m0x m2x.
  Proof.
    intros CSx LBx LFx SPx SSPx TOPx Wx m0x mx m2x c n OK HCS SHB HSP HBK [P S] MU WM Hc8 HC HF.
    clear - OK HCS SHB HSP HBK P S MU WM Hc8 HC HF. destruct OK as (C1 & _).
    assert (NCS : forall x, shadow_of AL c <= x < shadow_of AL c + n -> ~ CSx x).
    { intros x Hx. replace x with (shadow_of AL (c + 8 * (x - shadow_of AL c))) by (rewrite shadow_of_plus; lia).
      apply (proj2 (proj2 (proj2 (C1 _ (HC (c + 8 * (x - shadow_of AL c)) ltac:(lia)))))). }
    split.
    - intros x Hx Hcl Ho. destruct (P x Hx Hcl Ho) as [E1 W1]. split; [| intros Hw; apply WM; apply W1; exact Hw].
      rewrite <- E1. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I]. intros Hin.
      set (c1 := c + 8 * (x - shadow_of AL c)).
      assert (X1 : x = shadow_of AL c1) by (subst c1; rewrite shadow_of_plus; lia).
      assert (CS1 : CSx c1) by (subst c1; apply HC; lia).
      destruct (SHB c1 CS1) as [D1 D2].
      destruct Hcl as [Hs|[[Hd1 Hd2]|([Bb jb] & Hb & Hr)]]; [lia| lia|].
      apply (NCS x Hin). cbn in Hr. replace x with (Bb + (x - Bb)) by lia. apply (HBK Bb jb Hb). lia.
    - intros c' Hc' Hr. destruct (S c' Hc' Hr) as [E1 W1]. split; [| intros Hw; apply WM; apply W1; exact Hw].
      rewrite <- E1. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I]. intros Hin.
      apply (HF c' Hc'). unfold shadow_of in *.
      pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.div_mod c' 8 ltac:(lia)). pose proof (Z.mod_pos_bound c' 8 ltac:(lia)).
      lia.
  Qed.
  #[using="IMG NEEDR LOS SLO TOP LFB HNDk DIMG H0M XW W0AS SP1 F64 FRSH CFB APF ESF LOC CSP FN64 FB8"] Lemma cs_shadow_write : forall mq m2 hq LBq ls dW CS0 SHC SHC' v f (j : Z),
    CSTA mq hq LBq ls dW CS0 SHC v f -> 4 <= j < 31 ->
    (forall d0, In d0 ls -> md_addr d0 + 16 <= FB + 8 * j \/ FB + 8 * j + 8 <= md_addr d0) ->
    munch [(Z.shiftr FB 3 + al_sb AL + j, Z.shiftr FB 3 + al_sb AL + j + 1)] mq m2 -> wmono asegs mq m2 ->
    HM asegs R HIA hq LBq LF1 m2 -> mem_inv asegs m2 -> stk asegs m2 lo sp1 ->
    Forall (fun ac => rw_cells asegs m2 (fst ac) (snd ac)) CS0 ->
    rw_cells asegs m2 (Z.shiftr FB 3 + al_sb AL) SHC' -> cells_size SHC' = cells_size SHC ->
    CSTA m2 hq LBq ls dW CS0 SHC' v f.
  Proof.
    intros mq m2 hq LBq ls dW CS0 SHC SHC' v f j CST J4 LJ MU WM HH2 MI2 ST2 CH2 SH2 SZ. clear W0BLK SPA SP1M NST.
    pose proof (art_lo asegs R HIA) as ALO. pose proof FRSH as (F0 & F1 & F2 & F3).
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    destruct (A_mpi_client2.cs_w_facts asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 256 dX es LOS LOC CSP FRSH FN64 XW W0AS _ _ _ _ _ _ _ _ _ CST) as (_ & _ & EA & _).
    destruct CST as (HH & (HTc & HSc & HFc) & HCSc & (HVc & HFRc) & LOK & SA & LA & MW & OW & WOK & SUB & COV & FRS & EXT & PX & FRL & FRW & MI & ST & CH & CHS & SHD & SHN).
    assert (KIN : forall b, In b (mpd_keep LB dX) -> In b LB).
    { intros b Hb. unfold mpd_keep in Hb. destruct (md_own dX); [exact Hb| apply filter_In in Hb; exact (proj1 Hb)| exact Hb]. }
    assert (KS : forall b, In b (mpd_keep LB dX) -> In b LBq).
    { intros b Hb. apply SUB; [exact (KIN b Hb)| exact (A_mpi_client2.In_mpd_keep_not_blk_w _ _ _ Hb)]. }
    assert (ESH : Z.shiftr FB 3 + al_sb AL + j = shadow_of AL (FB + 8 * j)).
    { unfold shadow_of. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm 8 j), Z.div_add by lia. lia. }
    rewrite ESH in MU.
    assert (CFBq : crange (hcs asegs R HIA hq) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]).
    assert (CG : crange (hcs asegs R HIA hq) (FB + 8 * j) (8 * 1)) by (eapply crange_sub; [exact CFBq| lia| lia]).
    assert (G8 : (FB + 8 * j) mod 8 = 0) by (clear - FB8; Z.div_mod_to_equations; lia).
    pose proof (fresh_apart_relist_m hq LBq mq FB 256 FRSH HH) as (_ & _ & _ & G4).
    set (LBk := (FB + 32, 8 * j - 32) :: (FB + 8 * j + 8, 240 - 8 * j) :: LBq).
    assert (CSH : forall c', cshd R LBk ((FB, 0) :: LF) (arl_stklo R) (hstkhi asegs R HIA hq) c' -> hcs asegs R HIA hq c').
    { intros c' Hc'. eapply (cshd_hcs asegs R HIA hq LBq LF1 mq (arl_stklo R) c' HH); [lia|].
      unfold cshd in Hc' |- *. destruct Hc' as [Hs|[(b & Hb & Hr)|[(b & Hb & Hr)|Hst]]].
      - left. exact Hs.
      - destruct Hb as [<-|[<-|Hb]].
        + right. right. left. exists (FB, 256). split; [left; reflexivity| cbn [fst snd] in Hr |- *; lia].
        + right. right. left. exists (FB, 256). split; [left; reflexivity| cbn [fst snd] in Hr |- *; lia].
        + right. left. exists b. split; [exact Hb| exact Hr].
      - destruct Hb as [<-|Hb]; [cbn [fst snd] in Hr; lia|]. right. right. left. exists b. split; [right; exact Hb| exact Hr].
      - right. right. right. exact Hst. }
    assert (CRK : forall B0 k0, In (B0, k0) (LBk ++ fdata ((FB, 0) :: LF)) -> crange (hcs asegs R HIA hq) B0 k0).
    { intros B0 k0 Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - destruct Hb as [E|[E|Hb]].
        + injection E as E1 E2. subst B0 k0. eapply crange_sub; [exact CFBq| lia| lia].
        + injection E as E1 E2. subst B0 k0. eapply crange_sub; [exact CFBq| lia| lia].
        + apply (hm_blocks_cs asegs R HIA hq LBq LF1 mq HH). apply in_app_iff. left. exact Hb.
      - cbn [fdata] in Hb. destruct Hb as [E|[E|Hb]].
        + injection E as E1 E2. subst B0 k0. intros x Hx. lia.
        + injection E as E1 E2. subst B0 k0. intros x Hx. lia.
        + apply (hm_blocks_cs asegs R HIA hq LBq LF1 mq HH). apply in_app_iff. right. cbn [fdata]. right. right. exact Hb. }
    assert (SFk : shadow_free R LBk ((FB, 0) :: LF) (arl_stklo R) (hstkhi asegs R HIA hq) (FB + 8 * j) (8 * 1)).
    { intros c' Hc' Hin. unfold cshd in Hc'. destruct Hc' as [Hs|[(b & Hb & Hr)|[(b & Hb & Hr)|Hst]]].
      - lia.
      - destruct Hb as [<-|[<-|Hb]]; [cbn [fst snd] in Hr; lia| cbn [fst snd] in Hr; lia|].
        destruct b as [B0 k0]. destruct (G4 B0 k0 ltac:(apply in_app_iff; left; exact Hb)) as [K|K]; cbn [fst snd] in Hr; lia.
      - destruct Hb as [<-|Hb]; [cbn [fst snd] in Hr; lia|].
        destruct b as [B0 k0]. destruct (APF B0 k0 Hb) as [K|K]; cbn [fst snd] in Hr; lia.
      - destruct Hst as [Hd _]. lia. }
    assert (PRK : presA asegs R LBk ((FB, 0) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [] mq m2).
    { eapply (presA_munch_shadow (hcs asegs R HIA hq)) with (c := FB + 8 * j) (n := 1);
        [exact CSOKq| exact CSH| exact (hcs_shadow_band asegs R HIA hq)| lia| exact CRK| apply presA_refl| exact MU| exact WM| exact G8| exact CG| exact SFk]. }
    assert (LOK2 : Forall (A_mpi_client2.local_okA asegs R HIA (bv_unsigned sp) sp1 FB 256 m2 hq LBq) ls).
    { apply Forall_forall. intros dj Hdj. pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & NSJ & JL & JA8 & OJ).
      destruct (A_mpi_client2.mpd_step asegs R HIA LF FB 0 mq m2 hq hq LBq LBk LBq sp1 [] dj MJ OJ PRK MI MI2 (fun x Hx => Hx) ltac:(lia)) as [MJ2 OJ2].
      - unfold client_range. intros a Ha. unfold client_addr, in_block. destruct JL as [[JL1 JL2]|[JL1 JL2]].
        + right. right. destruct (LJ dj Hdj) as [K|K].
          * exists (FB + 32, 8 * j - 32). split; [apply in_or_app; left; left; reflexivity| cbn [fst snd]; lia].
          * exists (FB + 8 * j + 8, 240 - 8 * j). split; [apply in_or_app; left; right; left; reflexivity| cbn [fst snd]; lia].
        + left. lia.
      - intros O. right. right. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ MJ O)).
      - exact I.
      - intros _. exact I.
      - intros b Hb. destruct (MpiClient.mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ MJ O)).
      - split; [exact MJ2|]. split; [exact NSJ|]. split; [exact JL|]. split; [exact JA8| exact OJ2]. }
    destruct (A_mpi_client2.mpd_step asegs R HIA LF FB 0 mq m2 hq hq LBq LBk LBq sp1 [] dW MW ltac:(rewrite EA; exact OW) PRK MI MI2 (fun x Hx => Hx) ltac:(lia)) as [MW2 OW2].
    { rewrite EA. eapply (A_mpi_client2.w0_client_step asegs R HIA h LB LF (bv_unsigned sp) lo sp1 FB 0 dX LOC CSP XW W0AS LBk sp1); [| lia].
      intros b Hb. right. right. exact (KS b Hb). }
    { intros O. right. right. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ MW O)). }
    { exact I. }
    { intros _. exact I. }
    { intros b Hb. destruct (MpiClient.mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ MW O)). }
    assert (EXT2 : Forall (fun e => mpd_at asegs m2 LBq e /\ aobj asegs AL (hcs asegs R HIA hq) m2 (md_addr e) 16) es).
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as [ME OE].
      destruct (A_mpi_client2.mpd_step asegs R HIA LF FB 0 mq m2 hq hq LBq LBk LBq sp1 [] e ME OE PRK MI MI2 (fun x Hx => Hx) ltac:(lia)) as [ME2 OE2].
      - eapply (A_mpi_client2.ext_client_step R LB LF (bv_unsigned sp) lo FB 0 dX es ESF e LBk sp1 He); [| lia].
        intros b Hb. right. right. exact (KS b Hb).
      - intros O. right. right. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ ME O)).
      - exact I.
      - intros _. exact I.
      - intros b Hb. destruct (MpiClient.mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (A_mpi_client2.mpd_heap_in _ _ _ _ ME O)).
      - split; [exact ME2| exact OE2]. }
    assert (PX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(md_addr dX, md_addr dX + 16)] m m2).
    { eapply (presA_munch_shadow (hcs asegs R HIA hq)) with (c := FB + 8 * j) (n := 1);
        [exact CSOKq| | exact (hcs_shadow_band asegs R HIA hq)| lia| | exact PX| exact MU| exact WM| exact G8| exact CG|].
      - intros c' Hc'. apply HCSc. eapply (cshd_hcs asegs R HIA h LB LF m (arl_stklo R) c' H0M); [lia|].
        unfold cshd in Hc' |- *. destruct Hc' as [Hs|[(b & Hb & Hr)|[Hl|Hst]]];
          [left; exact Hs| right; left; exists b; split; [exact (KIN b Hb)| exact Hr]| right; right; left; exact Hl| right; right; right; exact Hst].
      - intros B0 k0 Hb. eapply crange_mono; [exact HCSc|]. apply (hm_blocks_cs asegs R HIA h LB LF m H0M).
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (KIN _ Hb)| right; exact Hb].
      - intros c' Hc' Hin. unfold cshd in Hc'. destruct Hc' as [Hs|[(b & Hb & Hr)|[(b & Hb & Hr)|Hst]]].
        + lia.
        + destruct b as [B0 k0]. destruct (F3 B0 k0 ltac:(apply in_app_iff; left; exact (KIN _ Hb))) as [K|K]; cbn [fst snd] in Hr; lia.
        + destruct b as [B0 k0]. destruct (APF B0 k0 Hb) as [K|K]; cbn [fst snd] in Hr; lia.
        + destruct Hst as [Hd _]. lia. }
    unfold A_mpi_client2.cstateA.
    split; [exact HH2|]. split; [exact (conj HTc (conj HSc HFc))|]. split; [exact HCSc|]. split; [exact (conj HVc HFRc)|].
    split; [exact LOK2|]. split; [exact SA|]. split; [exact LA|]. split; [exact MW2|]. split; [rewrite <- EA; exact OW2|].
    split; [exact WOK|]. split; [exact SUB|]. split; [exact COV|]. split; [exact FRS|]. split; [exact EXT2|]. split; [exact PX2|].
    split; [exact FRL|]. split; [exact FRW|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact CH2|]. split; [exact CHS|].
    split; [exact SH2| rewrite SZ; exact SHN].
  Qed.
  End Fr.
  End Call.
End WalkC.
