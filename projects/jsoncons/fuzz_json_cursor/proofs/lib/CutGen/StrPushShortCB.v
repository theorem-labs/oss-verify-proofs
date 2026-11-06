(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmFloatCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_strpush_sfast_cboth_T Cut_strpush_sfast_cboth Cut_strpush_sgrow_cboth_T Cut_strpush_sgrow_cboth Cut_strpush_fast_cboth_T Cut_strpush_fast_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module F := Cut_strpush_sfast_cboth.  Module FT := Cut_strpush_sfast_cboth_T.
Module G := Cut_strpush_sgrow_cboth.  Module GT := Cut_strpush_sgrow_cboth_T.
Module FL := Cut_strpush_fast_cboth.  Module FLT := Cut_strpush_fast_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module SPS.
Definition PC_OPNEW : Z := 1363704.
Definition PC_MM : Z := 520748.
Definition RETPC : Z := 990728.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition cE := EVar 11. Definition nE := EVar 32. Definition nbE := EVar 44.
Definition BNEW : list (expr * expr) := [(nbE, ELit 48)].
Definition BLKS (i : nat) : list (expr * expr) := match i with 0%nat => [] | _ => BNEW end.
Definition FFS_F : list (list (expr * Z * Z)) := map (fun _ => []) F.CPS.
Definition FFS_G : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition NEWS_MM : list kentry := STAT ++ [KBlob (SA nbE 0) (ELit 22) 0].
Definition CPF0 : list SGP.region := [(EVar 2, -4368, ELit 4368); (oE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, ELit 48)].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition OPN : expr := EAlu Instr.ALU_ADD oE nE.

Definition leaf_chk_f (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (Z.eqb pc RETPC && Nat.eqb i 0 && CBA.exit_base_chk FT.NF RETPC c ps && CHA.foot_chk FT.NF F.HDECL c [] [] && CH2.blocks_eqb (nth i F.BLS []) []
       && CBA.regions_eqb (CC.cp_F c) CPF0 && Nat.leb 40 (CC.cp_nx c)
       && has cells (KWord (SA oE 0) 1 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) nE) (ELit 2))) && has cells (KBlob (SA oE 1) nE 0)
       && has cells (KWord (SA OPN 1) 1 cE) && has cells (KWord (SA OPN 2) 1 (ELit 0)))%bool
  end.

Definition leaf_chk_g (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth i G.BLS []) (BLKS i) && CH2.blocks_eqb (nth j G.BLS []) (BLKS j) && CHA.foot_chk GT.NF G.HDECL c (BLKS i) [] &&
              if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb i 0 && Nat.eqb j 1 && Nat.eqb nx 40 && CBA.regions_eqb (CC.cp_F c) CPF0
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] news None c ps cj [] [] BNEW [])
                 && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (ELit 48) news
                 && CL.ps_reg_is ps 10 (ELit 48))%bool
              else if Z.eqb pc PC_MM then
                (Z.eqb (SR.ps_pc ps) PC_MM && Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF1 && Nat.leb 45 (CC.cp_nx c)
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BNEW [] [(nbE, 0, ELit 22)] NEWS_MM (Some nbE) c ps cj BNEW [] BNEW [])
                 && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD oE (ELit 1)) && CL.ps_reg_is ps 12 (ELit 22) && has cells (KBlob (SA oE 1) (ELit 22) 0))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && Nat.eqb i 2 && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c BNEW [] && CH2.blocks_eqb (nth i G.BLS []) BNEW
           && CBA.regions_eqb (CC.cp_F c) CPF1 && Nat.leb 45 (CC.cp_nx c)
           && has cells (KWord (SA oE 0) 8 (ELit 49)) && has cells (KWord (SA oE 8) 8 (ELit 23)) && has cells (KWord (SA oE 16) 8 nbE)
           && has cells (KBlob (SA nbE 0) (ELit 22) 0) && has cells (KWord (SA nbE 22) 1 cE) && has cells (KWord (SA nbE 23) 1 (ELit 0)))%bool
      end
  end.
Lemma leaf_f_ok : CH2.leaves_all F.CPS F.TAGS leaf_chk_f = true.
Proof. vmc_refl. Qed.
Lemma leaf_g_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk_g = true.
Proof. vmc_refl. Qed.
Lemma heap_f_ok : CHA.heap_chkA FT.NF F.HDECL F.BLS FFS_F F.CPS F.TAGS = true.
Proof. vmc_refl. Qed.
Lemma heap_g_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS_G G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma FFSF_nil : forall i, nth i FFS_F [] = [].
Proof. intros i. unfold FFS_F. do 1 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma FFSG_nil : forall i, nth i FFS_G [] = [].
Proof. intros i. unfold FFS_G. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
End SPS.

Module SPF.
Definition PC_OPNEW : Z := 1363704.
Definition PC_MM : Z := 520748.
Definition PC_OPDEL : Z := 980676.
Definition RETPC : Z := 990728.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition cE := EVar 11. Definition kE := EVar 32. Definition szE := EVar 33. Definition pE := EVar 34. Definition nbE := EVar 44.
Definition CAP : expr := EMd Instr.M_MUL (ELit 2) kE.
Definition BOLD : list (expr * expr) := [(pE, CAP)].
Definition FFS_F : list (list (expr * Z * Z)) := map (fun _ => []) FL.CPS.
Definition STAT : list kentry := [KImg FLT.GLO FLT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition CPF0 : list SGP.region := [(EVar 2, -4368, ELit 4368); (oE, 0, ELit 24); (pE, 0, CAP)].
Definition has := CC.has_cell.

Definition leaf_chk_f (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (Z.eqb pc RETPC && Nat.eqb i 0 && CBA.exit_base_chk FLT.NF RETPC c ps && CHA.foot_chk FLT.NF FL.HDECL c BOLD [] && CH2.blocks_eqb (nth i FL.BLS []) BOLD
       && CBA.regions_eqb (CC.cp_F c) CPF0 && Nat.leb 40 (CC.cp_nx c)
       && has cells (KWord (SA oE 0) 8 (EAlu Instr.ALU_ADD CAP (ELit 1))) && has cells (KWord (SA oE 8) 8 (EAlu Instr.ALU_ADD szE (ELit 1))) && has cells (KWord (SA oE 16) 8 pE)
       && has cells (KBlob (SA pE 0) szE 0) && has cells (KWord (SA (EAlu Instr.ALU_ADD szE pE) 0) 1 cE) && has cells (KWord (SA (EAlu Instr.ALU_ADD szE pE) 1) 1 (ELit 0)))%bool
  end.

Lemma leaf_f_ok : CH2.leaves_all FL.CPS FL.TAGS leaf_chk_f = true.
Proof. vmc_refl. Qed.
Lemma heap_f_ok : CHA.heap_chkA FLT.NF FL.HDECL FL.BLS FFS_F FL.CPS FL.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma FFSF_nil : forall i, nth i FFS_F [] = [].
Proof. intros i. unfold FFS_F. do 2 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
End SPF.

Section StrPushShortOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI SPS.PC_OPNEW.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI SPS.PC_MM false.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Lemma src_in_fobj : forall LB FF LK cr A (M : mem) V sp scr o q n bs,
  ri_inv HI LB FF LK cr A M V -> CL5A.ainfr FF o 24 -> o mod 8 = 0 -> shadow_zero M o 3 -> 0 <= q -> 0 <= n -> q + n <= 24 ->
  rdn (hl_segs L) M (Z_to_bv 64 (o + q)) (Z.to_nat n) = Some bs ->
  CRC.mem_src L ar LB FF sp scr M (o + q) n bs.
Proof.
  intros LB FF LK cr A M V sp scr o q n bs HH Ofr O8 Osh Hq Hn Hqn Hrd.
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  split; [|split; [lia|split; [|split; [|exact Hrd]]]].
  - intros a Ha. left. unfold shadow_zero in Osh. replace (S a) with (S o + (a - o) / 8).
    + apply Osh. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    + unfold S. apply Z.mod_divide in O8; [|lia]. destruct O8 as [t ->].
      assert (E1 : a / 8 = (a - t * 8) / 8 + t) by (rewrite <- Z.div_add by lia; f_equal; lia).
      assert (E2 : t * 8 / 8 = t) by (apply Z.div_mul; lia). lia.
  - destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
    unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI in *. split; [lia|]. split; [lia|]. left. lia.
  - intros i Hi. right. destruct (CL5A.infr_wok L ar LB FF sp scr o 24 (o + q + i) RFx Ofr ltac:(lia)) as (_ & G2 & _). exact (aclientw_client _ _ _ _ _ _ _ G2).
Qed.

Lemma push_back_sfast : forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r : Z) (s : list Z),
  PMSA.cps_asan L ar HI 990424 r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => Z.of_nat (length s) < 22 /\ PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ PMFCA.sso_nonul L M o s /\ L5.defined M o 24 /\
                  PMLA.fobj M FF o 24 /\ PMSA.stksh ar M sp PMSA.STR_SCR)
      (fun R M R' M' LB' cr' LBk W => PMLA.str_at (hl_segs L) M' o (PML.SShort (s ++ [c])) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(o, 24)]).
Proof.
  intros LB FF LK cr A o c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Hlt & Ha0 & Ha1 & Hc & Hstr & Hdefo & (Ofr & O8 & Osh) & Hstksh) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh in *. change (256 + (16 + 4096)) with 4368 in *.
  destruct Hstr as (Hlen22 & Hb0 & Hbs).
  set (n := Z.of_nat (length s)) in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [n] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 n) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; clear - Hc; lia).
  assert (U32 : bv_unsigned (ev E0 32) = n) by (rewrite V32; apply u64_of_Z; unfold n in *; clear - Hlt; lia).

  assert (SCRV : CH.hd_scr F.HDECL = 4368) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr F.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr F.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= FT.NF)%nat) by (unfold FT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr F.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFx Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp F.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr F.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr F.HDECL) (CH.hd_scr F.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl FT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) FT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= FT.GLO /\ FT.GHI <= asc_got_hi C /\ 0 <= FT.GLO /\ FT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold FT.GLO, FT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : mem) (_ : Model) => True).
  assert (NOGOTO : forall i c0 kk ps j sg, CH2.is_leaf F.CPS F.TAGS i c0 kk ps (CC.TGoto j sg) -> False).
  { intros i c0 kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ SPS.leaf_f_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 990424 with (CC.cp_pc F.cp0) by vmc_refl.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN FT.NF E0 M model A LB FF LK sp F.HDECL WW WW F.BLS SPS.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            F.CPS K PMSA.fp_ok XI F.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact F.plans.
  - exact F.tags_ok.
  - exact SPS.heap_f_ok.
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c0 kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SPS.leaf_f_ok _ _ _ _ _ HIL) as X. unfold SPS.leaf_chk_f in X.
    apply andb_prop in X as [X Ynul]. apply andb_prop in X as [X Ychr]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yb0].
    apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
    apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
    assert (HagE : env_agree FT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN FT.NF E0 M model A LB FF LK sp F.HDECL WW WW F.BLS SPS.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              K DEF0 R r EV Hra Hraok SPS.RETPC 0%nat c0 ps0 _ Xbase _ (SPS.FFSF_nil 0%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact SPS.ret_at | rewrite SPS.FFSF_nil, YB; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB F.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.
    assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n0 Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
    assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
    assert (W11 : bv_unsigned (ev E' 11) = c) by (rewrite (FZ 11%nat eq_refl); exact U11).
    assert (W32 : bv_unsigned (ev E' 32) = n) by (rewrite (FZ 32%nat eq_refl); exact U32).
    assert (CELL : forall X0, SPS.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
    { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
    pose proof (CBA.amb_off L ar C HI HIok LYB FT.NF E0 M model A LB FF LK sp F.HDECL WW F.BLS SPS.FFS_F Cred 0 0%nat E A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    assert (LEN : Z.of_nat (length (s ++ [c])) = n + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (UON : bv_unsigned (edenot E' SPS.OPN) = o + n) by (unfold SPS.OPN, SPS.oE, SPS.nE; apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W10, ?W32; clear; lia | unfold n in *; clear - Hlt O3 O6; lia]).
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
    unfold PMLA.str_at, L5.lstr_short. rewrite LEN. split; [rewrite length_app; cbn [length]; unfold n in Hlt; clear - Hlt; lia|].
    split; [|split].
    + pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ o (CELL _ Yb0) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
      apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. replace (2 * (n + 1)) with (CL5A.uv E' (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) SPS.nE) (ELit 2))); [exact G0|].
      unfold CL5A.uv, SPS.nE. apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W32; clear; lia | unfold n in *; clear - Hlt; lia].
    + apply (CL5.bytes_at_app (hl_segs L)).
      * apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat (o + 1) s (CELL _ Yblob) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia) _)).
        rewrite <- (proj2 HagE'). reflexivity.
      * intros q Hq. cbn [length] in Hq. assert (q = 0%nat) by (clear - Hq; lia). subst q. cbn [nth]. rewrite Z.add_0_r. fold n.
        pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + 1 + n) (CELL _ Ychr) ltac:(unfold estart; cbn [a_base a_off]; rewrite UON; clear; lia)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, SPS.cE in G0. cbn [edenot] in G0. rewrite W11 in G0. exact G0.
    + replace (o + 1 + (n + 1)) with (o + n + 2) by (clear; lia).
      pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + n + 2) (CELL _ Ynul) ltac:(unfold estart; cbn [a_base a_off]; rewrite UON; clear; lia)) as G0.
      apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0.
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact Hdefo).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [apply regs_ok_id|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know F.cp0) in change (CC.cp_know F.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI FT.NF 0 NF32 FT.SCELLS FT.GLO FT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI FT.NF 0 NF32 FT.SCELLS FT.GLO FT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := o) (z := 2 * n); [ev0 | clear - O3; lia | clear - O6; lia | | unfold n in *; clear - Hlt; lia |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?U32; clear; lia | unfold n in *; clear - Hlt; lia].
      * apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hb0].
    + eapply CL5.krange_intro with (v := n); [lin_eval; rw_atoms; rewrite ?U32; clear; lia | unfold n in *; clear - Hlt; lia | unfold n in *; clear - Hlt; lia].
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev0 | unfold elenZ; cbn [edenot]; exact U32 | clear - O3; lia | unfold n in *; clear - Hlt O6; lia | clear - O6; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - O3; lia | unfold n in *; clear - Hlt O6; lia | apply (CL5A.visr_sub _ o 24 (o + 1) (Z.of_nat (length s)) VO ltac:(clear; lia) ltac:(unfold n in *; clear - Hlt; lia)) | exact Hbs].
      * apply (L5.defined_sub _ o 24 (o + 1) (Z.of_nat (length s)) DO ltac:(clear; lia) ltac:(unfold n in *; clear - Hlt; lia)).
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - Hc; lia | clear - Hc; lia].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 F.BLS []) with (@nil (expr * expr)). cbn [nth SPS.FFS_F app CHA.denF map length CH2.den].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; reflexivity | exact Hroom].
    + exact I.
  - exact Hfp.
Qed.

Lemma push_back_sgrow : forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r : Z) (s : list Z),
  PMSA.cps_asan L ar HI 990424 r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => Z.of_nat (length s) = 22 /\ PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ PMFCA.sso_nonul L M o s /\ L5.defined M o 24 /\
                  PMLA.fobj M FF o 24 /\ PMSA.stksh ar M sp PMSA.STR_SCR /\ acredit_ok L cr 48)
      (fun R M R' M' LB' cr' LBk W => exists p, PMLA.str_at (hl_segs L) M' o (PML.SLong 48 p (s ++ [c])) /\ PMLA.afresh L ar LB FF M' p 48 /\
                                                LB' = (p, 48) :: LB /\ cr' = adebit L cr 48 /\ LBk = LB /\ W = [(o, 24)]).
Proof.
  intros LB FF LK cr A o c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Heq & Ha0 & Ha1 & Hc & Hstr & Hdefo & (Ofr & O8 & Osh) & Hstksh & Hcred) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh in *. change (256 + (16 + 4096)) with 4368 in *.
  destruct Hstr as (Hlen22 & Hb0 & Hbs).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; clear - Hc; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4368) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFx Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  assert (OSHK : forall a, S o <= a < S o + 3 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold S in Ha; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    pose proof (SHR o 24 a ltac:(clear - O3; lia) ltac:(clear; lia) ltac:(clear - O6; lia) SH) as SRa. unfold hid in O5. clear - Hin SRa O5. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if Nat.eqb i 0 then cr1 = cr else cr1 = adebit L cr 48).
  set (AFP := fun (nb : Z) => ablock_range L ar nb 48 /\ blocks_apart nb 48 LB /\ fframes_apart nb 48 FF).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
               let nb := CL5A.uv E SPS.nbE in if Nat.eqb i 0 then True else AFP nb /\ L5.defined M1 nb 48 /\ shadow_blk M1 nb 48).

  assert (NOFOOT : forall LBown a, Forall (fun bb => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) LBown -> 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL WW LBown [] a).
  { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as G0. cbv beta in G0. clear - Hin Ha G0. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (NOGOTO : forall i c0 kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c0 kk ps (CC.TGoto j sg) -> False).
  { intros i c0 kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ SPS.leaf_g_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }

  assert (DEN : forall E, CH2.den E SPS.BNEW = [(CL5A.uv E SPS.nbE, 48)]).
  { intros E. unfold CH2.den, SPS.BNEW, SPS.nbE, CL5A.uv. cbn [map fst snd edenot]. rewrite (u64_of_Z 48) by (clear; lia). reflexivity. }

  assert (PRO : forall i1 : nat, (1 <= i1)%nat -> forall E A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SPS.FFS_G Cred 0 i1 E A1 M1 m1 ->
            XI i1 E A1 M1 m1 -> let nb := CL5A.uv E SPS.nbE in env_agree GT.NF E0 E /\ CHA.curF FF sp SPS.FFS_G i1 E = FF /\ AFP nb /\ L5.defined M1 nb 48 /\ shadow_blk M1 nb 48).
  { intros i1 Hi1 Ex Ax Mx mx HAx HXx. cbv zeta. split; [exact (proj1 (proj2 (proj2 (proj2 HAx))))|]. split; [unfold CHA.curF; rewrite SPS.FFSG_nil; reflexivity|].
    unfold XI in HXx. destruct (Nat.eqb i1 0) eqn:E1'; [apply Nat.eqb_eq in E1'; exfalso; clear - Hi1 E1'; lia|]. exact HXx. }
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 990424 with (CC.cp_pc G.cp0) by vmc_refl.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SPS.FFS_G Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SPS.heap_g_ok.
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c0 kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SPS.leaf_g_ok _ _ _ _ _ HIL) as X. unfold SPS.leaf_chk_g in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SPS.FFS_G Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X XK]. apply andb_prop in X as [X YFOOT]. apply andb_prop in X as [YBi YBj]. apply CH2.blocks_eqb_eq in YBi, YBj.
      destruct (Z.eqb_spec pc SPS.PC_OPNEW) as [->|Hne1].
      {
        cbv zeta in XK. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := SPS.news_of (nx + 4) cj) in *.
        apply andb_prop in XK as [XK Y10]. apply andb_prop in XK as [XK YNEWS]. apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK YF]. apply andb_prop in XK as [XK YN]. apply andb_prop in XK as [XK Yj].
        apply andb_prop in XK as [Y0 Yi]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj, YN. subst i j.
        lazymatch type of Y5 with SPS.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB LB G.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity).
        assert (HcF : CHA.curF FF sp SPS.FFS_G 0%nat E = FF) by reflexivity.
        refine (CALLEE SPS.PC_OPNEW 4112 0%nat [] [] news None 0 0%nat c0 ps0 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !SPS.FFSG_nil, YBi, YBj; cbn [SPS.BLKS]; exact Hchk | rewrite !SPS.FFSG_nil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (NXeq : CH2.ci_nx ci = 40%nat) by (destruct HV as (_ & _ & _ & _ & HV5); clear - HV5 YN; unfold nx, APC.NCS in *; lia).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 48 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|].
        split; [split; [exact (REG 10%nat (ELit 48) 48 Y10 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia)) | split; [clear; lia | exact Hcred]]|].
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (clear - NQ5 NQ7 NQ3; lia).
        assert (Hvu : CL5A.uv E2 SPS.nbE = u).
        { unfold CL5A.uv, SPS.nbE. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite NXeq in G0 |- *. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        split; [apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS 1%nat E2 = (u, 48) :: LB) by (unfold CHA.curB; rewrite YBj; cbn [SPS.BLKS]; rewrite (DEN E2), Hvu; reflexivity).
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
        split; [unfold XI; cbn [Nat.eqb]; rewrite Hvu; split; [split; [exact Hrng | split; [exact Hbap | exact Hfap]]|]; split; [exact Hdef | exact Hsh]|].
        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7028736 LYHN GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps0) [] [] 44%nat (ELit 48) M' M2 A1 A2 m' m2 LB ((u, 48) :: LB) FF FF LK1 LK2 cr (adebit L cr 48) u 48 news
                  HagE' Hag2 HK HH1 _ eq_refl Hvu _ _ Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0); [reflexivity | rewrite NXeq; reflexivity | unfold elenZ; cbn [edenot]; apply u64_of_Z; clear; lia | rewrite NXeq; rewrite YN in YNEWS; exact YNEWS]. }
      destruct (Z.eqb_spec pc SPS.PC_MM) as [->|Hne2]; [|exfalso; clear - XK; discriminate XK].
      {
        apply andb_prop in XK as [XK Yblob]. apply andb_prop in XK as [XK Y12]. apply andb_prop in XK as [XK Y11]. apply andb_prop in XK as [XK Y10].
        apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK Ynx]. apply andb_prop in XK as [XK YF]. apply andb_prop in XK as [XK Yj]. apply andb_prop in XK as [Y0 Yi].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj. apply Nat.leb_le in Ynx. subst i j.
        lazymatch type of Y5 with SPS.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (PRO 1%nat ltac:(clear; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF & HSB). set (nb := CL5A.uv E SPS.nbE) in *.
        pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in Q6.
        assert (HcB : CHA.curB LB G.BLS 1%nat E = (nb, 48) :: LB) by (unfold CHA.curB; rewrite YBi; cbn [SPS.BLKS]; rewrite (DEN E); reflexivity).
        refine (CALLEE SPS.PC_MM 2560 0%nat SPS.BNEW [(SPS.nbE, 0, ELit 22)] SPS.NEWS_MM (Some SPS.nbE) 0 1%nat c0 ps0 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !SPS.FFSG_nil, YBi, YBj; cbn [SPS.BLKS]; exact Hchk | rewrite !SPS.FFSG_nil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP0 & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 48) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (NB' : CL5A.uv E' SPS.nbE = nb) by (unfold nb, CL5A.uv, SPS.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
        assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold CL5A.uv, SPS.nbE in NB'; cbn [edenot] in NB'; exact NB').
        assert (CELL : forall X0, SPS.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SPS.FFS_G Cred 0 1%nat E A1 M' m' HA') as Hoff.
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        assert (HF2 : Forall (fun bb : Z * Z => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) [(nb, 48)]) by (constructor; [cbn [fst snd]; exact Q6 | constructor]).
        assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SPS.FFS_G Cred 0 STKF SCRP NF32 U2 WRS_OK
                    1%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite SPS.FFSG_nil, YBi; exact YFOOT|].
          rewrite SPS.FFSG_nil, YBi. cbn [SPS.BLKS]. rewrite (DEN E). exact (NOFOOT _ a HF2 SRa). }
        assert (HSB' : shadow_blk M' nb 48).
        { apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB].
          intros a Ha. exact (FRS nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha). }
        assert (OSH' : shadow_zero M' o 3).
        { apply (CL5A.shadow_zero_same M M'); [|exact Osh]. intros j0 Hj0. exact (Hfr1 (S o + j0) (OSHK (S o + j0) ltac:(clear - Hj0; lia))). }
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (LENST : length s = Z.to_nat 22) by (clear - Heq; lia).
        eexists. eexists. split.
        { exact (CRC.memcpy_cps L ar HI PMSA.fp_ok SPS.PC_MM MEMMOVE_LIBC 2560 ((nb, 48) :: LB) FF LK1 (adebit L cr 48) A1 nb (o + 1) 22 (map (Z_to_bv 8) s) (sp + CH2.ci_csp ci) (CC.cp_pc cj)
                   ltac:(rewrite SCRMEM; clear; lia)). }
        split.
        { unfold CRC.memcpy_pre.
          split; [exact (REG 10%nat _ nb Y10 W44)|].
          split; [exact (REG 11%nat _ (o + 1) Y11 ltac:(apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W10; clear; lia | clear - O3 O6; lia]))|].
          split; [exact (REG 12%nat _ 22 Y12 ltac:(cbn [edenot]; apply u64_of_Z; clear; lia))|].
          split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb 48 nb 22 HH1 (or_introl eq_refl) HSB' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))|].
          split.
          - refine (src_in_fobj _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 o 1 22 (map (Z_to_bv 8) s) HH1 Ofr O8 OSH' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) _).
            rewrite <- LENST. apply (L5C.bytes_at_rdn (hl_segs L) M' s (o + 1) ltac:(clear - O3; lia) ltac:(clear - O6 Heq; lia)).
            apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat (o + 1) s (CELL _ Yblob) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
          - destruct Ofr as (f & Hf & F1 & F2). pose proof (Hfap f Hf) as AP. clear - AP F1 F2. lia. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta.
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (NB2 : CL5A.uv E2 SPS.nbE = nb) by (unfold CL5A.uv, SPS.nbE; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Ynx; lia); exact W44).
          assert (T44 : bv_unsigned (ev E2 44) = nb) by (unfold CL5A.uv, SPS.nbE in NB2; cbn [edenot] in NB2; exact NB2).
          split; [unfold SPS.nbE; cbn [edenot]; rewrite Ha0', <- T44; apply Z_to_bv_bv_unsigned|].
          split; [rewrite (DEN E'), NB'; apply incl_refl|].
          split.
          { intros w a [<-|[]] Hin. exists (SPS.nbE, 0, ELit 22). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. change (bv_unsigned (edenot E' SPS.nbE)) with (CL5A.uv E' SPS.nbE). rewrite NB'.
            cbn [edenot]. rewrite u64_of_Z by (clear; lia). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
            refine (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb 48 a RFx (conj Q5 (conj Q6 Q7)) ltac:(clear; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 _ Hfap (or_introl _) Kc).
            - exact Hbap.
            - clear - Hin. lia. }
          split; [unfold CHA.curB; rewrite YBj; cbn [SPS.BLKS]; rewrite (DEN E2), NB2; exact HH2|].
          split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
          pose proof HP as (HP1 & HP2 & HP3).

          assert (GB2 : forall q, (q < length s)%nat -> M2 (Z_to_bv 64 (nb + Z.of_nat q)) = Some (Z_to_bv 8 (nth q s 0))).
          { intros q Hq. destruct (Hnew (Z.of_nat q) ltac:(clear - Hq LENST Heq; lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id, nth_error_map in Hnth.
            destruct (nth_error s q) as [z|] eqn:Ez; [|discriminate Hnth]. cbn [option_map] in Hnth. assert (Hz : Z_to_bv 8 z = Z_to_bv 8 v) by congruence. rewrite (@nth_error_nth _ s q z 0 Ez).
            unfold byte_at in Hb. rewrite Hb, <- Hz. reflexivity. }
          split.
          { unfold XI. cbn [Nat.eqb]. rewrite NB2. split; [exact HAFP|]. split.
            - intros q Hq. apply (HP3 (nb + q)); [clear - Hq Q0 Q7; lia | left; exists (nb, 48); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] |].
              apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF q Hq).
            - apply (PTA.shadow_blk_ag M' M2 (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB'].
              intros a Ha. pose proof (SHR nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
              apply HP1. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 48); split; [left; reflexivity | exact Ha]|].
              intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin SRa Q6. lia. }

          intros X0 HX0 _. unfold SPS.NEWS_MM, SPS.STAT, SPS.nbE in HX0. cbn [app In] in HX0.
          destruct HX0 as [<-|[<-|[<-|[]]]]; [apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity
                                         | apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity |].
          assert (VNB : CL5A.visr (ahid A2 m2) nb 22).
          { intros q Hq. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (nb + q) HH2); [clear - Hq Q0 Q7; lia | left; exists (nb, 48); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] |].
            intros Hc'. exfalso. pose proof (SHR (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) _ ltac:(clear - CL; lia) ltac:(clear - S2 S3 SP1; lia) ltac:(clear; lia) Hc') as SRa. clear - SRa Q6 Hq. lia. }
          eapply CL5.kblob_intro with (A := nb) (bs := s); [unfold estart; cbn [a_base a_off edenot]; rewrite T44; clear; lia | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by (clear; lia); clear - Heq; lia | clear - Q0; lia | clear - Q7 Heq; lia | clear - Q7; lia
                                                           | rewrite <- (proj2 HagE2); reflexivity | |].
          - apply (CL5A.bytes_vis (hl_segs L)); [clear - Q0; lia | clear - Q7 Heq; lia | rewrite Heq; exact VNB |].
            intros q Hq. unfold L5.u8_at. cbn [rdn]. rewrite (GB2 q Hq). reflexivity.
          - apply (CL5A.defined_vis _ M2 nb (Z.of_nat (length s))); [rewrite Heq; exact VNB|]. intros q Hq. rewrite <- (Z2Nat.id q) by (clear - Hq; lia). rewrite (GB2 (Z.to_nat q) ltac:(clear - Hq; lia)). discriminate. } }
    +
      apply andb_prop in X as [X Ynul]. apply andb_prop in X as [X Ychr]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0].
      apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
      apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      destruct (PRO 2%nat ltac:(clear; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF & HSB). set (nb := CL5A.uv E SPS.nbE) in *.
      pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in Q6.
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SPS.FFS_G Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok SPS.RETPC 2%nat c0 ps0 _ Xbase _ (SPS.FFSG_nil 2%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact SPS.ret_at | rewrite SPS.FFSG_nil, YB; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = adebit L cr 48) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS 2%nat E = (nb, 48) :: LB) by (unfold CHA.curB; rewrite YB; cbn [SPS.BLKS]; rewrite (DEN E); reflexivity). rewrite HB in HH1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W11 : bv_unsigned (ev E' 11) = c) by (rewrite (FZ 11%nat eq_refl); exact U11).
      assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold nb, CL5A.uv, SPS.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
      assert (CELL : forall X0, SPS.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SPS.FFS_G Cred 0 2%nat E A1 M' m' HA') as Hoff.
      rewrite SCRV in HP.
      assert (LEN : Z.of_nat (length (s ++ [c])) = 23) by (rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.to_nat]; clear - Heq; lia).
      apply (Hcont fx' R' M' model2 ((nb, 48) :: LB) (adebit L cr 48) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      exists nb. split.
      {   unfold PMLA.str_at, L5.lstr_long. rewrite LEN. split; [|split; [reflexivity | clear; lia]].
        split; [reflexivity|].
        split; [|split; [|split; [|split]]].
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite u64_of_Z in G0 by (clear; lia). exact G0.
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite u64_of_Z in G0 by (clear; lia). exact G0.
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(unfold estart, SPS.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv, SPS.nbE in G0. cbn [edenot] in G0. rewrite W44 in G0. exact G0.
        - apply (CL5.bytes_at_app (hl_segs L)).
          + apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat nb s (CELL _ Yblob) ltac:(unfold estart, SPS.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
          + intros q Hq. cbn [length] in Hq. assert (q = 0%nat) by (clear - Hq; lia). subst q. cbn [nth]. rewrite Z.add_0_r. rewrite Heq.
            pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (nb + 22) (CELL _ Ychr) ltac:(unfold estart, SPS.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia)) as G0.
            apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, SPS.cE in G0. cbn [edenot] in G0. rewrite W11 in G0. exact G0.
        - pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (nb + 23) (CELL _ Ynul) ltac:(unfold estart, SPS.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia)) as G0.
          apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0. }
      split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
      unfold PMLA.afresh. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split.
      { intros q Hq. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF q Hq). }
      apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB]. intros a Ha.
      pose proof (SHR nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
      refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SPS.FFS_G Cred 0 STKF SCRP NF32 U2 WRS_OK
                2%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite SPS.FFSG_nil, YB; exact Xfoot|].
      rewrite SPS.FFSG_nil, YB. cbn [SPS.BLKS]. rewrite (DEN E). apply (NOFOOT _ a); [constructor; [cbn [fst snd]; exact Q6 | constructor] | exact SRa].
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact Hdefo).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [apply regs_ok_id|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := o) (z := 44); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia |].
      rewrite Heq in Hb0. apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hb0].
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev0 | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by (clear; lia); clear - Heq; lia | clear - O3; lia | clear - Heq O6; lia | clear - O6; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - O3; lia | clear - Heq O6; lia | apply (CL5A.visr_sub _ o 24 (o + 1) (Z.of_nat (length s)) VO ltac:(clear; lia) ltac:(clear - Heq; lia)) | exact Hbs].
      * apply (L5.defined_sub _ o 24 (o + 1) (Z.of_nat (length s)) DO ltac:(clear; lia) ltac:(clear - Heq; lia)).
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - Hc; lia | clear - Hc; lia].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with (@nil (expr * expr)). cbn [nth SPS.FFS_G app CHA.denF map length CH2.den].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity | exact Hroom].
    + exact I.
  - exact Hfp.
Qed.

Theorem str_push_back_short_ok : PMFCA.str_push_back_short_specA L ar HI 990424.
Proof.
  intros LB FF LK cr A o c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hc & Hstr & Hdefo & Hobj & Hstksh & Hcredit) Hcont.
  assert (LEN : Z.of_nat (length (s ++ [c])) = Z.of_nat (length s) + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
  pose proof Hstr as (Hl22 & _).
  destruct (Z_lt_le_dec (Z.of_nat (length s)) 22) as [Hlt|Hge].
  - apply (push_back_sfast LB FF LK cr A o c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hst & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. split; [|split; [exact HLBk | exact HW]]. left.
    split; [rewrite LEN; clear - Hlt; lia|]. split; [exact Hst|]. split; [|split; [exact HLB | exact Hcr]].
    destruct Hobj as (Ofr & _ & _). destruct Ofr as (f & Hf & F1 & F2).
    destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia.
  - assert (Heq : Z.of_nat (length s) = 22) by (clear - Hge Hl22; lia).
    apply (push_back_sgrow LB FF LK cr A o c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
    { split; [exact Heq|]. repeat (split; [assumption|]). apply Hcredit. exact Heq. }
    intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hst & Hfr & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP); [|assumption..]. split; [|split; [exact HLBk | exact HW]]. right. exists p'. rewrite LEN.
    split; [clear - Heq; lia|]. split; [exact Hst|]. split; [|split; [exact Hfr | split; [exact HLB | exact Hcr]]].
    destruct Hobj as (Ofr & _ & _). destruct Ofr as (f & Hf & F1 & F2).
    destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia.
Qed.

Theorem str_push_back_l48_ok : PMFCA.str_push_back_l48_specA L ar HI 990424.
Proof.
  intros LB FF LK cr A o p c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hc & Hstr & Hlt47 & HinLB & Hshb & (Ofr & O8 & Osh) & Hstksh) Hcont.
  set (cap := 48) in *.
  assert (Hlt : Z.of_nat (length s) + 1 < cap) by (unfold cap; clear - Hlt47; lia).
  assert (H24 : 24 <= cap) by (unfold cap; clear; lia).
  assert (Hlen : Z.of_nat (length s) < 2 ^ 26) by (clear - Hlt47; lia).
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh, PMSA.fobj, PMSA.str_at, PMSA.afresh in *. change (256 + (16 + 4096)) with 4368 in *.
  destruct Hstr as (Hw0 & Hw8 & Hw16 & Hbs).
  assert (Hbit : Z.testbit (cap + 1) 0 = true) by reflexivity. assert (Hc8 : cap mod 8 = 0) by reflexivity.
  assert (Hslt : Z.of_nat (length s) < cap) by (clear - Hlt; lia).
  set (size := Z.of_nat (length s)) in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (p, cap) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7. change (hid (p + cap <= 2147446784 \/ 17594333495296 <= p)) in B6.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (RFr : CHA.rng_facts L ar (lb_remove p LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove p y LB Hy) | apply incl_refl]. }
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by (clear; lia); clear - H; lia).

  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size; p] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 k) by reflexivity. assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; clear - Hc; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; clear - Hk B0 B3 B7; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; clear - B0 B3 B7; lia).
  assert (UCAP : forall E1, env_agree FLT.NF E0 E1 -> bv_unsigned (edenot E1 SPF.CAP) = cap).
  { intros E1 HagE. unfold SPF.CAP, SPF.kE. apply CL5.u_lin; [lin_eval; rw_atoms|]; rewrite <- ?(proj1 HagE 32%nat) by (apply Nat.ltb_lt; reflexivity); rewrite ?U32; clear - Hk B3 B7 B0; lia. }

  assert (SCRV : CH.hd_scr FL.HDECL = 4368) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr FL.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr FL.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= FLT.NF)%nat) by (unfold FLT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove p LB) FF sp (CH.hd_scr FL.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove p LB) FF sp _ o 24 a RFr Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs FL.HDECL) -> SGP.region_vars_lt FLT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs FL.HDECL) -> SGP.region_vars_lt FLT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove p LB) FF sp FL.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar (lb_remove p LB) FF sp (CH.hd_scr FL.HDECL) o 24 a RFr Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img FL.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr FL.HDECL) (CH.hd_scr FL.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl FLT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) FLT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= FLT.GLO /\ FLT.GHI <= asc_got_hi C /\ 0 <= FLT.GLO /\ FLT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold FLT.GLO, FLT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) => shadow_blk M1 p cap).
  assert (KSTK : forall a, S (sp - 4368) <= a < S (sp - 4368) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 4368)) / 8 -> CHA.akept L ar (lb_remove p LB) FF sp (CH.hd_scr FL.HDECL) WW a).
  { intros a Ha. assert (AL4368 : (sp - 4368) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 4368) with ((2 * (sp / 16) - 546) * 8) by lia; apply Z_mod_mult).
    destruct (PTA.stksh_rng ar sp 4368 a ltac:(clear - S2; lia) AL4368 C8 (proj2 SP1) TOP47 ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [right; right; right; right; left; exact G2|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    unfold in_shadow_of, S, SB in G2. unfold hid in O5. clear - Hin G2 O5 CL. lia. }

  assert (NOFOOT : forall LBown a, Forall (fun bb => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) LBown -> 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp FL.HDECL WW LBown [] a).
  { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as G0. cbv beta in G0. clear - Hin Ha G0. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (NOGOTO : forall i c0 kk ps j sg, CH2.is_leaf FL.CPS FL.TAGS i c0 kk ps (CC.TGoto j sg) -> False).
  { intros i c0 kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ SPF.leaf_f_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }

  assert (DEN1 : forall E, env_agree FLT.NF E0 E -> CH2.den E SPF.BOLD = [(p, cap)]).
  { intros E HagE. unfold CH2.den, SPF.BOLD, SPF.pE. cbn [map fst snd]. f_equal. f_equal; [cbn [edenot]; rewrite <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity); exact U34 | exact (UCAP E HagE)]. }
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; unfold size; clear - Hlen; lia).
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 990424 with (CC.cp_pc FL.cp0) by vmc_refl.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN FLT.NF E0 M model A (lb_remove p LB) FF LK sp FL.HDECL WW WW FL.BLS SPF.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            FL.CPS K PMSA.fp_ok XI FL.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact FL.plans.
  - exact FL.tags_ok.
  - exact SPF.heap_f_ok.
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c0 kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SPF.leaf_f_ok _ _ _ _ _ HIL) as X. unfold SPF.leaf_chk_f in X.
    apply andb_prop in X as [X Ynul]. apply andb_prop in X as [X Ychr]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0].
    apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
    apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
    assert (HagE : env_agree FLT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    assert (HSB : shadow_blk M1 p cap) by exact HXi.
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN FLT.NF E0 M model A (lb_remove p LB) FF LK sp FL.HDECL WW WW FL.BLS SPF.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              K DEF0 R r EV Hra Hraok SPF.RETPC 0%nat c0 ps0 _ Xbase _ (SPF.FFSF_nil 0%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact SPF.ret_at | rewrite SPF.FFSF_nil, YB; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB (lb_remove p LB) FL.BLS 0%nat E = (p, cap) :: lb_remove p LB) by (unfold CHA.curB; rewrite YB; rewrite (DEN1 E HagE); reflexivity). rewrite HB in HH1.
    assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
    assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
    assert (W11 : bv_unsigned (ev E' 11) = c) by (rewrite (FZ 11%nat eq_refl); exact U11).
    assert (W33 : bv_unsigned (ev E' 33) = size) by (rewrite (FZ 33%nat eq_refl); exact U33).
    assert (W34 : bv_unsigned (ev E' 34) = p) by (rewrite (FZ 34%nat eq_refl); exact U34).
    assert (CELL : forall X0, SPF.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
    { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
    pose proof (CBA.amb_off L ar C HI HIok LYB FLT.NF E0 M model A (lb_remove p LB) FF LK sp FL.HDECL WW FL.BLS SPF.FFS_F Cred 0 0%nat E A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    assert (LEN : Z.of_nat (length (s ++ [c])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (USP : bv_unsigned (edenot E' (EAlu Instr.ALU_ADD SPF.szE SPF.pE)) = size + p) by (unfold SPF.szE, SPF.pE; apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W33, ?W34; clear; lia | unfold size in *; clear - Hlen Hlt B0 B7; lia]).
    apply (Hcont fx' R' M' model2 LB cr (lb_remove p LB) WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact (CBA.own_back L ar C HI HIok _ _ _ _ _ _ _ p cap HH1 HinLB ND1)].
    split.
    {   unfold PMLA.str_at, L5.lstr_long. rewrite LEN. split; [|split; [exact Hc8 | clear - Hlt; unfold size in *; lia]].
      split; [exact Hbit|]. split; [|split; [|split; [|split]]].
      - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(unfold estart, SPF.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
        replace (CL5A.uv E' (EAlu Instr.ALU_ADD SPF.CAP (ELit 1))) with (cap + 1) in G0; [exact G0|]. symmetry. unfold SPF.CAP, SPF.kE.
        apply CL5.u_lin; [lin_eval; rw_atoms|]; rewrite <- ?(proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); rewrite ?U32; clear - Hk H24 B7 B3 B0; lia.
      - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(unfold estart, SPF.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
        replace (CL5A.uv E' (EAlu Instr.ALU_ADD SPF.szE (ELit 1))) with (size + 1) in G0; [exact G0|]. symmetry. unfold SPF.szE.
        apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W33; clear; lia | unfold size in *; clear - Hlen; lia].
      - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(unfold estart, SPF.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
        unfold CL5A.uv, SPF.pE in G0. cbn [edenot] in G0. rewrite W34 in G0. exact G0.
      - apply (CL5.bytes_at_app (hl_segs L)).
        + apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat p s (CELL _ Yblob) ltac:(unfold estart, SPF.pE; cbn [a_base a_off edenot]; rewrite W34; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
        + intros q Hq. cbn [length] in Hq. assert (q = 0%nat) by (clear - Hq; lia). subst q. cbn [nth]. rewrite Z.add_0_r. fold size.
          pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (p + size) (CELL _ Ychr) ltac:(unfold estart; cbn [a_base a_off]; rewrite USP; clear; lia)) as G0.
          apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, SPF.cE in G0. cbn [edenot] in G0. rewrite W11 in G0. exact G0.
      - replace (p + (size + 1)) with (p + size + 1) by (clear; lia).
        pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (p + size + 1) (CELL _ Ynul) ltac:(unfold estart; cbn [a_base a_off]; rewrite USP; clear; lia)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0. }
    split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
    apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of p cap a)); [| clear - H24; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ B16) | exact HSB]. intros a Ha.
    pose proof (SHR p cap a ltac:(clear - B0; lia) ltac:(clear - H24; lia) B7 Ha) as SRa.
    refine (CBA.leaf_frame L ar C HI HIok FLT.NF E0 M model A (lb_remove p LB) FF LK sp FL.HDECL WW WW FL.BLS SPF.FFS_F Cred 0 STKF SCRP NF32 U2 WRS_OK
              0%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite SPF.FFSF_nil, YB; exact Xfoot|].
    rewrite SPF.FFSF_nil, YB. rewrite (DEN1 E HagE). apply (NOFOOT _ a); [constructor; [cbn [fst snd]; unfold hid in B6; exact B6 | constructor] | exact SRa].
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VB : CL5A.visr (ahid A model) p cap).
    { intros q Hq. apply CLV; [clear - Hq B0 B7; lia | left; exists (p, cap); split; [exact HinLB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. unfold hid in B6. clear - Hq B6. lia. }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact (DEFO _ _ _ _ _ _ HH)).
    assert (DB : L5.defined Mv p cap) by (apply (CL5A.defined_vis _ M p cap VB); exact Bdef).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (U64V : forall q z, 0 <= q -> q + 8 <= 24 -> L5.u64_at (hl_segs L) M (o + q) z -> L5.u64_at (hl_segs L) Mv (o + q) z).
    { intros q z K0 K1 Hq. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ o 24 (o + q) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hq]. }
    split; [apply regs_ok_id|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know FL.cp0) in change (CC.cp_know FL.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI FLT.NF 0 NF32 FLT.SCELLS FLT.GLO FLT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI FLT.NF 0 NF32 FLT.SCELLS FLT.GLO FLT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev0 | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal.
      * replace o with (o + 0) by (clear; lia). apply (U64V 0); [clear; lia | clear; lia | rewrite Z.add_0_r; exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev0 | clear - O3; lia | clear - O6; lia | |].
      * exact V33.
      * apply (U64V 8); [clear; lia | clear; lia | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev0 | clear - O3; lia | clear - O6; lia | exact V34 | apply (U64V 16); [clear; lia | clear; lia | exact Hw16]].
    + eapply CL5.krange_intro with (v := k); [lin_eval; rw_atoms; clear; lia | clear - Hk H24 B5 B7; lia | clear - Hk H24 B5 B7; lia].
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - Hc; lia | clear - Hc; lia].
    + eapply CL5.krange_intro with (v := size); [lin_eval; rw_atoms; clear; lia | unfold size; clear - Hlen; lia | unfold size; clear - Hlen; lia].
    + eapply CL5.krange_intro with (v := cap - 2 - size); [lin_eval; rw_atoms; clear - Hk; lia | unfold size in *; clear - Hlt B5 B7; lia | unfold size in *; clear - Hlt B5 B7; lia].
    + eapply CL5.kblob_intro with (bs := s) (A := p); [ev0 | exact U33 | clear - B0; lia | clear - B7 Hlt; unfold size in *; lia | clear - B0 B7 B3; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - B0; lia | clear - B7 Hlt; unfold size in *; lia | apply (CL5A.visr_sub _ p cap p (Z.of_nat (length s)) VB ltac:(clear; lia) ltac:(clear - Hlt; unfold size in *; lia)) | exact Hbs].
      * apply (L5.defined_sub _ p cap p (Z.of_nat (length s)) DB ltac:(clear; lia) ltac:(clear - Hlt; unfold size in *; lia)).
    + eapply CL5.kunk_intro with (A := p) (N := cap); [ev0 | unfold elenZ; exact (UCAP E0 (CC.env_agree_refl _ _)) | clear - B0; lia | clear - B7; lia | clear - B0 B7 B3; lia | exact DB].
    + eapply CL5.kwr_intro with (A := p) (N := cap); [ev0 | unfold elenZ; exact (UCAP E0 (CC.env_agree_refl _ _)) | clear - B0; lia | clear - B7; lia | clear - B0 B7 B3; lia | exact DB].
    + eapply CL5.krange_intro with (v := p); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - B0 B7 B3; lia].
    + eapply CL5.kalign_intro with (v := p); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := p) (N2 := cap); [ev0 | reflexivity | ev0 | unfold elenZ; exact (UCAP E0 (CC.env_agree_refl _ _)) | clear - B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := p) (N2 := cap); [ev0 | reflexivity | ev0 | unfold elenZ; exact (UCAP E0 (CC.env_agree_refl _ _)) |].
      destruct Ofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. clear - QF F1 F2. lia.
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 FL.BLS []) with SPF.BOLD. rewrite (DEN1 E0 (CC.env_agree_refl _ _)). cbn [nth SPF.FFS_F app CHA.denF map length].
      split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ p cap HH HinLB)|]. split; [apply incl_refl|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity | exact Hroom].
    + unfold XI. cbn [Nat.eqb]. exact Hshb.
  - exact Hfp.
Qed.

End StrPushShortOk.
