(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB EncMemXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_str_push_back_x_sso_xboth_T Cut_str_push_back_x_sso_xboth Cut_str_push_back_x_sso_full_xboth_T Cut_str_push_back_x_sso_full_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module F := Cut_str_push_back_x_sso_xboth.  Module FT := Cut_str_push_back_x_sso_xboth_T.
Module G := Cut_str_push_back_x_sso_full_xboth.  Module GT := Cut_str_push_back_x_sso_full_xboth_T.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.

Module EPSA.
Definition PC_OPNEW : Z := 1429232.    (* [comment removed for export] *)
Definition PC_MM : Z := 527112.        (* [comment removed for export] *)
Definition RETPC : Z := 1056308.        (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition cE := EVar 11. Definition nE := EVar 32. Definition nbE := EVar 44.
Definition onE : expr := EAlu Instr.ALU_ADD oE nE.                                                       (* [comment removed for export] *)
Definition BNEW : list (expr * expr) := [(nbE, ELit 48)].
Definition BLKS (i : nat) : list (expr * expr) := match i with 0%nat => [] | _ => BNEW end.
Definition FFS_F : list (list (expr * Z * Z)) := map (fun _ => []) F.CPS.
Definition FFS_G : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1497016) 8 (ELit SBz)].
Definition NEWS_MM : list kentry := STAT ++ [KBlob (SA nbE 0) (ELit 22) 0].
Definition CPF0 : list SGP.region := [(EVar 2, -4368, ELit 4368); (oE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, ELit 48)].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition leaf_chk_f (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (Z.eqb pc RETPC && Nat.eqb i 0 && CBA.exit_base_chk FT.NF RETPC c ps && CHA.foot_chk FT.NF F.HDECL c [] [] && CH2.blocks_eqb (nth i F.BLS []) []
       && CBA.regions_eqb (CC.cp_F c) CPF0 && Nat.leb 40 (CC.cp_nx c)
       && has cells (KWord (SA oE 0) 1 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) nE) (ELit 2))) && has cells (KBlob (SA oE 1) nE 0)
       && has cells (KWord (SA onE 1) 1 cE) && has cells (KWord (SA onE 2) 1 (ELit 0)))%bool
  end.
(* [comment removed for export] *)
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
                 && CRB.fresh_news_ok 65536 7094272 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (ELit 48) news
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
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_g_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk_g = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_f_ok : CHA.heap_chkA FT.NF F.HDECL F.BLS FFS_F F.CPS F.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_g_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS_G G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma FFSF_nil : forall i, nth i FFS_F [] = [].
Proof. intros i. unfold FFS_F. do 2 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma FFSG_nil : forall i, nth i FFS_G [] = [].
Proof. intros i. unfold FFS_G. do 4 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
End EPSA.
Section PushBackS.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Variable onmax : Z.
Hypothesis OPNEW_OK : PMESA.opnew_x_specA L ar HI onmax EPSA.PC_OPNEW.             (* [comment removed for export] *)
Hypothesis MEMMOVE_LIBC : PMESA.amemcpy_x_spec_at L ar HI onmax EPSA.PC_MM false.   (* [comment removed for export] *)

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

(* [comment removed for export] *)
Lemma push_back_sso_x : forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r : Z) (s : list Z),
  PMSA.cps_asan L ar HI 1056004 r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => Z.of_nat (length s) <= 21 /\ PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ PMSA.str_at L M o (PML.SShort s) /\
                  PMSA.fobj M FF o 24 /\ PMSA.stksh ar M sp PMSA.STR_SCR)
      (fun R M R' M' LB' cr' LBk W => PMSA.str_at L M' o (PML.SShort (s ++ [c])) /\ L5.defined M' o 24 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(o, 24)]).
Proof.
  intros LB FF LK cr A o c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Hle & Ha0 & Ha1 & Hc & Hstr & (Ofr & O8 & Osh) & Hstksh) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh, PMSA.fobj, PMSA.str_at, PMSA.afresh in *. change (256 + (16 + 4096)) with 4368 in *.
  destruct Hstr as (Hl22 & Hb0 & Hbs & Hnul).
  set (size := Z.of_nat (length s)) in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7094272 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.
  (* [comment removed for export] *)
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  (* [comment removed for export] *)
  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [size] 0))) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 size) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; clear - Hc; lia).
  assert (U32 : bv_unsigned (ev E0 32) = size) by (rewrite V32; apply u64_of_Z; unfold size; clear - Hle; lia).
  (* [comment removed for export] *)
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
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img F.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr F.HDECL) (CH.hd_scr F.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl FT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) FT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= FT.GLO /\ FT.GHI <= asc_got_hi C /\ 0 <= FT.GLO /\ FT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold FT.GLO, FT.GHI. clear. lia. }
  (* [comment removed for export] *)
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : mem) (_ : Model) => True).
  assert (NOGOTO : forall i c0 kk ps j sg, CH2.is_leaf F.CPS F.TAGS i c0 kk ps (CC.TGoto j sg) -> False).
  { intros i c0 kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ EPSA.leaf_f_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 1056004 with (CC.cp_pc F.cp0) by (vm_compute; reflexivity).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN FT.NF E0 M model A LB FF LK sp F.HDECL WW WW F.BLS EPSA.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            F.CPS K PMSA.fp_ok XI F.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact F.plans.
  - exact F.tags_ok.
  - exact EPSA.heap_f_ok.
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - (* [comment removed for export] *)
    intros i c0 kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ EPSA.leaf_f_ok _ _ _ _ _ HIL) as X. unfold EPSA.leaf_chk_f in X.
    apply andb_prop in X as [X Ynul]. apply andb_prop in X as [X Ychr]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yw0].
    apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
    apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
    assert (HagE : env_agree FT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN FT.NF E0 M model A LB FF LK sp F.HDECL WW WW F.BLS EPSA.FFS_F Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              K DEF0 R r EV Hra Hraok EPSA.RETPC 0%nat c0 ps0 _ Xbase _ (EPSA.FFSF_nil 0%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact EPSA.ret_at | rewrite EPSA.FFSF_nil, YB; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB F.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.
    assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
    assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
    assert (W11 : bv_unsigned (ev E' 11) = c) by (rewrite (FZ 11%nat eq_refl); exact U11).
    assert (W32 : bv_unsigned (ev E' 32) = size) by (rewrite (FZ 32%nat eq_refl); exact U32).
    assert (CELL : forall X0, EPSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
    { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
    pose proof (CBA.amb_off L ar C HI HIok LYB FT.NF E0 M model A LB FF LK sp F.HDECL WW F.BLS EPSA.FFS_F Cred 0 0%nat E A1 M' m' HA') as Hoff.
    rewrite SCRV in HP.
    assert (LEN : Z.of_nat (length (s ++ [c])) = size + 1) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    assert (UON : bv_unsigned (edenot E' EPSA.onE) = o + size) by (unfold EPSA.onE, EPSA.oE, EPSA.nE; apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W10, ?W32; clear; lia | clear - Hle O3 O6; unfold size in *; lia]).
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split.
    { (* [comment removed for export] *) unfold PMLA.str_at, L5.lstr_short. rewrite LEN. split; [rewrite length_app; cbn [length]; clear - Hle; unfold size in *; lia|]. split; [|split].
      - pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ o (CELL _ Yw0) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) EPSA.nE) (ELit 2))) with (2 * (size + 1)) in G0; [exact G0|].
        symmetry. unfold EPSA.nE. apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W32; clear; lia | clear - Hle; unfold size in *; lia].
      - apply (CL5.bytes_at_app (hl_segs L)).
        + apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat (o + 1) s (CELL _ Yblob) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
        + intros q Hq. cbn [length] in Hq. assert (q = 0%nat) by (clear - Hq; lia). subst q. cbn [nth]. rewrite Z.add_0_r. fold size.
          pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + 1 + size) (CELL _ Ychr) ltac:(unfold estart; cbn [a_base a_off]; rewrite UON; clear; lia)) as G0.
          apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, EPSA.cE in G0. cbn [edenot] in G0. rewrite W11 in G0. exact G0.
      - replace (o + 1 + (size + 1)) with (o + size + 2) by (clear; lia).
        pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + size + 2) (CELL _ Ynul) ltac:(unfold estart; cbn [a_base a_off]; rewrite UON; clear; lia)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0. }
    split; [exact (DEFO _ _ _ _ _ _ HH1)|]. repeat split; reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact (DEFO _ _ _ _ _ _ HH)).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [apply regs_ok_id|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know F.cp0) in change (CC.cp_know F.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI FT.NF 0 NF32 FT.SCELLS FT.GLO FT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI FT.NF 0 NF32 FT.SCELLS FT.GLO FT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := o) (z := 2 * size); [ev0 | clear - O3; lia | clear - O6; lia | | clear - Hle; unfold size in *; lia |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?U32; clear; lia | clear - Hle; unfold size in *; lia].
      * apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hb0].
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - Hc; lia | clear - Hc; lia].
    + eapply CL5.krange_intro with (v := size); [lin_eval; rw_atoms; clear; lia | unfold size; clear - Hle; lia | unfold size in *; clear - Hle; lia].
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev0 | exact U32 | clear - O3; lia | clear - O6 Hle; unfold size in *; lia | clear - O3 O6; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - O3; lia | clear - O6 Hle; unfold size in *; lia | apply (CL5A.visr_sub _ o 24 (o + 1) (Z.of_nat (length s)) VO ltac:(clear; lia) ltac:(clear - Hle; unfold size in *; lia)) | exact Hbs].
      * apply (L5.defined_sub _ o 24 (o + 1) (Z.of_nat (length s)) DO ltac:(clear; lia) ltac:(clear - Hle; unfold size in *; lia)).
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  - (* [comment removed for export] *)
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 F.BLS []) with (@nil (expr * expr)). cbn [nth EPSA.FFS_F app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity | exact Hroom].
    + exact I.
  - exact Hfp.
Qed.
(* [comment removed for export] *)
Lemma push_back_sso_full_x : forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r : Z) (s : list Z),
  PMSA.cps_asan L ar HI 1056004 r sp PMSA.STR_SCR LB FF LK cr A 0
      (fun R M => Z.of_nat (length s) = 22 /\ PMSA.a0 R o /\ PMSA.a1 R c /\ 0 <= c < 256 /\ PMSA.str_at L M o (PML.SShort s) /\
                  PMSA.fobj M FF o 24 /\ PMSA.stksh ar M sp PMSA.STR_SCR /\ 48 <= onmax /\ acredit_ok L cr 48)
      (fun R M R' M' LB' cr' LBk W => exists p', PMSA.str_at L M' o (PML.SLong 48 p' (s ++ [c])) /\ PMSA.afresh L ar LB FF M' p' 48 /\
                                     LB' = (p', 48) :: LB /\ cr' = adebit L cr 48 /\ LBk = LB /\ W = [(o, 24)]).
Proof.
  intros LB FF LK cr A o c sp r s. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Heq & Ha0 & Ha1 & Hc & Hstr & (Ofr & O8 & Osh) & Hstksh & Hon & Hcred) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh, PMSA.fobj, PMSA.str_at, PMSA.afresh in *. change (256 + (16 + 4096)) with 4368 in *.
  destruct Hstr as (Hl22 & Hb0 & Hbs & Hnul).
  set (size := Z.of_nat (length s)) in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7094272 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.
  (* [comment removed for export] *)
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  (* [comment removed for export] *)
  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun id => nth id [map (Z_to_bv 8) s] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 c) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = c) by (rewrite V11; apply u64_of_Z; clear - Hc; lia).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if Nat.eqb i 0 then cr1 = cr else cr1 = adebit L cr 48).
  set (AFP := fun (nb : Z) => ablock_range L ar nb 48 /\ blocks_apart nb 48 LB /\ fframes_apart nb 48 FF).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
               let nb := CL5A.uv E EPSA.nbE in
               if Nat.eqb i 0 then shadow_zero M1 o 3 else AFP nb /\ L5.defined M1 nb 48 /\ shadow_blk M1 nb 48 /\ ((i <= 1)%nat -> shadow_zero M1 o 3)).
  (* [comment removed for export] *)
  assert (NOFOOT : forall LBown a, Forall (fun bb => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) LBown -> 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL WW LBown [] a).
  { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as G0. cbv beta in G0. clear - Hin Ha G0. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (NOGOTO : forall i c0 kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c0 kk ps (CC.TGoto j sg) -> False).
  { intros i c0 kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ EPSA.leaf_g_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  (* [comment removed for export] *)
  assert (DEN3 : forall E, CH2.den E EPSA.BNEW = [(CL5A.uv E EPSA.nbE, 48)]).
  { intros E. unfold CH2.den, EPSA.BNEW, EPSA.nbE, CL5A.uv. cbn [map fst snd]. repeat f_equal. }
  (* [comment removed for export] *)
  assert (OSH : forall a, in_shadow_of o 24 a -> 2147450880 <= a < 17594333495296 /\ (forall LBx spx scrx, aclient L ar LBx FF spx scrx a) /\ L5.outside WW a).
  { intros a Ha. pose proof (SHR o 24 a O3 ltac:(clear; lia) O6 Ha) as SRa. split; [exact SRa|]. split.
    - intros LBx spx scrx. do 5 right. left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf|].
      unfold in_shadow_of, S in Ha |- *. pose proof (Z.div_le_mono (ff_addr f) o 8 ltac:(clear; lia) ltac:(clear - F1; lia)) as D1.
      pose proof (Z.div_le_mono (o + 24 - 1) (ff_addr f + ff_bytes (ff_class f) - 1) 8 ltac:(clear; lia) ltac:(clear - F2; lia)) as D2. clear - Ha D1 D2. lia.
    - intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SRa O5. lia. }
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 1056004 with (CC.cp_pc G.cp0) by (vm_compute; reflexivity).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact EPSA.heap_g_ok.
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c0 kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - (* [comment removed for export] *)
    intros i c0 kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ EPSA.leaf_g_ok _ _ _ _ _ HIL) as X. unfold EPSA.leaf_chk_g in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    (* [comment removed for export] *)
    assert (PRO : forall i1 : nat, (1 <= i1)%nat -> forall E A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS EPSA.FFS_G Cred 0 i1 E A1 M1 m1 ->
              XI i1 E A1 M1 m1 -> let nb := CL5A.uv E EPSA.nbE in env_agree GT.NF E0 E /\ CHA.curF FF sp EPSA.FFS_G i1 E = FF /\ AFP nb /\ L5.defined M1 nb 48 /\ shadow_blk M1 nb 48 /\ ((i1 <= 1)%nat -> shadow_zero M1 o 3)).
    { intros i1 Hi1 Ex Ax Mx mx HAx HXx. cbv zeta. split; [exact (proj1 (proj2 (proj2 (proj2 HAx))))|]. split; [unfold CHA.curF; rewrite EPSA.FFSG_nil; reflexivity|].
      unfold XI in HXx. destruct (Nat.eqb i1 0) eqn:E1'; [apply Nat.eqb_eq in E1'; exfalso; clear - Hi1 E1'; lia|]. exact HXx. }
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X XK]. apply andb_prop in X as [X YFOOT]. apply andb_prop in X as [YBi YBj]. apply CH2.blocks_eqb_eq in YBi, YBj.
      destruct (Z.eqb_spec pc EPSA.PC_OPNEW) as [->|Hne1].
      { (* [comment removed for export] *)
        cbv zeta in XK. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := EPSA.news_of (nx + 4) cj) in *.
        apply andb_prop in XK as [XK Y10]. apply andb_prop in XK as [XK YNEWS]. apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK YF]. apply andb_prop in XK as [XK YN]. apply andb_prop in XK as [XK Yj].
        apply andb_prop in XK as [Y0 Yi]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj, YN. subst i j.
        lazymatch type of Y5 with EPSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB LB G.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity).
        assert (HcF : CHA.curF FF sp EPSA.FFS_G 0%nat E = FF) by reflexivity.
        refine (CALLEE EPSA.PC_OPNEW 4112 0%nat [] [] news None 0 0%nat c0 ps0 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !EPSA.FFSG_nil, YBi, YBj; cbn [EPSA.BLKS]; exact Hchk | rewrite !EPSA.FFSG_nil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (NXeq : CH2.ci_nx ci = 40%nat) by (destruct HV as (_ & _ & _ & _ & HV5); clear - HV5 YN; unfold nx, APC.NCS in *; lia).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 48 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|].
        split; [split; [exact (REG 10%nat (ELit 48) 48 Y10 eq_refl) | split; [clear - Hon; lia | exact Hcred]]|].
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (clear - NQ5 NQ7 NQ3; lia).
        assert (Hvu : CL5A.uv E2 EPSA.nbE = u).
        { unfold CL5A.uv, EPSA.nbE. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite NXeq in G0 |- *. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        split; [cbn [CH2.den map]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS 1%nat E2 = (u, 48) :: LB) by (unfold CHA.curB; rewrite YBj; cbn [EPSA.BLKS]; rewrite (DEN3 E2), Hvu; reflexivity).
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
        split.
        { unfold XI. cbn [Nat.eqb]. rewrite Hvu. split; [split; [exact Hrng | split; [exact Hbap | exact Hfap]]|]. split; [exact Hdef|]. split; [exact Hsh|]. intros _.
          (* [comment removed for export] *)
          apply (PTA.shadow_zero_ag M1 M2 (in_shadow_of o 24)); [| | unfold XI in HXi; exact HXi].
          - intros a Ha. destruct (OSH a Ha) as (SRa & Kc & Ko). pose proof HP as (HP1 & _ & _).
            rewrite (HP1 a); [|split; [clear - SRa; lia | split; [apply Kc | intros w []]]].
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 WRS_OK
                      0%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite EPSA.FFSG_nil, YBi; exact YFOOT|].
            rewrite EPSA.FFSG_nil, YBi. apply (NOFOOT [] a); [constructor | exact SRa].
          - intros j Hj. exact (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)). }
        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7094272 LYHN GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps0) [] [] 44%nat (ELit 48) M' M2 A1 A2 m' m2 LB ((u, 48) :: LB) FF FF LK1 LK2 cr (adebit L cr 48) u 48 news
                  HagE' Hag2 HK HH1 _ eq_refl Hvu _ _ Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0); [reflexivity | rewrite NXeq; reflexivity | reflexivity | rewrite NXeq; rewrite YN in YNEWS; exact YNEWS]. }
      destruct (Z.eqb_spec pc EPSA.PC_MM) as [->|Hne2]; [|exfalso; clear - XK; discriminate XK].
      { (* [comment removed for export] *)
        apply andb_prop in XK as [XK Yblob]. apply andb_prop in XK as [XK Y12]. apply andb_prop in XK as [XK Y11]. apply andb_prop in XK as [XK Y10].
        apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK Ynx]. apply andb_prop in XK as [XK YF]. apply andb_prop in XK as [XK Yj]. apply andb_prop in XK as [Y0 Yi].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj. apply Nat.leb_le in Ynx. subst i j.
        lazymatch type of Y5 with EPSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (PRO 1%nat ltac:(clear; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF & HSB & HSO). specialize (HSO ltac:(clear; lia)). set (nb := CL5A.uv E EPSA.nbE) in *.
        pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in Q6.
        assert (HcB : CHA.curB LB G.BLS 1%nat E = (nb, 48) :: LB) by (unfold CHA.curB; rewrite YBi; cbn [EPSA.BLKS]; rewrite (DEN3 E); reflexivity).
        refine (CALLEE EPSA.PC_MM 2560 0%nat EPSA.BNEW [(EPSA.nbE, 0, ELit 22)] EPSA.NEWS_MM (Some EPSA.nbE) 0 1%nat c0 ps0 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !EPSA.FFSG_nil, YBi, YBj; cbn [EPSA.BLKS]; exact Hchk | rewrite !EPSA.FFSG_nil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP0 & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 48) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (NB' : CL5A.uv E' EPSA.nbE = nb) by (unfold nb, CL5A.uv, EPSA.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
        assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold CL5A.uv, EPSA.nbE in NB'; cbn [edenot] in NB'; exact NB').
        assert (UO1 : CL5A.uv E' (EAlu Instr.ALU_ADD EPSA.oE (ELit 1)) = o + 1) by (unfold CL5A.uv, EPSA.oE; apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?W10; clear; lia | clear - O3 O6; lia]).
        assert (CELL : forall X0, EPSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS EPSA.FFS_G Cred 0 1%nat E A1 M' m' HA') as Hoff.
        assert (HF2 : Forall (fun bb : Z * Z => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) [(nb, 48)]) by (constructor; [cbn [fst snd]; exact Q6 | constructor]).
        assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 WRS_OK
                    1%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite EPSA.FFSG_nil, YBi; exact YFOOT|].
          rewrite EPSA.FFSG_nil, YBi. cbn [EPSA.BLKS]. rewrite (DEN3 E). exact (NOFOOT _ a HF2 SRa). }
        assert (HSB' : shadow_blk M' nb 48).
        { apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB].
          intros a Ha. exact (FRS nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha). }
        assert (HSO' : shadow_zero M' o 3).
        { apply (PTA.shadow_zero_ag M1 M' (in_shadow_of o 24)); [| | exact HSO].
          - intros a Ha. exact (FRS o 24 a O3 ltac:(clear; lia) O6 Ha).
          - intros j Hj. exact (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)). }
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c0 ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (LENST : length s = 22%nat) by (unfold size in Heq; clear - Heq; lia).
        eexists. eexists. split.
        { exact (EMA.memcpy_cpsX L ar HI PMSA.fp_ok onmax EPSA.PC_MM MEMMOVE_LIBC 2560 ((nb, 48) :: LB) FF LK1 (adebit L cr 48) A1 nb (o + 1) 22 (map (Z_to_bv 8) s) (sp + CH2.ci_csp ci) (CC.cp_pc cj)
                   ltac:(rewrite SCRMEM; clear; lia)). }
        split.
        { unfold EMA.memcpy_preX.
          split; [exact (REG 10%nat _ nb Y10 W44)|]. split; [exact (REG 11%nat _ (o + 1) Y11 UO1)|]. split; [exact (REG 12%nat _ 22 Y12 eq_refl)|].
          split; [exact (EMA.dst_in_blockX L ar C HI HIok onmax _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb 48 nb 22 HH1 (or_introl eq_refl) HSB' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hon; lia))|].
          split.
          - (* [comment removed for export] *)
            split; [exact (EMA.aacc_of_shz M' o 3 (o + 1) 22 HSO' O8 ltac:(clear; lia) ltac:(clear; lia))|].
            split; [clear - O3 O6; lia|].
            split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; unfold hid in O5; clear - O3 O4 O5 CSP S3; lia|].
            split.
            + intros i1 Hi1. right. right. right. right. left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf|]. clear - F1 F2 Hi1. lia.
            + change (Z.to_nat 22) with 22%nat. rewrite <- LENST. apply (L5C.bytes_at_rdn (hl_segs L) M' s (o + 1) ltac:(clear - O3; lia) ltac:(rewrite LENST; clear - O6; lia)).
              apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat (o + 1) s (CELL _ Yblob) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
          - destruct Ofr as (f & Hf & F1 & F2). destruct (Hfap f Hf) as [AP|AP]; [left; clear - AP F1; lia | right; clear - AP F2; lia]. }
        { (* [comment removed for export] *)
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta.
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (NB2 : CL5A.uv E2 EPSA.nbE = nb) by (unfold CL5A.uv, EPSA.nbE; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Ynx; lia); exact W44).
          assert (T44 : bv_unsigned (ev E2 44) = nb) by (unfold CL5A.uv, EPSA.nbE in NB2; cbn [edenot] in NB2; exact NB2).
          split; [unfold EPSA.nbE; cbn [edenot]; rewrite Ha0', <- T44; apply Z_to_bv_bv_unsigned|].
          split; [rewrite (DEN3 E'), NB'; apply incl_refl|].
          split.
          { intros w a [<-|[]] Hin. exists (EPSA.nbE, 0, ELit 22). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. change (bv_unsigned (edenot E' EPSA.nbE)) with (CL5A.uv E' EPSA.nbE). rewrite NB'.
            cbn [edenot]. rewrite (u64_of_Z 22) by (clear; lia). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
            refine (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb 48 a RFx (conj Q5 (conj Q6 Q7)) ltac:(clear; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 _ Hfap (or_introl _) Kc).
            - intros bb Hbb. exact (Hbap bb Hbb).
            - clear - Hin. lia. }
          split; [unfold CHA.curB; rewrite YBj; cbn [EPSA.BLKS]; rewrite (DEN3 E2), NB2; exact HH2|].
          split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
          pose proof HP as (HP1 & HP2 & HP3).
          (* [comment removed for export] *)
          assert (GB2 : forall q, (q < length s)%nat -> M2 (Z_to_bv 64 (nb + Z.of_nat q)) = Some (Z_to_bv 8 (nth q s 0))).
          { intros q Hq. destruct (Hnew (Z.of_nat q) ltac:(clear - Hq LENST; lia)) as (v & (Hnth & Hv) & Hb). rewrite Nat2Z.id, nth_error_map in Hnth.
            destruct (nth_error s q) as [z|] eqn:Ez; [|discriminate Hnth]. cbn [option_map] in Hnth. assert (Hz : Z_to_bv 8 z = Z_to_bv 8 v) by congruence. rewrite (@nth_error_nth _ s q z 0 Ez).
            unfold byte_at in Hb. rewrite Hb, <- Hz. reflexivity. }
          split.
          { unfold XI. cbn [Nat.eqb]. rewrite NB2. split; [exact HAFP|]. split; [|split; [|intros H3; exfalso; clear - H3; lia]].
            - intros q Hq. apply (HP3 (nb + q)); [clear - Hq Q0 Q7; lia | left; exists (nb, 48); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] |].
              apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF q Hq).
            - apply (PTA.shadow_blk_ag M' M2 (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB'].
              intros a Ha. pose proof (SHR nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
              apply HP1. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 48); split; [left; reflexivity | exact Ha]|].
              intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin SRa Q6. lia. }
          (* [comment removed for export] *)
          intros X0 HX0 _. unfold EPSA.NEWS_MM, EPSA.STAT, EPSA.nbE in HX0. cbn [app In] in HX0.
          destruct HX0 as [<-|[<-|[<-|[]]]]; [apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity
                                         | apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity |].
          assert (VNB : CL5A.visr (ahid A2 m2) nb 22).
          { intros q Hq. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (nb + q) HH2); [clear - Hq Q0 Q7; lia | left; exists (nb, 48); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] |].
            intros Hc'. exfalso. pose proof (SHR (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) _ ltac:(clear - CL; lia) ltac:(clear - S2 S3 SP1; lia) ltac:(clear; lia) Hc') as SRa. clear - SRa Q6 Hq. lia. }
          eapply CL5.kblob_intro with (A := nb) (bs := s); [unfold estart; cbn [a_base a_off edenot]; rewrite T44; clear; lia | unfold elenZ; cbn [edenot]; rewrite (u64_of_Z 22) by (clear; lia); rewrite LENST; reflexivity | clear - Q0; lia | rewrite LENST; clear - Q7; lia | clear - Q7; lia
                                                           | rewrite <- (proj2 HagE2); reflexivity | |].
          - apply (CL5A.bytes_vis (hl_segs L)); [clear - Q0; lia | rewrite LENST; clear - Q7; lia | rewrite LENST; exact VNB |].
            intros q Hq. unfold L5.u8_at. cbn [rdn]. rewrite (GB2 q Hq). reflexivity.
          - apply (CL5A.defined_vis _ M2 nb (Z.of_nat (length s))); [rewrite LENST; exact VNB|]. intros q Hq. rewrite <- (Z2Nat.id q) by (clear - Hq; lia). rewrite (GB2 (Z.to_nat q) ltac:(clear - Hq LENST; lia)). discriminate. } }
    + (* [comment removed for export] *)
      apply andb_prop in X as [X Ynul]. apply andb_prop in X as [X Ychr]. apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0].
      apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
      apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      destruct (PRO 2%nat ltac:(clear; lia) E A1 M1 m1 HA HXi) as (HagE & HcF & HAFP & HDF & HSB & _). set (nb := CL5A.uv E EPSA.nbE) in *.
      pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in Q6.
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok EPSA.RETPC 2%nat c0 ps0 _ Xbase _ (EPSA.FFSG_nil 2%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact EPSA.ret_at | rewrite EPSA.FFSG_nil, YB; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = adebit L cr 48) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS 2%nat E = (nb, 48) :: LB) by (unfold CHA.curB; rewrite YB; cbn [EPSA.BLKS]; rewrite (DEN3 E); reflexivity). rewrite HB in HH1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W11 : bv_unsigned (ev E' 11) = c) by (rewrite (FZ 11%nat eq_refl); exact U11).
      assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold nb, CL5A.uv, EPSA.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
      assert (CELL : forall X0, EPSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS EPSA.FFS_G Cred 0 2%nat E A1 M' m' HA') as Hoff.
      rewrite SCRV in HP.
      assert (LENST : length s = 22%nat) by (unfold size in Heq; clear - Heq; lia).
      assert (LEN : Z.of_nat (length (s ++ [c])) = 23) by (rewrite length_app, Nat2Z.inj_add; rewrite LENST; reflexivity).
      apply (Hcont fx' R' M' model2 ((nb, 48) :: LB) (adebit L cr 48) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      exists nb. split.
      { (* [comment removed for export] *) unfold PMLA.str_at, L5.lstr_long. rewrite LEN. split; [|split; [reflexivity | clear; lia]].
        split; [reflexivity|]. split; [|split; [|split; [|split]]].
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0.
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0.
        - apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(unfold estart, EPSA.oE; cbn [a_base a_off edenot]; rewrite W10; clear; lia)) as G0.
          unfold CL5A.uv, EPSA.nbE in G0. cbn [edenot] in G0. rewrite W44 in G0. exact G0.
        - apply (CL5.bytes_at_app (hl_segs L)).
          + apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat nb s (CELL _ Yblob) ltac:(unfold estart, EPSA.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia) _)). rewrite <- (proj2 HagE'). reflexivity.
          + intros q Hq. cbn [length] in Hq. assert (q = 0%nat) by (clear - Hq; lia). subst q. cbn [nth]. rewrite Z.add_0_r, LENST.
            pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (nb + 22) (CELL _ Ychr) ltac:(unfold estart, EPSA.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia)) as G0.
            apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, EPSA.cE in G0. cbn [edenot] in G0. rewrite W11 in G0. exact G0.
        - pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (nb + 23) (CELL _ Ynul) ltac:(unfold estart, EPSA.nbE; cbn [a_base a_off edenot]; rewrite W44; clear; lia)) as G0.
          apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia). exact G0. }
      split; [|split; [reflexivity | split; [reflexivity | split; reflexivity]]].
      unfold PMLA.afresh. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split.
      { intros q Hq. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF q Hq). }
      apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB]. intros a Ha.
      pose proof (SHR nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
      refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS EPSA.FFS_G Cred 0 STKF SCRP NF32 U2 WRS_OK
                2%nat c0 ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite EPSA.FFSG_nil, YB; exact Xfoot|].
      rewrite EPSA.FFSG_nil, YB. cbn [EPSA.BLKS]. rewrite (DEN3 E). apply (NOFOOT _ a); [constructor; [cbn [fst snd]; exact Q6 | constructor] | exact SRa].
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact (DEFO _ _ _ _ _ _ HH)).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (LENST : length s = 22%nat) by (unfold size in Heq; clear - Heq; lia).
    split; [apply regs_ok_id|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := o) (z := 44); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) |].
      replace 44 with (2 * Z.of_nat (length s)) by (rewrite LENST; reflexivity). exact Hb0.
    + eapply CL5.krange_intro with (v := c); [lin_eval; rw_atoms; clear; lia | clear - Hc; lia | clear - Hc; lia].
    + eapply CL5.kblob_intro with (bs := s) (A := o + 1); [ev0 | unfold elenZ; cbn [edenot]; rewrite (u64_of_Z 22) by (clear; lia); rewrite LENST; reflexivity | clear - O3; lia | rewrite LENST; clear - O6; lia | clear - O3 O6; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - O3; lia | rewrite LENST; clear - O6; lia | apply (CL5A.visr_sub _ o 24 (o + 1) (Z.of_nat (length s)) VO ltac:(clear; lia) ltac:(rewrite LENST; clear; lia)) | exact Hbs].
      * apply (L5.defined_sub _ o 24 (o + 1) (Z.of_nat (length s)) DO ltac:(clear; lia) ltac:(rewrite LENST; clear; lia)).
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  - (* [comment removed for export] *)
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with (@nil (expr * expr)). cbn [nth EPSA.FFS_G app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity | exact Hroom].
    + unfold XI. cbn [Nat.eqb]. exact Osh.
  - exact Hfp.
Qed.
End PushBackS.
